use super::PcgVisitor;
use crate::{
    action::BorrowPcgAction,
    borrow_pcg::{
        borrow_pcg_edge::BorrowPcgEdge,
        edge::{
            borrow_flow::{
                AssignmentData, BorrowFlowEdge, BorrowFlowEdgeKind, CastData, OperandType,
            },
            delegation::DelegationEdge,
            kind::BorrowPcgEdgeKind,
        },
        edge_data::LabelNodePredicate,
        region_projection::{ExtractRegionsCtxt, PlaceOrConst},
    },
    pcg::{
        CapabilityKind, EvalStmtPhase, PcgNode, PcgRefLike,
        obtain::{ActionApplier, HasSnapshotLocation, expand::PlaceExpander},
        place_capabilities::PlaceCapabilitiesInterface,
    },
    rustc_interface::middle::mir::{self, CastKind, Operand, Rvalue},
    utils::Place,
};

use crate::utils::{
    AnalysisLocation, DataflowCtxt, SnapshotLocation, maybe_old::MaybeLabelledPlace,
};

use super::{PcgError, PcgUnsupportedError};

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    /// The label that should be used when referencing (after `PostOperands`), the
    /// value at the place before the move.
    pub(crate) fn pre_operand_move_label(&self) -> SnapshotLocation {
        SnapshotLocation::Before(AnalysisLocation::new(
            self.location(),
            EvalStmtPhase::PostOperands,
        ))
    }

    /// The maybe-labelled place to use to reference the value of an operand after
    /// the `PostOperands` phase. If the operand was copied, the place is returned
    /// as-is. If the operand was moved, the place is returned with the label of
    /// the value before the move.
    pub(crate) fn maybe_labelled_operand(
        &self,
        operand: &Operand<'tcx>,
    ) -> PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx>> {
        match operand {
            Operand::Copy(place) => PlaceOrConst::Place((*place).into()),
            Operand::Move(place) => PlaceOrConst::Place(MaybeLabelledPlace::new(
                (*place).into(),
                Some(self.pre_operand_move_label()),
            )),
            Operand::Constant(const_) => PlaceOrConst::Const(const_.const_),
            #[allow(unreachable_patterns)]
            _ => todo!(),
        }
    }

    pub(crate) fn assign_post_main(
        &mut self,
        target: Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> Result<(), PcgError> {
        let ctxt = self.ctxt;

        // If `target` is a reference, then the dereferenced place technically
        // still retains its capabilities. However, because we currently only
        // keep capabilities for non-labelled places, we remove all the capabilities
        // to everything postfix of `target`.
        //
        // We should change this logic once we start keeping capabilities for
        // labelled places.
        if target.is_ref(ctxt) {
            self.pcg
                .place_capabilities
                .remove_all_postfixes(target, ctxt);
        }

        self.pcg
            .place_capabilities
            .insert(target, CapabilityKind::Exclusive, self.ctxt);
        match rvalue {
            Rvalue::Aggregate(
                box (mir::AggregateKind::Adt(..)
                | mir::AggregateKind::Tuple
                | mir::AggregateKind::Array(..)),
                fields,
            ) => {
                let target: Place<'tcx> = (*target).into();
                for (field_idx, field) in fields.iter().enumerate() {
                    let operand_place: Place<'tcx> = if let Some(place) = field.place() {
                        place.into()
                    } else {
                        continue;
                    };
                    for (source_rp_idx, source_proj) in operand_place
                        .lifetime_projections(self.ctxt)
                        .iter()
                        .enumerate()
                    {
                        let maybe_labelled = self.maybe_labelled_operand(field);
                        let source_proj = source_proj.with_base(maybe_labelled);
                        self.connect_outliving_projections(source_proj, target, |_| {
                            BorrowFlowEdgeKind::Aggregate {
                                field_idx,
                                target_rp_index: source_rp_idx,
                            }
                        })?;
                    }
                }
            }
            Rvalue::Use(operand) => {
                let p = operand.place();
                if let Some(p) = p {
                    let p: Place = p.into();
                    if p.ty(self.ctxt).ty.is_raw_ptr() {
                        let p = p.with_inherent_region(self.ctxt).project_deref(self.ctxt);
                        let node = PcgNode::from(p);
                        let edges = self
                            .pcg
                            .borrows_graph()
                            .edges_blocked_by(node, self.ctxt.bc_ctxt());
                        let alias_edges = edges
                            .into_iter()
                            .filter_map(|e| match e.kind {
                                BorrowPcgEdgeKind::Delegation(de) => Some(de),
                                _ => None,
                            })
                            .collect::<Vec<_>>();
                        if !alias_edges.is_empty() {
                            self.record_and_apply_action(
                                BorrowPcgAction::add_edge(
                                    BorrowPcgEdge::new(
                                        DelegationEdge {
                                            rawptr_place: target.project_deref(ctxt).into(),
                                            aliased_place: alias_edges[0].aliased_place,
                                        }
                                        .into(),
                                        self.pcg.borrow.validity_conditions.clone(),
                                    ),
                                    "assign_post_main",
                                )
                                .into(),
                            )?;
                            return Ok(());
                        }
                    }
                }
                self.assignment_projections(operand, target, None)?;
            }
            Rvalue::Cast(kind, operand, ty) => {
                if let CastKind::PtrToPtr = kind {
                    let p = operand.place().unwrap();
                    let p: Place = p.into();
                    let p = p.with_inherent_region(self.ctxt).project_deref(self.ctxt);
                    let edges = self.pcg.borrows_graph().edges_blocked_by(p.into(), ctxt);
                    let alies_edges = edges
                        .into_iter()
                        .filter_map(|e| match e.kind {
                            BorrowPcgEdgeKind::Delegation(de) => Some(de),
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    if !alies_edges.is_empty() {
                        assert!(alies_edges.len() == 1);
                        self.record_and_apply_action(
                            BorrowPcgAction::add_edge(
                                BorrowPcgEdge::new(
                                    DelegationEdge {
                                        rawptr_place: target.project_deref(ctxt).into(),
                                        aliased_place: alies_edges[0].aliased_place,
                                    }
                                    .into(),
                                    self.pcg.borrow.validity_conditions.clone(),
                                ),
                                "assign_post_main",
                            )
                            .into(),
                        )?;
                    }
                } else {
                    self.assignment_projections(operand, target, Some(CastData::new(*kind, *ty)))?;
                }
            }
            Rvalue::Ref(borrow_region, kind, blocked_place) => {
                let blocked_place: Place<'tcx> = (*blocked_place).into();
                let blocked_place = blocked_place.with_inherent_region(self.ctxt);
                if !target.ty(self.ctxt).ty.is_ref() {
                    return Err(PcgError::unsupported(
                        PcgUnsupportedError::AssignBorrowToNonReferenceType,
                    ));
                }
                if matches!(kind, mir::BorrowKind::Fake(_)) {
                    return Ok(());
                }
                self.pcg.borrow.add_borrow(
                    blocked_place,
                    target,
                    *kind,
                    self.location(),
                    *borrow_region,
                    &mut self.pcg.place_capabilities,
                    self.ctxt,
                );
                self.label_lifetime_projections_for_borrow(blocked_place, target, *kind)?;
            }
            Rvalue::RawPtr(kind, p) => {
                if !kind.is_fake() {
                    let p: Place<'tcx> = (*p).into();
                    let p = p.with_inherent_region(self.ctxt);
                    self.record_and_apply_action(
                        BorrowPcgAction::add_edge(
                            BorrowPcgEdge::new(
                                DelegationEdge {
                                    rawptr_place: target.project_deref(ctxt).into(),
                                    aliased_place: p.into(),
                                }
                                .into(),
                                self.pcg.borrow.validity_conditions.clone(),
                            ),
                            "assign_post_main",
                        )
                        .into(),
                    )?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn assignment_projections(
        &mut self,
        operand: &Operand<'tcx>,
        target_place: Place<'tcx>,
        cast_data: Option<CastData<'tcx>>,
    ) -> Result<(), PcgError> {
        let (source_projections, operand_type) = match operand {
            Operand::Move(place) | Operand::Copy(place) => {
                let operand_type = if matches!(operand, Operand::Move(_)) {
                    OperandType::Move
                } else {
                    OperandType::Copy
                };
                let place_label = matches!(operand_type, OperandType::Move)
                    .then(|| self.pre_operand_move_label());
                let place: Place<'tcx> = (*place).into();
                let place = place.with_inherent_region(self.ctxt);
                (
                    self.ctxt.extract_lifetime_projections(PlaceOrConst::Place(
                        MaybeLabelledPlace::new(place, place_label),
                    )),
                    operand_type,
                )
            }
            Operand::Constant(const_) => (
                self.ctxt
                    .extract_lifetime_projections(PlaceOrConst::Const(const_.const_)),
                OperandType::Const,
            ),
            #[allow(unreachable_patterns)]
            _ => return Ok(()),
        };
        for source_proj in source_projections {
            self.connect_outliving_projections(source_proj, target_place, |_| {
                BorrowFlowEdgeKind::Assignment(AssignmentData::new(operand_type, cast_data))
            })?;
        }
        Ok(())
    }

    fn label_lifetime_projections_for_borrow(
        &mut self,
        blocked_place: Place<'tcx>,
        target: Place<'tcx>,
        kind: mir::BorrowKind,
    ) -> Result<(), PcgError> {
        let ctxt = self.ctxt;
        for source_proj in blocked_place.lifetime_projections(self.ctxt) {
            let mut obtainer = self.place_obtainer();
            let source_proj = if kind.mutability().is_mut() {
                let label = obtainer.prev_snapshot_location();
                obtainer.apply_action(
                    BorrowPcgAction::label_lifetime_projection(
                        LabelNodePredicate::postfix_lifetime_projection(source_proj.into()),
                        Some(label.into()),
                        "Label region projections of newly borrowed place",
                    )
                    .into(),
                )?;
                source_proj.with_label(Some(label.into()), self.ctxt)
            } else {
                source_proj.with_label(
                    obtainer
                        .label_for_shared_expansion_of_rp(source_proj, obtainer.ctxt)
                        .map(Into::into),
                    self.ctxt,
                )
            };
            let source_region = source_proj.region(self.ctxt.ctxt());
            let mut nested_ref_mut_targets = vec![];
            for target_proj in target.lifetime_projections(self.ctxt) {
                let target_region = target_proj.region(self.ctxt.ctxt());
                if self
                    .ctxt
                    .bc()
                    .outlives(source_region, target_region, self.location())
                {
                    let regions_equal =
                        self.ctxt
                            .bc()
                            .same_region(source_region, target_region, self.location());
                    self.record_and_apply_action(
                        BorrowPcgAction::add_edge(
                            BorrowPcgEdge::new(
                                BorrowFlowEdge::new(
                                    source_proj.into(),
                                    target_proj.into(),
                                    BorrowFlowEdgeKind::BorrowOutlives { regions_equal },
                                )
                                .into(),
                                self.pcg.borrow.validity_conditions.clone(),
                            ),
                            "assign_post_main",
                        )
                        .into(),
                    )?;
                    if regions_equal && kind.mutability().is_mut() {
                        nested_ref_mut_targets.push(target_proj.into());
                    }
                }
            }
            self.place_obtainer().add_and_update_placeholder_edges(
                source_proj.into(),
                &nested_ref_mut_targets,
                "assign",
                ctxt,
            )?;
        }
        Ok(())
    }
}
