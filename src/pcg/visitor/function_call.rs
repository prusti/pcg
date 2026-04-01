use super::PcgVisitor;
use crate::{
    action::BorrowPcgAction,
    borrow_pcg::{
        FunctionData,
        abstraction::{ArgIdx, ArgIdxOrResult, FunctionCall, FunctionShape},
        borrow_pcg_edge::BorrowPcgEdge,
        domain::{FunctionCallAbstractionInput, FunctionCallAbstractionOutput},
        edge::abstraction::{
            AbstractionBlockEdge, AbstractionEdge,
            function::{
                DefinedFnCall, FunctionCallAbstraction, FunctionCallAbstractionEdgeMetadata,
            },
        },
        edge_data::LabelNodePredicate,
        region_projection::{HasRegions, LifetimeProjection},
    },
    coupling::{CoupledEdgesData, FunctionCallCoupledEdgeKind, PcgCoupledEdgeKind},
    pcg::obtain::{HasSnapshotLocation, expand::PlaceExpander},
    rustc_interface::{
        middle::mir::{Location, Operand},
        span::Span,
    },
    utils::{PcgSettings, data_structures::HashSet, display::DisplayWithCompilerCtxt},
};

use super::PcgError;
use crate::{
    rustc_interface::middle::ty::{self},
    utils::{self, DataflowCtxt, SnapshotLocation},
};

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    pub(crate) fn settings(&self) -> &'a PcgSettings {
        self.ctxt.settings()
    }

    fn node_for_input(
        &self,
        call: &FunctionCall<'_, 'tcx>,
        input: LifetimeProjection<'tcx, ArgIdx>,
    ) -> FunctionCallAbstractionInput<'tcx> {
        let operand = call.inputs[*input.base];
        let operand = self.maybe_labelled_operand(operand);
        FunctionCallAbstractionInput(
            LifetimeProjection::from_index(operand, input.region_idx)
                .with_label(Some(self.prev_snapshot_location().into()), self.ctxt),
        )
    }

    fn node_for_output(
        &self,
        call: &FunctionCall<'_, 'tcx>,
        output: LifetimeProjection<'tcx, ArgIdxOrResult>,
    ) -> FunctionCallAbstractionOutput<'tcx> {
        match output.base {
            ArgIdxOrResult::Argument(arg_idx) => {
                let operand = call.inputs[*arg_idx];
                let place = self.maybe_labelled_operand(operand).expect_place();
                LifetimeProjection::from_index(place, output.region_idx)
                    .with_label(
                        Some(SnapshotLocation::After(self.location().block).into()),
                        self.ctxt,
                    )
                    .into()
            }
            ArgIdxOrResult::Result => {
                LifetimeProjection::from_index(call.output, output.region_idx).into()
            }
        }
    }

    fn create_edges_for_shape(
        &mut self,
        shape: &FunctionShape,
        call: &FunctionCall<'_, 'tcx>,
    ) -> Result<(), PcgError<'tcx>> {
        let metadata = FunctionCallAbstractionEdgeMetadata {
            location: call.location,
            defined_fn_call: call.defined,
        };
        let abstraction_edges: HashSet<AbstractionBlockEdge<'_, _, _>> = shape
            .edges()
            .map(|AbstractionBlockEdge { input, output, .. }| {
                AbstractionBlockEdge::new_checked(
                    self.node_for_input(call, input),
                    self.node_for_output(call, output),
                    self.ctxt,
                )
            })
            .collect();
        if self.settings().coupling {
            let coupled_edges = CoupledEdgesData::new(abstraction_edges.iter().copied());
            if !coupled_edges.is_empty() {
                tracing::debug!("Coupled edges: {:?}", coupled_edges);
            }
            for edge in coupled_edges {
                let pcg_coupled_edge = PcgCoupledEdgeKind::function_call(
                    FunctionCallCoupledEdgeKind::new(metadata, edge),
                );
                self.record_and_apply_action(
                    BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(
                            pcg_coupled_edge.into(),
                            self.pcg.borrow.validity_conditions.clone(),
                        ),
                        "Function call",
                    )
                    .into(),
                )?;
            }
        } else {
            for edge in abstraction_edges {
                self.record_and_apply_action(
                    BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(
                            AbstractionEdge::FunctionCall(FunctionCallAbstraction::new(
                                metadata, edge,
                            ))
                            .into(),
                            self.pcg.borrow.validity_conditions.clone(),
                        ),
                        "Function call",
                    )
                    .into(),
                )?;
            }
        }
        Ok(())
    }
    #[tracing::instrument(skip(self, func, args, destination))]
    pub(super) fn make_function_call_abstraction(
        &mut self,
        func: &Operand<'tcx>,
        call_span: Span,
        args: &[&Operand<'tcx>],
        destination: utils::Place<'tcx>,
        location: Location,
    ) -> Result<(), PcgError<'tcx>> {
        let call = FunctionCall::new(
            location,
            args,
            destination,
            match func.ty(self.ctxt.body(), self.ctxt.tcx()).kind() {
                ty::TyKind::FnDef(def_id, substs) => Some(DefinedFnCall::new(
                    FunctionData::new(*def_id),
                    substs,
                    self.ctxt.ctxt().def_id(),
                    call_span,
                )),
                _ => None,
            },
        );

        let ctxt = self.ctxt;

        // The versions of the region projections for the function inputs just
        // before they were moved out, labelled with their last modification
        // time
        let arg_region_projections = args
            .iter()
            .map(|arg| self.maybe_labelled_operand(arg))
            .flat_map(|input_place| input_place.lifetime_projections(self.ctxt))
            .collect::<Vec<_>>();

        let pre_rps = arg_region_projections
            .iter()
            .map(|rp| {
                rp.with_label(
                    Some(self.place_obtainer().prev_snapshot_location().into()),
                    self.ctxt,
                )
            })
            .collect::<Vec<_>>();

        let post_rps = arg_region_projections
            .iter()
            .map(|rp| {
                rp.with_label(
                    Some(SnapshotLocation::After(self.location().block).into()),
                    self.ctxt,
                )
            })
            .collect::<Vec<_>>();

        for (rp, post_rp) in arg_region_projections.iter().zip(post_rps.iter()) {
            if let (Some(rp), Some(post_rp)) = (
                rp.try_to_local_lifetime_projection(),
                post_rp.try_to_local_lifetime_projection(),
            ) {
                self.place_obtainer()
                    .redirect_source_of_future_edges(rp, post_rp, ctxt)?;
            }
        }

        for (rp, pre_rp) in arg_region_projections.iter().zip(pre_rps.iter()) {
            if let Some(rp) = rp.try_to_local_lifetime_projection() {
                self.record_and_apply_action(
                    BorrowPcgAction::label_lifetime_projection(
                        LabelNodePredicate::equals_lifetime_projection(rp),
                        pre_rp.label(),
                        format!(
                            "Function call:Label Pre version of {}",
                            rp.display_string(self.ctxt),
                        ),
                    )
                    .into(),
                )?;
            }
        }
        let shape = call.shape(self.ctxt);
        self.create_edges_for_shape(&shape, &call)?;

        Ok(())
    }
}
