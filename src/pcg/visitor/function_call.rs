use super::PcgVisitor;
use crate::{
    action::BorrowPcgAction,
    borrow_pcg::{
        FunctionData,
        abstraction::{
            ArgIdx, ArgIdxOrResult, CallShapeDataSource, FunctionShape, FunctionShapeDataSource,
        },
        borrow_pcg_edge::BorrowPcgEdge,
        domain::{FunctionCallAbstractionInput, FunctionCallAbstractionOutput},
        edge::abstraction::{
            AbstractionBlockEdge, AbstractionEdge,
            function::{
                CallDatatypes, DefinedFnCallShapeDataSource, DefinedFnTarget,
                FunctionCallAbstraction, FunctionCallAbstractionEdgeMetadata, FunctionCallData,
                RustCallDatatypes, UndefinedFnCallShapeDataSource,
            },
        },
        edge_data::LabelNodePredicate,
        region_projection::{HasRegions, HasTy, LifetimeProjection},
    },
    coupling::{CoupledEdgesData, FunctionCallCoupledEdgeKind, PcgCoupledEdgeKind},
    pcg::obtain::{HasSnapshotLocation, expand::PlaceExpander},
    rustc_interface::{
        index::Idx,
        middle::mir::{Location, Operand},
        span::Span,
    },
    utils::{
        PcgSettings,
        data_structures::HashSet,
        display::{DisplayWithCompilerCtxt, DisplayWithCtxt},
    },
};

use super::PcgError;
use crate::{
    rustc_interface::middle::ty::{self},
    utils::{self, DataflowCtxt, HasCompilerCtxt, SnapshotLocation},
};

fn get_function_call_target<'a, 'tcx: 'a>(
    func: &Operand<'tcx>,
    ctxt: impl HasCompilerCtxt<'a, 'tcx>,
) -> Option<DefinedFnTarget<'tcx>> {
    match func.ty(ctxt.body(), ctxt.tcx()).kind() {
        ty::TyKind::FnDef(def_id, substs) => Some(DefinedFnTarget {
            fn_def_id: *def_id,
            substs,
        }),
        _ => None,
    }
}

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    pub(crate) fn settings(&self) -> &'a PcgSettings {
        self.ctxt.settings()
    }

    fn node_for_input<'ops, D: CallDatatypes<'tcx, Inputs = &'ops [&'ops Operand<'tcx>]>>(
        &self,
        call: &FunctionCallData<'tcx, D>,
        // data_source: &impl FunctionShapeDataSource<'tcx, Ctxt>,
        input: LifetimeProjection<'tcx, ArgIdx>,
    ) -> FunctionCallAbstractionInput<'tcx>
    where
        'tcx: 'ops,
    {
        let operand = call.inputs[input.base.index()];
        let operand = self.maybe_labelled_operand(operand);
        FunctionCallAbstractionInput(
            LifetimeProjection::from_index(operand, input.region_idx)
                .with_label(Some(self.prev_snapshot_location().into()), self.ctxt),
        )
    }

    fn node_for_output<
        'ops,
        D: CallDatatypes<'tcx, OutputPlace = utils::Place<'tcx>, Inputs = &'ops [&'ops Operand<'tcx>]>,
    >(
        &self,
        call: &FunctionCallData<'tcx, D>,
        output: LifetimeProjection<'tcx, ArgIdxOrResult>,
    ) -> FunctionCallAbstractionOutput<'tcx>
    where
        'tcx: 'ops,
    {
        match output.base {
            ArgIdxOrResult::Argument(arg_idx) => {
                let operand = call.inputs[*arg_idx];
                let place = self.maybe_labelled_operand(operand).expect_place();
                tracing::warn!("place for output {}: {:?}", output, place);
                LifetimeProjection::from_index(place, output.region_idx)
                    .with_label(
                        Some(SnapshotLocation::After(self.location().block).into()),
                        self.ctxt,
                    )
                    .into()
            }
            ArgIdxOrResult::Result => {
                debug_assert!(
                    call.output_place.regions(self.ctxt.bc_ctxt()).len()
                        > output.region_idx.index(),
                    "Output region index {} is out of bounds for place {:?}:{:?}",
                    output.region_idx.index(),
                    call.output_place,
                    call.output_place.rust_ty(self.ctxt.bc_ctxt())
                );
                LifetimeProjection::from_index(call.output_place, output.region_idx).into()
            }
        }
    }

    fn create_edges_for_call<'ops>(
        &mut self,
        call: FunctionCallData<'tcx, RustCallDatatypes<'ops>>,
    ) -> Result<(), PcgError<'tcx>>
    where
        'tcx: 'ops,
    {
        let metadata = FunctionCallAbstractionEdgeMetadata {
            location: call.location,
            target: call.target,
        };
        let shape = match call.as_defined_fn_call_data() {
            Some(call) => {
                DefinedFnCallShapeDataSource::new(call, self.ctxt.tcx())
                    .unwrap()
                    .shape(self.ctxt)
            }
            None => UndefinedFnCallShapeDataSource { call }.shape(self.ctxt),
        };
        // tracing::warn!(
        //     "shape: {}",
        //     shape.display_string((function_data.unwrap(), self.ctxt.bc_ctxt()))
        // );
        let abstraction_edges: HashSet<
            AbstractionBlockEdge<
                'tcx,
                FunctionCallAbstractionInput<'tcx>,
                FunctionCallAbstractionOutput<'tcx>,
            >,
        > = shape
            .edges()
            .map(|AbstractionBlockEdge { input, output, .. }| {
                // tracing::warn!("input: {:?}, output: {:?}", input, output);
                AbstractionBlockEdge::new_checked(
                    self.node_for_input(&call, input),
                    self.node_for_output(&call, output),
                    self.ctxt.bc_ctxt(),
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
    pub(super) fn make_function_call_abstraction<'args, 'mir>(
        &mut self,
        func: &Operand<'tcx>,
        call_span: Span,
        args: &'args [&'args Operand<'tcx>],
        destination: utils::Place<'tcx>,
        location: Location,
    ) -> Result<(), PcgError<'tcx>> {
        let target = get_function_call_target(func, self.ctxt);
        let caller_data = FunctionCallData {
            target,
            caller_def_id: self.ctxt.def_id(),
            span: call_span,
            inputs: args,
            output_place: destination,
            location,
        };

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
                            rp.display_string(self.ctxt.bc_ctxt()),
                        ),
                    )
                    .into(),
                )?;
            }
        }
        self.create_edges_for_call(caller_data)
    }
}
