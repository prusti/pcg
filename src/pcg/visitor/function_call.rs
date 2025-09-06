use super::PcgVisitor;
use crate::action::BorrowPcgAction;
use crate::borrow_pcg::abstraction::{ArgIdx, ArgIdxOrResult, FunctionCall, FunctionShape};
use crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdge;
use crate::borrow_pcg::domain::{FunctionCallAbstractionInput, FunctionCallAbstractionOutput};
use crate::borrow_pcg::edge::abstraction::function::{
    FunctionCallAbstraction, FunctionCallData, FunctionData,
};
use crate::borrow_pcg::edge::abstraction::{AbstractionBlockEdge, AbstractionType};
use crate::borrow_pcg::has_pcs_elem::LabelLifetimeProjectionPredicate;
use crate::borrow_pcg::region_projection::LifetimeProjection;
use crate::pcg::obtain::{HasSnapshotLocation, PlaceExpander};
use crate::pcg_validity_assert;
use crate::rustc_interface::infer::infer::TyCtxtInferExt;
use crate::rustc_interface::infer::traits::ObligationCause;
use crate::rustc_interface::middle::mir::{Location, Operand};
use crate::rustc_interface::span::Span;
use crate::rustc_interface::trait_selection::traits::query::normalize::QueryNormalizeExt;
use crate::utils::display::DisplayWithCompilerCtxt;

use super::PcgError;
use crate::rustc_interface::middle::ty::{self};
use crate::utils::{self, DataflowCtxt, HasCompilerCtxt, SnapshotLocation};

fn get_function_call_data<'a, 'tcx: 'a>(
    func: &Operand<'tcx>,
    operand_tys: Vec<ty::Ty<'tcx>>,
    call_span: Span,
    ctxt: impl HasCompilerCtxt<'a, 'tcx>,
) -> Option<FunctionCallData<'tcx>> {
    match func.ty(ctxt.body(), ctxt.tcx()).kind() {
        ty::TyKind::FnDef(def_id, substs) => Some(FunctionCallData::new(
            *def_id,
            substs,
            operand_tys,
            call_span,
        )),
        ty::TyKind::FnPtr(..) => None,
        _ => None,
    }
}

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    fn node_for_input(
        &self,
        call: &FunctionCall<'_, 'tcx>,
        input: LifetimeProjection<'tcx, ArgIdx>,
    ) -> FunctionCallAbstractionInput<'tcx> {
        let operand = call.inputs[*input.base];
        let place = self.maybe_labelled_operand_place(&operand).unwrap();
        LifetimeProjection::from_index(place, input.region_idx)
            .with_label(Some(self.prev_snapshot_location().into()), self.ctxt)
            .into()
    }

    fn node_for_output(
        &self,
        call: &FunctionCall<'_, 'tcx>,
        output: LifetimeProjection<'tcx, ArgIdxOrResult>,
    ) -> FunctionCallAbstractionOutput<'tcx> {
        match output.base {
            ArgIdxOrResult::Argument(arg_idx) => {
                let operand = call.inputs[*arg_idx];
                let place = self.maybe_labelled_operand_place(&operand).unwrap();
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
        shape: FunctionShape<'tcx>,
        call: &FunctionCall<'_, 'tcx>,
        function_data: Option<FunctionData<'tcx>>,
    ) -> Result<(), PcgError> {
        for (input, output) in shape.iter().copied() {
            self.record_and_apply_action(
                BorrowPcgAction::add_edge(
                    BorrowPcgEdge::new(
                        AbstractionType::FunctionCall(
                            FunctionCallAbstraction::new(
                                call.location,
                                function_data,
                                AbstractionBlockEdge::new(
                                    self.node_for_input(call, input),
                                    self.node_for_output(call, output),
                                    self.ctxt,
                                ),
                            )
                            .into(),
                        )
                        .into(),
                        self.pcg.borrow.validity_conditions.clone(),
                    ),
                    "Function call",
                    self.ctxt,
                )
                .into(),
            )?;
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
    ) -> Result<(), PcgError> {
        let function_call_data = get_function_call_data(
            func,
            args.iter()
                .map(|arg| arg.ty(self.ctxt.body(), self.ctxt.tcx()))
                .collect(),
            call_span,
            self.ctxt,
        );

        let call = FunctionCall::new(location, args, destination);

        let ctxt = self.ctxt;

        // The versions of the region projections for the function inputs just
        // before they were moved out, labelled with their last modification
        // time
        let arg_region_projections = args
            .iter()
            .filter_map(|arg| self.maybe_labelled_operand_place(arg))
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
            self.place_obtainer()
                .redirect_source_of_future_edges(*rp, *post_rp, ctxt)?;
        }

        for (rp, pre_rp) in arg_region_projections.iter().zip(pre_rps.iter()) {
            self.record_and_apply_action(
                BorrowPcgAction::label_lifetime_projection(
                    LabelLifetimeProjectionPredicate::Equals(*rp),
                    pre_rp.label(),
                    format!(
                        "Function call:Label Pre version of {}",
                        rp.to_short_string(self.ctxt.bc_ctxt()),
                    ),
                )
                .into(),
            )?;
        }
        let call_shape = FunctionShape::new(&call, self.ctxt.bc_ctxt());
        let function_data = function_call_data.as_ref().map(|f| f.function_data);
        let shape = if let Some(function_call_data) = function_call_data.as_ref() {
            let sig_shape = function_call_data.shape(self.ctxt.bc_ctxt());
            // pcg_validity_assert!(
            //     sig_shape == call_shape,
            //     "Signature shape {} for function {:?} with signature {:#?}\nInstantiated:{:#?}\nFully Resolved:{:#?}\nCall shape {}",
            //     sig_shape.to_short_string(self.ctxt.bc_ctxt()),
            //     function_call_data.def_id(),
            //     ctxt.tcx().fn_sig(function_call_data.def_id()),
            //     function_call_data.instantiated_sig(self.ctxt.bc_ctxt()),
            //     function_call_data.fully_normalized_sig(self.ctxt.bc_ctxt()),
            //     call_shape.to_short_string(self.ctxt.bc_ctxt())
            // );
            sig_shape
        } else {
            call_shape
        };
        self.create_edges_for_shape(shape, &call, function_data)?;

        Ok(())
    }
}
