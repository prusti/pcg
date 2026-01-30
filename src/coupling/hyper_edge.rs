use std::borrow::Cow;

use crate::{
    borrow_pcg::{
        edge::kind::BorrowPcgEdgeType,
        edge_data::{
            LabelEdgePlaces, LabelNodePredicate, NodeReplacement, conditionally_label_places,
        },
        has_pcs_elem::{LabelNodeContext, LabelPlace, PlaceLabeller, SourceOrTarget},
    },
    pcg::PcgNodeLike,
    pcg_validity_assert,
    utils::{
        DebugCtxt, PcgPlace,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
    },
};

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct HyperEdge<InputNode, OutputNode> {
    pub(crate) inputs: Vec<InputNode>,
    pub(crate) outputs: Vec<OutputNode>,
}

impl<Ctxt: Copy, InputNode: DisplayWithCtxt<Ctxt>, OutputNode: DisplayWithCtxt<Ctxt>>
    DisplayWithCtxt<Ctxt> for HyperEdge<InputNode, OutputNode>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Seq(vec![
            DisplayOutput::Text(Cow::Borrowed("HyperEdge(inputs: ")),
            self.inputs.display_output(ctxt, mode),
            DisplayOutput::Text(Cow::Borrowed(", outputs: ")),
            self.outputs.display_output(ctxt, mode),
            DisplayOutput::Text(Cow::Borrowed(")")),
        ])
    }
}

impl<InputNode, OutputNode> HyperEdge<InputNode, OutputNode> {
    pub(crate) fn new(inputs: Vec<InputNode>, outputs: Vec<OutputNode>) -> Self {
        pcg_validity_assert!(!inputs.is_empty(), "HyperEdge must have at least one input");
        pcg_validity_assert!(
            !outputs.is_empty(),
            "HyperEdge must have at least one output"
        );
        Self { inputs, outputs }
    }

    pub fn inputs(&self) -> &Vec<InputNode> {
        &self.inputs
    }

    pub fn outputs(&self) -> &Vec<OutputNode> {
        &self.outputs
    }

    pub fn map_into<T>(self, f: impl FnOnce(Vec<InputNode>, Vec<OutputNode>) -> T) -> T {
        f(self.inputs, self.outputs)
    }

    pub fn into_tuple(self) -> (Vec<InputNode>, Vec<OutputNode>) {
        (self.inputs, self.outputs)
    }

    #[allow(unused)]
    pub(crate) fn map_inputs<T>(self, f: impl FnMut(InputNode) -> T) -> HyperEdge<T, OutputNode> {
        HyperEdge::new(self.inputs.into_iter().map(f).collect(), self.outputs)
    }

    #[allow(unused)]
    pub(crate) fn map_outputs<T>(self, f: impl FnMut(OutputNode) -> T) -> HyperEdge<InputNode, T> {
        HyperEdge::new(self.inputs, self.outputs.into_iter().map(f).collect())
    }

    pub(crate) fn try_to_singleton_edge(&self) -> Option<(&InputNode, &OutputNode)> {
        if self.inputs.len() == 1 && self.outputs.len() == 1 {
            Some((&self.inputs[0], &self.outputs[0]))
        } else {
            None
        }
    }
}

impl<
    'tcx,
    Ctxt: Copy + DebugCtxt,
    P: PcgPlace<'tcx, Ctxt>,
    Input: LabelPlace<'tcx, Ctxt, P> + PcgNodeLike<'tcx, Ctxt, P>,
    Output: LabelPlace<'tcx, Ctxt, P> + PcgNodeLike<'tcx, Ctxt, P>,
> LabelEdgePlaces<'tcx, Ctxt, P> for HyperEdge<Input, Output>
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        conditionally_label_places(
            self.inputs.iter_mut(),
            predicate,
            labeller,
            LabelNodeContext::new(SourceOrTarget::Source, BorrowPcgEdgeType::Coupled),
            ctxt,
        )
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        conditionally_label_places(
            self.outputs.iter_mut(),
            predicate,
            labeller,
            LabelNodeContext::new(SourceOrTarget::Target, BorrowPcgEdgeType::Coupled),
            ctxt,
        )
    }
}
