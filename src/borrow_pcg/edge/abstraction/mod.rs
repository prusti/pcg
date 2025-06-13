pub(crate) mod function;
pub(crate) mod r#loop;
pub(crate) mod r#type;

use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        borrow_pcg_edge::BlockedNode,
        domain::{AbstractionInputTarget, FunctionCallAbstractionInput},
        edge::abstraction::{function::FunctionCallAbstraction, r#loop::LoopAbstraction},
        edge_data::{LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{LabelPlace, LabelRegionProjection},
        latest::Latest,
        region_projection::{MaybeRemoteRegionProjectionBase, RegionProjectionLabel},
    },
    edgedata_enum,
    pcg::PCGNodeLike,
    utils::{maybe_remote::MaybeRemotePlace, redirect::MaybeRedirected},
};

use crate::borrow_pcg::borrow_pcg_edge::LocalNode;
use crate::borrow_pcg::domain::{AbstractionOutputTarget, LoopAbstractionInput};
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::has_pcs_elem::HasPcgElems;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::pcg::{LocalNodeLike, PCGNode};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::validity::HasValidityCheck;
use crate::utils::CompilerCtxt;
use itertools::Itertools;

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum AbstractionType<'tcx> {
    FunctionCall(FunctionCallAbstraction<'tcx>),
    Loop(LoopAbstraction<'tcx>),
}

edgedata_enum!(
    AbstractionType<'tcx>,
    FunctionCall(FunctionCallAbstraction<'tcx>),
    Loop(LoopAbstraction<'tcx>),
);

impl<'tcx> AbstractionType<'tcx> {
    pub(crate) fn redirect(
        &mut self,
        from: AbstractionOutputTarget<'tcx>,
        to: AbstractionOutputTarget<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        match self {
            AbstractionType::FunctionCall(c) => c.redirect(from, to, ctxt),
            AbstractionType::Loop(c) => c.redirect(from, to, ctxt),
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct AbstractionBlockEdge<'tcx, Input> {
    inputs: Vec<Input>,
    pub(crate) outputs: Vec<MaybeRedirected<AbstractionOutputTarget<'tcx>>>,
}

impl<'tcx, T: LabelPlace<'tcx>> LabelEdgePlaces<'tcx> for AbstractionBlockEdge<'tcx, T> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        latest: &Latest<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        for input in &mut self.inputs {
            changed |= input.label_place(predicate, latest, ctxt);
        }
        changed
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        latest: &Latest<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        for output in &mut self.outputs {
            changed |= output.label_place(predicate, latest, ctxt);
        }
        changed
    }
}

impl<
        'tcx: 'a,
        'a,
        Input: PCGNodeLike<'tcx> + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    > AbstractionBlockEdge<'tcx, Input>
{
    pub(crate) fn redirect(
        &mut self,
        from: AbstractionOutputTarget<'tcx>,
        to: AbstractionOutputTarget<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        for output in self.outputs.iter_mut() {
            if output.effective() == from {
                let output_node = output.effective().to_pcg_node(ctxt);
                if self
                    .inputs
                    .iter()
                    .any(|i| i.to_pcg_node(ctxt) == output_node)
                {
                    self.outputs = self
                        .outputs
                        .iter()
                        .filter(|o| o.effective() != from)
                        .cloned()
                        .collect();
                    return;
                } else {
                    output.redirect(from, to);
                }
            }
        }
        self.assert_validity(ctxt);
    }
}

impl<
        'tcx: 'a,
        'a,
        Input: LabelRegionProjection<'tcx>
            + PCGNodeLike<'tcx>
            + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    > LabelRegionProjection<'tcx> for AbstractionBlockEdge<'tcx, Input>
{
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        let mut i = 0;
        while i < self.inputs.len() {
            let input = &mut self.inputs[i];
            changed |= input.label_region_projection(projection, label, ctxt);
            let input = self.inputs[i];
            if self
                .outputs
                .iter()
                .any(|o| o.effective().to_pcg_node(ctxt) == input.to_pcg_node(ctxt))
            {
                self.inputs
                    .retain(|i| i.to_pcg_node(ctxt) != input.to_pcg_node(ctxt));
                self.assert_validity(ctxt);
                return true;
            }
            i += 1;
        }
        let mut j = 0;
        while j < self.outputs.len() {
            let output = &mut self.outputs[j];
            changed |= output.label_region_projection(projection, label, ctxt);
            let output = self.outputs[j].effective();
            if self
                .inputs
                .iter()
                .any(|i| i.to_pcg_node(ctxt) == output.to_pcg_node(ctxt))
            {
                self.outputs
                    .retain(|o| o.effective().to_pcg_node(ctxt) != output.to_pcg_node(ctxt));
                self.assert_validity(ctxt);
                return true;
            }
            j += 1;
        }
        self.assert_validity(ctxt);
        changed
    }
}

trait AbstractionInputLike<'tcx>: Sized + Clone {
    fn inputs_block<C: Copy>(
        inputs: &[Self],
        node: BlockedNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool;

    fn to_abstraction_input(self) -> AbstractionInputTarget<'tcx>;
}

impl<'tcx> AbstractionInputLike<'tcx> for LoopAbstractionInput<'tcx> {
    fn inputs_block<C: Copy>(
        inputs: &[Self],
        node: BlockedNode<'tcx>,
        _ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        match node {
            PCGNode::Place(p) => inputs.contains(&p.into()),
            PCGNode::RegionProjection(region_projection) => match region_projection.base {
                MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                    inputs.contains(&region_projection.with_base(maybe_remote_place).into())
                }
                MaybeRemoteRegionProjectionBase::Const(_) => false,
            },
        }
    }

    fn to_abstraction_input(self) -> AbstractionInputTarget<'tcx> {
        self
    }
}

impl<'tcx> AbstractionInputLike<'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn inputs_block<C: Copy>(
        inputs: &[Self],
        node: BlockedNode<'tcx>,
        _ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        match node {
            PCGNode::Place(_) => false,
            PCGNode::RegionProjection(region_projection) => match region_projection.base {
                MaybeRemoteRegionProjectionBase::Place(MaybeRemotePlace::Local(rp)) => {
                    inputs.contains(&region_projection.with_base(rp))
                }
                _ => false,
            },
        }
    }

    fn to_abstraction_input(self) -> AbstractionInputTarget<'tcx> {
        self.into()
    }
}

impl<'tcx, Input: AbstractionInputLike<'tcx>> EdgeData<'tcx> for AbstractionBlockEdge<'tcx, Input> {
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        Input::inputs_block(&self.inputs, node, ctxt)
    }

    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        _ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PCGNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(
            self.inputs()
                .into_iter()
                .map(|i| i.to_abstraction_input().into()),
        )
    }

    fn blocked_by_nodes<'slf, 'mir, BC: Copy + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir,
        'mir: 'slf,
    {
        Box::new(
            self.outputs()
                .into_iter()
                .map(move |o| o.to_local_node(ctxt)),
        )
    }
}

impl<'tcx, 'a, Input: DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>>
    DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for AbstractionBlockEdge<'tcx, Input>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        format!(
            "[{}] -> [{}]",
            self.inputs
                .iter()
                .map(|i| i.to_short_string(ctxt))
                .join(", "),
            self.outputs
                .iter()
                .map(|o| o.to_short_string(ctxt))
                .join(", ")
        )
    }
}

impl<
        'tcx: 'a,
        'a,
        Input: HasValidityCheck<'tcx>
            + PCGNodeLike<'tcx>
            + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    > HasValidityCheck<'tcx> for AbstractionBlockEdge<'tcx, Input>
{
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        for input in self.inputs.iter() {
            input.check_validity(ctxt)?;
        }
        for output in self.outputs.iter() {
            output.check_validity(ctxt)?;
        }
        for input in self.inputs.iter() {
            for output in self.outputs.iter() {
                if input.to_pcg_node(ctxt) == output.effective().to_pcg_node(ctxt) {
                    return Err(format!(
                        "Input {:?} and output {:?} are the same node",
                        input,
                        output,
                    ));
                }
            }
        }
        Ok(())
    }
}

impl<
        'tcx: 'a,
        'a,
        Input: Clone
            + PCGNodeLike<'tcx>
            + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    > AbstractionBlockEdge<'tcx, Input>
{
    pub(crate) fn new(
        inputs: Vec<Input>,
        outputs: Vec<AbstractionOutputTarget<'tcx>>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        assert!(!inputs.is_empty());
        assert!(!outputs.is_empty());
        let result = Self {
            inputs: inputs.into_iter().collect(),
            outputs: outputs.into_iter().map(|o| o.into()).collect(),
        };
        result.assert_validity(ctxt);
        result
    }
}

impl<'tcx, Input: Clone> AbstractionBlockEdge<'tcx, Input> {
    pub fn outputs(&self) -> Vec<AbstractionOutputTarget<'tcx>> {
        self.outputs.iter().map(|o| o.effective()).collect()
    }

    pub fn inputs(&self) -> Vec<Input> {
        self.inputs.to_vec()
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for LoopAbstractionInput<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            LoopAbstractionInput::Place(p) => p.pcg_elems(),
            LoopAbstractionInput::RegionProjection(rp) => rp.base.pcg_elems(),
        }
    }
}
impl<'tcx, Input: HasPcgElems<MaybeOldPlace<'tcx>>> HasPcgElems<MaybeOldPlace<'tcx>>
    for AbstractionBlockEdge<'tcx, Input>
{
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut result = vec![];
        for input in self.inputs.iter_mut() {
            result.extend(input.pcg_elems());
        }
        for output in self.outputs.iter_mut() {
            result.extend(output.pcg_elems());
        }
        result
    }
}
