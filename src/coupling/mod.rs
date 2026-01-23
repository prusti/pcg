use std::borrow::Cow;

use derive_more::{Deref, From, IntoIterator};
use itertools::Itertools;

use crate::{
    borrow_pcg::{
        AbstractionInputTarget, AbstractionOutputTarget, MakeFunctionShapeError,
        borrow_pcg_edge::{BorrowPcgEdge, LocalNode},
        domain::{
            FunctionCallAbstractionInput, FunctionCallAbstractionOutput, LoopAbstractionInput,
            LoopAbstractionOutput,
        },
        edge::{
            abstraction::{
                AbstractionBlockEdge, AbstractionEdge, FunctionCallOrLoop,
                function::{
                    FunctionCallAbstraction, FunctionCallAbstractionEdge,
                    FunctionCallAbstractionEdgeMetadata,
                },
                r#loop::{LoopAbstraction, LoopAbstractionEdge, LoopAbstractionEdgeMetadata},
            },
            kind::{BorrowPcgEdgeKind, BorrowPcgEdgeType},
        },
        edge_data::{
            EdgeData, LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate,
            NodeReplacement, conditionally_label_places,
        },
        graph::{BorrowsGraph, Conditioned},
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionResult, LabelNodeContext, LabelPlace,
            SourceOrTarget,
        },
        region_projection::LifetimeProjectionLabel,
        validity_conditions::ValidityConditions,
    },
    pcg::PcgNodeLike,
    pcg_validity_assert,
    utils::{
        CompilerCtxt, DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt,
        data_structures::{HashMap, HashSet},
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        validity::HasValidityCheck,
    },
};
use std::hash::Hash;

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct HyperEdge<InputNode, OutputNode> {
    inputs: Vec<InputNode>,
    outputs: Vec<OutputNode>,
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

/// A collection of hyper edges generated for a function or loop, without
/// identifying metadata.
#[derive(Eq, Hash, PartialEq, Clone, Debug, Deref, IntoIterator)]
pub struct CoupledEdgesData<InputNode, OutputNode>(Vec<HyperEdge<InputNode, OutputNode>>);

impl<InputNode: Eq + Hash, OutputNode: Eq + Hash> CoupledEdgesData<InputNode, OutputNode> {
    pub fn into_hash_set(self) -> HashSet<HyperEdge<InputNode, OutputNode>> {
        self.0.into_iter().collect()
    }
}

#[derive(Eq, Hash, PartialEq, Copy, Clone, Debug)]
pub enum CouplingErrorType {
    CannotConstructShape,
}

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct CouplingError<SourceData> {
    source_data: SourceData,
    error_type: CouplingErrorType,
}

impl<SourceData> CouplingError<SourceData> {
    pub(crate) fn map_source_data<T>(self, f: impl FnOnce(SourceData) -> T) -> CouplingError<T> {
        CouplingError {
            source_data: f(self.source_data),
            error_type: self.error_type,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, From)]
pub enum CoupleAbstractionError {
    CoupleInput(CoupleInputError),
    MakeFunctionShape(MakeFunctionShapeError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoupleInputError;

impl<InputNode: Eq + Hash + Copy, OutputNode: Eq + Hash + Copy>
    CoupledEdgesData<InputNode, OutputNode>
{
    #[cfg(not(feature = "coupling"))]
    fn try_couple_input(
        input: InputNode,
        other_inputs: &mut Vec<InputNode>,
        outputs_map: &mut HashMap<InputNode, HashSet<OutputNode>>,
    ) -> Result<HyperEdge<InputNode, OutputNode>, CoupleInputError> {
        unimplemented!(
            "Enable the `coupling` feature to use this function.  Coupling
            functionality is locked behind a feature flag because it is only
            supported on relatively recent Rust versions (for example, the
            implementation uses [`Vec::extract_if`] which is only available in
            Rust 1.87.0 and later)."
        )
    }

    #[cfg(feature = "coupling")]
    fn try_couple_input(
        input: InputNode,
        other_inputs: &mut Vec<InputNode>,
        outputs_map: &mut HashMap<InputNode, HashSet<OutputNode>>,
    ) -> Result<HyperEdge<InputNode, OutputNode>, CoupleInputError> {
        let expected_outputs = outputs_map[&input].clone();
        if expected_outputs.is_empty() {
            return Err(CoupleInputError);
        }
        let mut coupled_inputs: Vec<InputNode> = other_inputs
            .extract_if(.., |elem| outputs_map[elem] == expected_outputs)
            .collect();
        outputs_map.retain(|input, _| !coupled_inputs.contains(input));
        for v in outputs_map.values_mut() {
            v.retain(|output| !expected_outputs.contains(output));
        }
        coupled_inputs.push(input);
        Ok(HyperEdge::new(
            coupled_inputs,
            expected_outputs.into_iter().collect(),
        ))
    }

    pub(crate) fn new(
        edges: impl IntoIterator<Item = AbstractionBlockEdge<'_, InputNode, OutputNode>>,
    ) -> Result<Self, CoupleInputError> {
        let mut inputs = HashSet::default();
        let mut outputs_map: HashMap<InputNode, HashSet<OutputNode>> = HashMap::default();
        for edge in edges {
            inputs.insert(edge.input());
            outputs_map
                .entry(edge.input())
                .or_default()
                .insert(edge.output());
        }
        let mut inputs = inputs.into_iter().collect_vec();
        let mut hyper_edges = Vec::default();
        while let Some(input) = inputs.pop() {
            let edge = Self::try_couple_input(input, &mut inputs, &mut outputs_map)?;
            hyper_edges.push(edge);
        }
        Ok(Self(hyper_edges))
    }
}

/// A collection of hyper edges generated for a function or loop, alongside
/// metadata indicating their origin.
#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct CoupledEdges<Metadata, InputNode, OutputNode> {
    metadata: Metadata,
    edges: CoupledEdgesData<InputNode, OutputNode>,
}

type FunctionCoupledEdges<'tcx> = CoupledEdges<
    Conditioned<FunctionCallAbstractionEdgeMetadata<'tcx>>,
    FunctionCallAbstractionInput<'tcx>,
    FunctionCallAbstractionOutput<'tcx>,
>;

type LoopCoupledEdges<'tcx> = CoupledEdges<
    Conditioned<LoopAbstractionEdgeMetadata>,
    LoopAbstractionInput<'tcx>,
    LoopAbstractionOutput<'tcx>,
>;

/// A coupled edge derived from a function or loop
#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct PcgCoupledEdgeKind<'tcx>(
    pub FunctionCallOrLoop<FunctionCallCoupledEdgeKind<'tcx>, LoopCoupledEdgeKind<'tcx>>,
);

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct CoupledEdgeKind<Metadata, InputNode, OutputNode> {
    metadata: Metadata,
    edge: HyperEdge<InputNode, OutputNode>,
}

impl<Metadata, InputNode, OutputNode> CoupledEdgeKind<Metadata, InputNode, OutputNode> {
    pub(crate) fn new(metadata: Metadata, edge: HyperEdge<InputNode, OutputNode>) -> Self {
        Self { metadata, edge }
    }
    pub(crate) fn inputs(&self) -> &Vec<InputNode> {
        self.edge.inputs()
    }

    pub(crate) fn outputs(&self) -> &Vec<OutputNode> {
        self.edge.outputs()
    }

    pub fn metadata(&self) -> &Metadata {
        &self.metadata
    }
}

impl<
    Ctxt: Copy,
    Metadata: DisplayWithCtxt<Ctxt>,
    InputNode: DisplayWithCtxt<Ctxt>,
    OutputNode: DisplayWithCtxt<Ctxt>,
> DisplayWithCtxt<Ctxt> for CoupledEdgeKind<Metadata, InputNode, OutputNode>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        if let Some((input, output)) = self.edge.try_to_singleton_edge() {
            DisplayOutput::Seq(vec![
                self.metadata.display_output(ctxt, mode),
                DisplayOutput::Text(Cow::Borrowed(": ")),
                input.display_output(ctxt, mode),
                DisplayOutput::Text(Cow::Borrowed(" -> ")),
                output.display_output(ctxt, mode),
            ])
        } else {
            DisplayOutput::Seq(vec![
                self.metadata.display_output(ctxt, mode),
                DisplayOutput::Text(Cow::Borrowed(": ")),
                self.edge.inputs.display_output(ctxt, mode),
                DisplayOutput::Text(Cow::Borrowed(" -> ")),
                self.edge.outputs.display_output(ctxt, mode),
            ])
        }
    }
}

pub type FunctionCallCoupledEdgeKind<'tcx> = CoupledEdgeKind<
    FunctionCallAbstractionEdgeMetadata<'tcx>,
    FunctionCallAbstractionInput<'tcx>,
    FunctionCallAbstractionOutput<'tcx>,
>;

pub type LoopCoupledEdgeKind<'tcx> = CoupledEdgeKind<
    LoopAbstractionEdgeMetadata,
    LoopAbstractionInput<'tcx>,
    LoopAbstractionOutput<'tcx>,
>;

impl<'tcx, Ctxt: Copy + DebugCtxt> HasValidityCheck<Ctxt> for PcgCoupledEdgeKind<'tcx> {
    fn check_validity(&self, _ctxt: Ctxt) -> Result<(), String> {
        todo!()
    }
}

impl<
    'tcx,
    Ctxt: Copy,
    Input: LabelLifetimeProjection<'tcx> + PcgNodeLike<'tcx, Ctxt>,
    Output: LabelLifetimeProjection<'tcx> + PcgNodeLike<'tcx, Ctxt>,
> LabelEdgeLifetimeProjections<'tcx, Ctxt> for HyperEdge<Input, Output>
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        let source_context =
            LabelNodeContext::new(SourceOrTarget::Source, BorrowPcgEdgeType::Coupled);
        let target_context =
            LabelNodeContext::new(SourceOrTarget::Target, BorrowPcgEdgeType::Coupled);
        let mut result = LabelLifetimeProjectionResult::Unchanged;
        for input in self.inputs.iter_mut() {
            if predicate.applies_to(input.to_pcg_node(ctxt), source_context) {
                result |= input.label_lifetime_projection(label);
            }
        }
        for output in self.outputs.iter_mut() {
            if predicate.applies_to(output.to_pcg_node(ctxt), target_context) {
                result |= output.label_lifetime_projection(label);
            }
        }
        result
    }
}

impl<
    'tcx,
    Ctxt: Copy,
    Metadata,
    Input: LabelLifetimeProjection<'tcx> + PcgNodeLike<'tcx, Ctxt>,
    Output: LabelLifetimeProjection<'tcx> + PcgNodeLike<'tcx, Ctxt>,
> LabelEdgeLifetimeProjections<'tcx, Ctxt> for CoupledEdgeKind<Metadata, Input, Output>
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        self.edge.label_lifetime_projections(predicate, label, ctxt)
    }
}

impl<'tcx, Ctxt: Copy> LabelEdgeLifetimeProjections<'tcx, Ctxt> for PcgCoupledEdgeKind<'tcx> {
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        match &mut self.0 {
            FunctionCallOrLoop::FunctionCall(function) => {
                function.label_lifetime_projections(predicate, label, ctxt)
            }
            FunctionCallOrLoop::Loop(loop_) => {
                loop_.label_lifetime_projections(predicate, label, ctxt)
            }
        }
    }
}

impl<
    'tcx,
    Ctxt: Copy + DebugCtxt,
    Input: LabelPlace<'tcx, Ctxt> + PcgNodeLike<'tcx, Ctxt>,
    Output: LabelPlace<'tcx, Ctxt> + PcgNodeLike<'tcx, Ctxt>,
> LabelEdgePlaces<'tcx, Ctxt> for HyperEdge<Input, Output>
{
    fn label_blocked_places(
        &mut self,
        predicate: &crate::borrow_pcg::edge_data::LabelNodePredicate<'tcx>,
        labeller: &impl crate::borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx, Ctxt>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx>> {
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
        predicate: &crate::borrow_pcg::edge_data::LabelNodePredicate<'tcx>,
        labeller: &impl crate::borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx, Ctxt>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx>> {
        conditionally_label_places(
            self.outputs.iter_mut(),
            predicate,
            labeller,
            LabelNodeContext::new(SourceOrTarget::Target, BorrowPcgEdgeType::Coupled),
            ctxt,
        )
    }
}

impl<
    'a,
    'tcx,
    Metadata,
    Ctxt: Copy + DebugCtxt + HasCompilerCtxt<'a, 'tcx>,
    Input: LabelPlace<'tcx, Ctxt> + PcgNodeLike<'tcx, Ctxt>,
    Output: LabelPlace<'tcx, Ctxt> + PcgNodeLike<'tcx, Ctxt>,
> LabelEdgePlaces<'tcx, Ctxt> for CoupledEdgeKind<Metadata, Input, Output>
{
    fn label_blocked_places(
        &mut self,
        predicate: &crate::borrow_pcg::edge_data::LabelNodePredicate<'tcx>,
        labeller: &impl crate::borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx, Ctxt>,
        ctxt: Ctxt,
    ) -> HashSet<crate::borrow_pcg::edge_data::NodeReplacement<'tcx>> {
        self.edge.label_blocked_places(predicate, labeller, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &crate::borrow_pcg::edge_data::LabelNodePredicate<'tcx>,
        labeller: &impl crate::borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx, Ctxt>,
        ctxt: Ctxt,
    ) -> HashSet<crate::borrow_pcg::edge_data::NodeReplacement<'tcx>> {
        self.edge.label_blocked_by_places(predicate, labeller, ctxt)
    }
}

impl<'a, 'tcx, Ctxt: Copy + DebugCtxt + HasCompilerCtxt<'a, 'tcx>> LabelEdgePlaces<'tcx, Ctxt>
    for PcgCoupledEdgeKind<'tcx>
{
    fn label_blocked_places(
        &mut self,
        predicate: &crate::borrow_pcg::edge_data::LabelNodePredicate<'tcx>,
        labeller: &impl crate::borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx, Ctxt>,
        ctxt: Ctxt,
    ) -> HashSet<crate::borrow_pcg::edge_data::NodeReplacement<'tcx>> {
        match &mut self.0 {
            FunctionCallOrLoop::FunctionCall(function) => {
                function.label_blocked_places(predicate, labeller, ctxt)
            }
            FunctionCallOrLoop::Loop(loop_) => {
                loop_.label_blocked_places(predicate, labeller, ctxt)
            }
        }
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &crate::borrow_pcg::edge_data::LabelNodePredicate<'tcx>,
        labeller: &impl crate::borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx, Ctxt>,
        ctxt: Ctxt,
    ) -> HashSet<crate::borrow_pcg::edge_data::NodeReplacement<'tcx>> {
        match &mut self.0 {
            FunctionCallOrLoop::FunctionCall(function) => {
                function.label_blocked_by_places(predicate, labeller, ctxt)
            }
            FunctionCallOrLoop::Loop(loop_) => {
                loop_.label_blocked_by_places(predicate, labeller, ctxt)
            }
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for PcgCoupledEdgeKind<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match self {
            PcgCoupledEdgeKind(FunctionCallOrLoop::FunctionCall(function)) => {
                function.display_output(ctxt, mode)
            }
            PcgCoupledEdgeKind(FunctionCallOrLoop::Loop(loop_)) => loop_.display_output(ctxt, mode),
        }
    }
}

impl<'tcx> PcgCoupledEdgeKind<'tcx> {
    pub(crate) fn function_call(edge: FunctionCallCoupledEdgeKind<'tcx>) -> Self {
        Self(FunctionCallOrLoop::FunctionCall(edge))
    }
    pub(crate) fn loop_(edge: LoopCoupledEdgeKind<'tcx>) -> Self {
        Self(FunctionCallOrLoop::Loop(edge))
    }
    pub fn inputs<C: Copy>(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> Vec<AbstractionInputTarget<'tcx>> {
        match &self.0 {
            FunctionCallOrLoop::FunctionCall(function) => function
                .inputs()
                .iter()
                .map(|input| AbstractionInputTarget((*input).to_pcg_node(ctxt)))
                .collect(),
            FunctionCallOrLoop::Loop(loop_) => loop_
                .inputs()
                .iter()
                .map(|input| AbstractionInputTarget((*input).into()))
                .collect(),
        }
    }

    pub fn outputs(&self) -> Vec<AbstractionOutputTarget<'tcx>> {
        match &self.0 {
            FunctionCallOrLoop::FunctionCall(function) => function
                .outputs()
                .iter()
                .map(|output| AbstractionOutputTarget((**output).into()))
                .collect(),
            FunctionCallOrLoop::Loop(loop_) => loop_
                .outputs()
                .iter()
                .map(|output| AbstractionOutputTarget(**output))
                .collect(),
        }
    }
}

/// The set of coupled edges derived from a function or loop, alongside
/// metadata indicating their origin.
#[derive(Deref, PartialEq, Eq, Hash, Clone, Debug)]
pub struct PcgCoupledEdges<'tcx>(
    FunctionCallOrLoop<FunctionCoupledEdges<'tcx>, LoopCoupledEdges<'tcx>>,
);

impl<'tcx> PcgCoupledEdges<'tcx> {
    pub(crate) fn conditions(&self) -> &ValidityConditions {
        match &self.0 {
            FunctionCallOrLoop::FunctionCall(function) => &function.metadata.conditions,
            FunctionCallOrLoop::Loop(loop_) => &loop_.metadata.conditions,
        }
    }
    fn function_call(edges: FunctionCoupledEdges<'tcx>) -> Self {
        Self(FunctionCallOrLoop::FunctionCall(edges))
    }
    fn loop_(edges: LoopCoupledEdges<'tcx>) -> Self {
        Self(FunctionCallOrLoop::Loop(edges))
    }
    pub(crate) fn edges(&self) -> HashSet<PcgCoupledEdgeKind<'tcx>> {
        fn for_function_call<'tcx>(
            data: FunctionCoupledEdges<'tcx>,
        ) -> HashSet<PcgCoupledEdgeKind<'tcx>> {
            data.edges
                .0
                .into_iter()
                .map(|edge| {
                    PcgCoupledEdgeKind::function_call(FunctionCallCoupledEdgeKind::new(
                        data.metadata.value,
                        edge,
                    ))
                })
                .collect()
        }
        fn for_loop<'tcx>(data: LoopCoupledEdges<'tcx>) -> HashSet<PcgCoupledEdgeKind<'tcx>> {
            data.edges
                .0
                .into_iter()
                .map(|edge| {
                    PcgCoupledEdgeKind::loop_(LoopCoupledEdgeKind::new(data.metadata.value, edge))
                })
                .collect()
        }
        self.0.clone().bimap(for_function_call, for_loop)
    }
}

/// Either all of the coupled edges for a function or loop, or an error
#[derive(Eq, Hash, PartialEq, Clone, Debug, Deref)]
pub(crate) struct CoupleEdgesResult<'tcx, SourceEdges>(
    Result<PcgCoupledEdges<'tcx>, CouplingError<SourceEdges>>,
);

type PcgCoupleEdgesResult<'tcx> = CoupleEdgesResult<'tcx, Vec<Conditioned<AbstractionEdge<'tcx>>>>;

impl<'tcx, SourceEdges> CoupleEdgesResult<'tcx, SourceEdges> {
    pub(crate) fn map_source_edges<T>(
        self,
        f: impl FnOnce(SourceEdges) -> T,
    ) -> CoupleEdgesResult<'tcx, T> {
        CoupleEdgesResult(self.0.map_err(|e| e.map_source_data(f)))
    }
}

pub(crate) fn couple_edges<
    'tcx,
    Metadata: Clone,
    InputNode: Eq + Hash + Copy,
    OutputNode: Eq + Hash + Copy,
>(
    metadata: Metadata,
    edges: &HashSet<AbstractionBlockEdge<'tcx, InputNode, OutputNode>>,
    f: impl FnOnce(CoupledEdges<Metadata, InputNode, OutputNode>) -> PcgCoupledEdges<'tcx>,
) -> CoupleEdgesResult<'tcx, Metadata> {
    CoupleEdgesResult(match CoupledEdgesData::new(edges.iter().copied()) {
        Ok(coupled_edges) => Ok(f(CoupledEdges {
            metadata,
            edges: coupled_edges,
        })),
        Err(_) => Err(CouplingError {
            error_type: CouplingErrorType::CannotConstructShape,
            source_data: metadata,
        }),
    })
}

pub(crate) trait MutableCouplingDataSource<'tcx> {
    fn extract_abstraction_edges(&mut self) -> HashSet<Conditioned<AbstractionEdge<'tcx>>>;
}

pub(crate) trait CouplingDataSource<'tcx> {
    fn abstraction_edges(&self) -> HashSet<Conditioned<AbstractionEdge<'tcx>>>;
}

trait ObtainEdges<'tcx, Input> {
    fn obtain_abstraction_edges(input: Input) -> HashSet<Conditioned<AbstractionEdge<'tcx>>>;
}

struct ObtainExtract;
struct ObtainGet;

impl<'a, 'tcx: 'a, T: CouplingDataSource<'tcx> + 'a> ObtainEdges<'tcx, &'a T> for ObtainGet {
    fn obtain_abstraction_edges(input: &'a T) -> HashSet<Conditioned<AbstractionEdge<'tcx>>> {
        input.abstraction_edges()
    }
}

impl<'a, 'tcx: 'a, T: MutableCouplingDataSource<'tcx> + 'a> ObtainEdges<'tcx, &'a mut T>
    for ObtainExtract
{
    fn obtain_abstraction_edges(input: &'a mut T) -> HashSet<Conditioned<AbstractionEdge<'tcx>>> {
        input.extract_abstraction_edges()
    }
}

impl<'tcx> CouplingDataSource<'tcx> for BorrowsGraph<'tcx> {
    fn abstraction_edges(&self) -> HashSet<Conditioned<AbstractionEdge<'tcx>>> {
        self.edges
            .iter()
            .filter_map(|(kind, conditions)| match kind {
                BorrowPcgEdgeKind::Abstraction(abstraction) => {
                    Some(Conditioned::new(abstraction.clone(), conditions.clone()))
                }
                _ => None,
            })
            .collect()
    }
}

impl<'tcx> MutableCouplingDataSource<'tcx> for BorrowsGraph<'tcx> {
    fn extract_abstraction_edges(&mut self) -> HashSet<Conditioned<AbstractionEdge<'tcx>>> {
        let mut abstraction_edges = HashSet::default();
        self.edges.retain(|kind, conditions| match kind {
            BorrowPcgEdgeKind::Abstraction(abstraction) => {
                abstraction_edges.insert(Conditioned::new(abstraction.clone(), conditions.clone()));
                false
            }
            _ => true,
        });
        abstraction_edges
    }
}

impl<'tcx> MutableCouplingDataSource<'tcx> for HashSet<BorrowPcgEdge<'tcx>> {
    fn extract_abstraction_edges(&mut self) -> HashSet<Conditioned<AbstractionEdge<'tcx>>> {
        let mut abstraction_edges = HashSet::default();
        self.retain(|edge| match edge.kind() {
            BorrowPcgEdgeKind::Abstraction(abstraction) => {
                abstraction_edges.insert(Conditioned::new(
                    abstraction.clone(),
                    edge.conditions().clone(),
                ));
                false
            }
            _ => true,
        });
        abstraction_edges
    }
}

/// All results from an application of the coupling algorithm over a set of
/// abstraction edges
pub struct CouplingResults<'tcx, Err>(Vec<CoupleEdgesResult<'tcx, Err>>);

type PcgCouplingResults<'tcx> = CouplingResults<'tcx, Vec<Conditioned<AbstractionEdge<'tcx>>>>;

impl<'tcx, SourceData> CouplingResults<'tcx, SourceData> {
    fn new(results: Vec<CoupleEdgesResult<'tcx, SourceData>>) -> Self {
        Self(results)
    }

    fn into_iter(self) -> impl Iterator<Item = CoupleEdgesResult<'tcx, SourceData>> {
        self.0.into_iter()
    }
}

impl<'tcx> PcgCouplingResults<'tcx> {
    pub(crate) fn into_maybe_coupled_edges(
        self,
    ) -> HashSet<MaybeCoupledEdges<'tcx, Conditioned<AbstractionEdge<'tcx>>>> {
        self.into_iter()
            .map(|result| match result.0 {
                Ok(result) => MaybeCoupledEdges::Coupled(Box::new(result)),
                Err(other) => MaybeCoupledEdges::NotCoupled(other.source_data),
            })
            .collect()
    }
}

impl<'tcx> PcgCoupledEdges<'tcx> {
    #[allow(unused)]
    pub(crate) fn extract_coupled_edges(
        data_source: &mut impl MutableCouplingDataSource<'tcx>,
    ) -> Vec<PcgCoupledEdgeKind<'tcx>> {
        Self::coupled_edges::<_, ObtainExtract>(data_source)
    }

    #[allow(unused)]
    pub(crate) fn get_coupled_edges(
        data_source: &impl CouplingDataSource<'tcx>,
    ) -> Vec<PcgCoupledEdgeKind<'tcx>> {
        Self::coupled_edges::<_, ObtainGet>(data_source)
    }

    /// Returns the set of successful coupling results based on the abstraction
    /// edges.  If you are also interested in the unsuccessful
    /// couplings, use [`PcgCoupledEdges::from_data_source`].
    fn coupled_edges<T, ObtainType: ObtainEdges<'tcx, T>>(
        data_source: T,
    ) -> Vec<PcgCoupledEdgeKind<'tcx>> {
        PcgCoupledEdges::obtain_from_data_source::<_, ObtainType>(data_source)
            .into_iter()
            .flat_map(|result| {
                let set = match result.0 {
                    Ok(result) => result.edges(),
                    Err(_) => HashSet::default(),
                };
                set.into_iter()
            })
            .collect()
    }

    pub(crate) fn extract_from_data_source(
        data_source: &mut impl MutableCouplingDataSource<'tcx>,
    ) -> PcgCouplingResults<'tcx> {
        Self::obtain_from_data_source::<_, ObtainExtract>(data_source)
    }

    #[allow(unused)]
    pub(crate) fn get_from_data_source(
        data_source: &impl CouplingDataSource<'tcx>,
    ) -> PcgCouplingResults<'tcx> {
        Self::obtain_from_data_source::<_, ObtainGet>(data_source)
    }

    fn obtain_from_data_source<T, ObtainType: ObtainEdges<'tcx, T>>(
        data_source: T,
    ) -> PcgCouplingResults<'tcx> {
        let mut function_edges: HashMap<
            Conditioned<FunctionCallAbstractionEdgeMetadata<'tcx>>,
            HashSet<FunctionCallAbstractionEdge<'tcx>>,
        > = HashMap::default();
        let mut loop_edges: HashMap<
            Conditioned<LoopAbstractionEdgeMetadata>,
            HashSet<LoopAbstractionEdge<'tcx>>,
        > = HashMap::default();
        for edge in ObtainType::obtain_abstraction_edges(data_source) {
            match edge.value {
                AbstractionEdge::FunctionCall(function_call) => {
                    function_edges
                        .entry(Conditioned::new(function_call.metadata, edge.conditions))
                        .or_default()
                        .insert(function_call.edge);
                }
                AbstractionEdge::Loop(loop_abstraction) => {
                    loop_edges
                        .entry(Conditioned::new(loop_abstraction.metadata, edge.conditions))
                        .or_default()
                        .insert(loop_abstraction.edge);
                }
            }
        }
        let restore_fn_edges =
            |metadata: Conditioned<FunctionCallAbstractionEdgeMetadata<'tcx>>| {
                function_edges[&metadata]
                    .iter()
                    .map(|edge| {
                        Conditioned::new(
                            AbstractionEdge::FunctionCall(FunctionCallAbstraction::new(
                                metadata.value,
                                *edge,
                            )),
                            metadata.conditions.clone(),
                        )
                    })
                    .collect::<Vec<_>>()
            };
        let restore_loop_edge = |metadata: Conditioned<LoopAbstractionEdgeMetadata>| {
            loop_edges[&metadata]
                .iter()
                .map(|edge| {
                    Conditioned::new(
                        AbstractionEdge::Loop(LoopAbstraction::new(
                            *edge,
                            metadata.value.loop_head_block(),
                        )),
                        metadata.conditions.clone(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let mut result: Vec<PcgCoupleEdgesResult<'tcx>> = function_edges
            .iter()
            .map(|(metadata, edges)| {
                couple_edges(metadata.clone(), edges, PcgCoupledEdges::function_call)
                    .map_source_edges(restore_fn_edges)
            })
            .collect::<Vec<_>>();
        result.extend(loop_edges.iter().map(|(metadata, edges)| {
            couple_edges(metadata.clone(), edges, PcgCoupledEdges::loop_)
                .map_source_edges(restore_loop_edge)
        }));
        CouplingResults::new(result)
    }
}

pub enum MaybeCoupled<T, U> {
    Coupled(T),
    NotCoupled(U),
}

/// The maybe-coupled edges for a function call or loop
#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub enum MaybeCoupledEdges<'tcx, T> {
    Coupled(Box<PcgCoupledEdges<'tcx>>),
    NotCoupled(Vec<T>),
}

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub enum MaybeCoupledEdgeKind<'tcx, T> {
    Coupled(PcgCoupledEdgeKind<'tcx>),
    NotCoupled(T),
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>, T: DisplayWithCtxt<Ctxt>>
    DisplayWithCtxt<Ctxt> for MaybeCoupledEdgeKind<'tcx, T>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match self {
            MaybeCoupledEdgeKind::Coupled(coupled) => coupled.display_output(ctxt, mode),
            MaybeCoupledEdgeKind::NotCoupled(normal) => normal.display_output(ctxt, mode),
        }
    }
}

impl<'a, 'tcx, BC: Copy> EdgeData<'tcx, CompilerCtxt<'a, 'tcx, BC>> for PcgCoupledEdgeKind<'tcx> {
    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'a, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = crate::pcg::PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(self.inputs(ctxt).into_iter().map(|input| input.0))
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        _ctxt: CompilerCtxt<'a, 'tcx, BC>,
    ) -> Box<
        dyn std::iter::Iterator<Item = crate::borrow_pcg::borrow_pcg_edge::LocalNode<'tcx>> + 'slf,
    >
    where
        'tcx: 'slf,
    {
        Box::new(self.outputs().into_iter().map(|output| output.0))
    }
}

impl<'a, 'tcx, BC: Copy, T: EdgeData<'tcx, CompilerCtxt<'a, 'tcx, BC>>>
    EdgeData<'tcx, CompilerCtxt<'a, 'tcx, BC>> for MaybeCoupledEdgeKind<'tcx, T>
{
    fn blocked_nodes<'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'a, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = crate::pcg::PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        match self {
            MaybeCoupledEdgeKind::Coupled(coupled) => coupled.blocked_nodes(ctxt),
            MaybeCoupledEdgeKind::NotCoupled(normal) => normal.blocked_nodes(ctxt),
        }
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'a, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        match self {
            MaybeCoupledEdgeKind::Coupled(coupled) => coupled.blocked_by_nodes(ctxt),
            MaybeCoupledEdgeKind::NotCoupled(normal) => normal.blocked_by_nodes(ctxt),
        }
    }
}
