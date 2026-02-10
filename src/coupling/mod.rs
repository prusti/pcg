mod coupled_edge;
mod data_source;
mod hyper_edge;
mod results;

use std::borrow::Cow;

pub use coupled_edge::{
    CoupledEdges, CoupledEdgesData, MaybeCoupledEdgeKind, MaybeCoupledEdges, PcgCoupledEdges,
};
use derive_more::{Deref, DerefMut, From};
pub(crate) use hyper_edge::HyperEdge;

use crate::{
    borrow_pcg::{
        MakeFunctionShapeError,
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
            kind::BorrowPcgEdgeType,
        },
        edge_data::{LabelEdgeLifetimeProjections, LabelNodePredicate},
        graph::Conditioned,
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionResult, LabelNodeContext,
            SourceOrTarget,
        },
        region_projection::LifetimeProjectionLabel,
    },
    coupling::{
        data_source::{CouplingDataSource, MutableCouplingDataSource},
        results::{CoupleEdgesResult, CouplingResults, PcgCoupleEdgesResult, PcgCouplingResults},
    },
    pcg::PcgNodeLike,
    utils::{
        DebugCtxt, PcgPlace, Place,
        data_structures::{HashMap, HashSet},
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        validity::HasValidityCheck,
    },
};
use std::hash::Hash;

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
pub enum CoupleAbstractionError<'tcx> {
    CoupleInput(CoupleInputError),
    MakeFunctionShape(MakeFunctionShapeError<'tcx>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoupleInputError;

impl<InputNode: Eq + Hash + Copy, OutputNode: Eq + Hash + Copy>
    CoupledEdgesData<InputNode, OutputNode>
{
    pub(crate) fn new(
        edges: impl IntoIterator<Item = AbstractionBlockEdge<'_, InputNode, OutputNode>>,
    ) -> Self {
        use union_find::{QuickUnionUf, UnionBySize, UnionFind};

        let edges: Vec<_> = edges.into_iter().map(|e| (e.input(), e.output())).collect();
        if edges.is_empty() {
            return Self(Vec::new());
        }

        let mut uf: QuickUnionUf<UnionBySize> = QuickUnionUf::new(edges.len());
        let mut input_to_edge: HashMap<InputNode, usize> = HashMap::default();
        let mut output_to_edge: HashMap<OutputNode, usize> = HashMap::default();

        for (idx, (input, output)) in edges.iter().enumerate() {
            if let Some(&other_idx) = input_to_edge.get(input) {
                uf.union(idx, other_idx);
            }
            input_to_edge.insert(*input, idx);

            if let Some(&other_idx) = output_to_edge.get(output) {
                uf.union(idx, other_idx);
            }
            output_to_edge.insert(*output, idx);
        }

        let mut groups: HashMap<usize, (HashSet<InputNode>, HashSet<OutputNode>)> =
            HashMap::default();
        for (idx, (input, output)) in edges.into_iter().enumerate() {
            let root = uf.find(idx);
            let entry = groups.entry(root).or_default();
            entry.0.insert(input);
            entry.1.insert(output);
        }

        let hyper_edges = groups
            .into_values()
            .filter(|(inputs, outputs)| !inputs.is_empty() && !outputs.is_empty())
            .map(|(inputs, outputs)| {
                HyperEdge::new(inputs.into_iter().collect(), outputs.into_iter().collect())
            })
            .collect();

        Self(hyper_edges)
    }
}

/// A coupled edge derived from a function or loop
#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct PcgCoupledEdgeKind<'tcx, P = Place<'tcx>>(
    pub FunctionCallOrLoop<FunctionCallCoupledEdgeKind<'tcx, P>, LoopCoupledEdgeKind<'tcx, P>>,
);

#[derive(Eq, Hash, PartialEq, Clone, Debug, Deref, DerefMut)]
pub struct CoupledEdgeKind<Metadata, InputNode, OutputNode> {
    metadata: Metadata,
    #[deref]
    #[deref_mut]
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
                self.edge.inputs().display_output(ctxt, mode),
                DisplayOutput::Text(Cow::Borrowed(" -> ")),
                self.edge.outputs().display_output(ctxt, mode),
            ])
        }
    }
}

pub type FunctionCallCoupledEdgeKind<'tcx, P = Place<'tcx>> = CoupledEdgeKind<
    FunctionCallAbstractionEdgeMetadata<'tcx>,
    FunctionCallAbstractionInput<'tcx, P>,
    FunctionCallAbstractionOutput<'tcx, P>,
>;

pub type LoopCoupledEdgeKind<'tcx, P = Place<'tcx>> = CoupledEdgeKind<
    LoopAbstractionEdgeMetadata,
    LoopAbstractionInput<'tcx, P>,
    LoopAbstractionOutput<'tcx, P>,
>;

impl<Ctxt: Copy + DebugCtxt> HasValidityCheck<Ctxt> for PcgCoupledEdgeKind<'_> {
    fn check_validity(&self, _ctxt: Ctxt) -> Result<(), String> {
        todo!()
    }
}

impl<
    'tcx,
    Ctxt: Copy,
    P: PcgPlace<'tcx, Ctxt>,
    Input: LabelLifetimeProjection<'tcx> + PcgNodeLike<'tcx, Ctxt, P>,
    Output: LabelLifetimeProjection<'tcx> + PcgNodeLike<'tcx, Ctxt, P>,
> LabelEdgeLifetimeProjections<'tcx, Ctxt, P> for HyperEdge<Input, Output>
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        let source_context =
            LabelNodeContext::new(SourceOrTarget::Source, BorrowPcgEdgeType::Coupled);
        let target_context =
            LabelNodeContext::new(SourceOrTarget::Target, BorrowPcgEdgeType::Coupled);
        let mut result = LabelLifetimeProjectionResult::Unchanged;
        for input in &mut self.inputs {
            if predicate.applies_to(input.to_pcg_node(ctxt), source_context) {
                result |= input.label_lifetime_projection(label);
            }
        }
        for output in &mut self.outputs {
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
    P: PcgPlace<'tcx, Ctxt>,
    Metadata,
    Input: LabelLifetimeProjection<'tcx> + PcgNodeLike<'tcx, Ctxt, P>,
    Output: LabelLifetimeProjection<'tcx> + PcgNodeLike<'tcx, Ctxt, P>,
> LabelEdgeLifetimeProjections<'tcx, Ctxt, P> for CoupledEdgeKind<Metadata, Input, Output>
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        self.edge.label_lifetime_projections(predicate, label, ctxt)
    }
}

impl<'tcx, Ctxt: Copy, P> LabelEdgeLifetimeProjections<'tcx, Ctxt, P>
    for PcgCoupledEdgeKind<'tcx, P>
where
    FunctionCallCoupledEdgeKind<'tcx, P>: LabelEdgeLifetimeProjections<'tcx, Ctxt, P>,
    LoopCoupledEdgeKind<'tcx, P>: LabelEdgeLifetimeProjections<'tcx, Ctxt, P>,
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
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
    let coupled_edges = CoupledEdgesData::new(edges.iter().copied());
    CoupleEdgesResult(Ok(f(CoupledEdges {
        metadata,
        edges: coupled_edges,
    })))
}

trait ObtainEdges<'tcx, Input> {
    fn obtain_abstraction_edges(input: Input) -> HashSet<Conditioned<AbstractionEdge<'tcx>>>;
}

struct ObtainExtract;
#[allow(unused)]
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

impl<'tcx> PcgCoupledEdges<'tcx> {
    pub(crate) fn extract_from_data_source(
        data_source: &mut impl MutableCouplingDataSource<'tcx>,
    ) -> PcgCouplingResults<'tcx> {
        Self::obtain_from_data_source::<_, ObtainExtract>(data_source)
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
