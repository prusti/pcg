use derive_more::Deref;
use itertools::Itertools;

use crate::{
    borrow_pcg::{
        AbstractionInputTarget, AbstractionOutputTarget,
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike},
        domain::{
            FunctionCallAbstractionInput, FunctionCallAbstractionOutput, LoopAbstractionInput,
            LoopAbstractionOutput,
        },
        edge::{
            abstraction::{
                AbstractionBlockEdge, AbstractionEdge, FunctionCallOrLoop,
                function::{
                    AbstractionBlockEdgeWithMetadata, FunctionCallAbstraction,
                    FunctionCallAbstractionEdge, FunctionCallAbstractionEdgeMetadata,
                },
                r#loop::{LoopAbstraction, LoopAbstractionEdge, LoopAbstractionEdgeMetadata},
            },
            kind::BorrowPcgEdgeKind,
        },
        edge_data::EdgeData,
        graph::{BorrowsGraph, Conditioned},
    },
    pcg::PcgNodeLike,
    utils::{
        CompilerCtxt,
        data_structures::{HashMap, HashSet},
    },
};
use std::hash::Hash;

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct HyperEdge<InputNode, OutputNode> {
    inputs: Vec<InputNode>,
    outputs: Vec<OutputNode>,
}

impl<InputNode, OutputNode> HyperEdge<InputNode, OutputNode> {
    pub(crate) fn new(inputs: Vec<InputNode>, outputs: Vec<OutputNode>) -> Self {
        Self { inputs, outputs }
    }
    pub fn inputs(&self) -> &Vec<InputNode> {
        &self.inputs
    }
    pub fn outputs(&self) -> &Vec<OutputNode> {
        &self.outputs
    }
}

/// A collection of hyper edges generated for a function or loop, without
/// identifying metadata.
#[derive(Eq, Hash, PartialEq, Clone, Debug, Deref)]
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

impl<SourceData> CouplingError<Vec<SourceData>> {
    pub(crate) fn map_each_source_data_element<T>(
        self,
        f: impl FnMut(SourceData) -> T,
    ) -> CouplingError<Vec<T>> {
        CouplingError {
            source_data: self.source_data.into_iter().map(f).collect(),
            error_type: self.error_type,
        }
    }
}

pub struct CoupleInputError;

impl<InputNode: Eq + Hash + Copy, OutputNode: Eq + Hash + Copy>
    CoupledEdgesData<InputNode, OutputNode>
{
    fn try_couple_input(
        input: InputNode,
        other_inputs: &mut Vec<InputNode>,
        outputs_map: &mut HashMap<InputNode, HashSet<OutputNode>>,
    ) -> Result<HyperEdge<InputNode, OutputNode>, CoupleInputError> {
        let expected_outputs = outputs_map[&input].clone();
        if expected_outputs.is_empty() {
            return Err(CoupleInputError);
        }
        let other_inputs_in_edge: Vec<InputNode> = other_inputs
            .extract_if(.., |elem| outputs_map[elem] == expected_outputs)
            .collect();
        outputs_map.retain(|input, _| !other_inputs_in_edge.contains(input));
        for v in outputs_map.values_mut() {
            v.retain(|output| !expected_outputs.contains(output));
        }
        Ok(HyperEdge {
            inputs: other_inputs_in_edge,
            outputs: expected_outputs.into_iter().collect(),
        })
    }

    pub(crate) fn new(
        edges: HashSet<AbstractionBlockEdge<'_, InputNode, OutputNode>>,
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
    Conditioned<LoopAbstractionEdgeMetadata<'tcx>>,
    LoopAbstractionInput<'tcx>,
    LoopAbstractionOutput<'tcx>,
>;

/// A coupled edge derived from a function or loop
#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct PcgCoupledEdge<'tcx>(
    FunctionCallOrLoop<
        HyperEdge<FunctionCallAbstractionInput<'tcx>, FunctionCallAbstractionOutput<'tcx>>,
        HyperEdge<LoopAbstractionInput<'tcx>, LoopAbstractionOutput<'tcx>>,
    >,
);

impl<'tcx> PcgCoupledEdge<'tcx> {
    pub(crate) fn function_call(
        edge: HyperEdge<FunctionCallAbstractionInput<'tcx>, FunctionCallAbstractionOutput<'tcx>>,
    ) -> Self {
        Self(FunctionCallOrLoop::FunctionCall(edge))
    }
    pub(crate) fn loop_(
        edge: HyperEdge<LoopAbstractionInput<'tcx>, LoopAbstractionOutput<'tcx>>,
    ) -> Self {
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
    fn function_call(edges: FunctionCoupledEdges<'tcx>) -> Self {
        Self(FunctionCallOrLoop::FunctionCall(edges))
    }
    fn loop_(edges: LoopCoupledEdges<'tcx>) -> Self {
        Self(FunctionCallOrLoop::Loop(edges))
    }
    fn edges(&self) -> HashSet<PcgCoupledEdge<'tcx>> {
        fn for_function_call<'tcx>(
            data: FunctionCoupledEdges<'tcx>,
        ) -> HashSet<PcgCoupledEdge<'tcx>> {
            data.edges
                .0
                .into_iter()
                .map(PcgCoupledEdge::function_call)
                .collect()
        }
        fn for_loop<'tcx>(data: LoopCoupledEdges<'tcx>) -> HashSet<PcgCoupledEdge<'tcx>> {
            data.edges
                .0
                .into_iter()
                .map(PcgCoupledEdge::loop_)
                .collect()
        }
        self.0.clone().bimap(for_function_call, for_loop)
    }
}

/// Either all of the coupled edges for a function or loop, or an error
#[derive(Eq, Hash, PartialEq, Clone, Debug, Deref)]
struct CoupleEdgesResult<'tcx, SourceEdges>(
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

fn couple_edges<
    'tcx,
    Metadata: Clone,
    InputNode: Eq + Hash + Copy,
    OutputNode: Eq + Hash + Copy,
>(
    metadata: Metadata,
    edges: HashSet<AbstractionBlockEdge<'tcx, InputNode, OutputNode>>,
    f: impl FnOnce(CoupledEdges<Metadata, InputNode, OutputNode>) -> PcgCoupledEdges<'tcx>,
) -> CoupleEdgesResult<'tcx, Metadata> {
    CoupleEdgesResult(match CoupledEdgesData::new(edges.clone()) {
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

pub trait CouplingDataSource<'tcx> {
    fn extract_abstraction_edges(&mut self) -> HashSet<Conditioned<AbstractionEdge<'tcx>>>;
}

impl<'tcx> CouplingDataSource<'tcx> for HashSet<BorrowPcgEdge<'tcx>> {
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
    ) -> HashSet<MaybeCoupledEdge<'tcx, Conditioned<AbstractionEdge<'tcx>>>> {
        self.into_iter()
            .flat_map(|result| match result.0 {
                Ok(result) => result
                    .edges()
                    .into_iter()
                    .map(MaybeCoupledEdge::Coupled)
                    .collect(),
                Err(other) => {
                    other
                        .map_each_source_data_element(MaybeCoupledEdge::NotCoupled)
                        .source_data
                }
            })
            .collect()
    }
}

impl<'tcx> PcgCoupledEdges<'tcx> {
    /// Returns the set of successful coupling results based on the abstraction
    /// edges.  If you are also interested in the unsuccessful
    /// couplings, use [`PcgCoupledEdges::coupling_results`].
    pub fn coupled_edges(
        mut data_source: impl CouplingDataSource<'tcx>,
    ) -> Vec<PcgCoupledEdge<'tcx>> {
        PcgCoupledEdges::from_data_source(&mut data_source)
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

    pub fn from_data_source(
        data_source: &mut impl CouplingDataSource<'tcx>,
    ) -> PcgCouplingResults<'tcx> {
        let mut function_edges: HashMap<
            Conditioned<FunctionCallAbstractionEdgeMetadata<'tcx>>,
            HashSet<FunctionCallAbstractionEdge<'tcx>>,
        > = HashMap::default();
        let mut loop_edges: HashMap<
            Conditioned<LoopAbstractionEdgeMetadata<'tcx>>,
            HashSet<LoopAbstractionEdge<'tcx>>,
        > = HashMap::default();
        for edge in data_source.extract_abstraction_edges() {
            match edge.value {
                AbstractionEdge::FunctionCall(function_call) => {
                    function_edges
                        .entry(Conditioned::new(function_call.metadata, edge.conditions))
                        .or_default()
                        .insert(function_call.edge.clone());
                }
                AbstractionEdge::Loop(loop_abstraction) => {
                    loop_edges
                        .entry(Conditioned::new(loop_abstraction.metadata, edge.conditions))
                        .or_default()
                        .insert(loop_abstraction.edge.clone());
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
                                metadata.value.location,
                                metadata.value.function_data,
                                edge.clone(),
                            )),
                            metadata.conditions.clone(),
                        )
                    })
                    .collect::<Vec<_>>()
            };
        let restore_loop_edge = |metadata: Conditioned<LoopAbstractionEdgeMetadata<'tcx>>| {
            loop_edges[&metadata]
                .iter()
                .map(|edge| {
                    Conditioned::new(
                        AbstractionEdge::Loop(LoopAbstraction::new(edge.clone(), metadata.value)),
                        metadata.conditions.clone(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let mut result: Vec<PcgCoupleEdgesResult<'tcx>> = function_edges
            .iter()
            .map(|(metadata, edges)| {
                couple_edges(
                    metadata.clone(),
                    edges.clone(),
                    PcgCoupledEdges::function_call,
                )
                .map_source_edges(restore_fn_edges)
            })
            .collect::<Vec<_>>();
        result.extend(loop_edges.iter().map(|(metadata, edges)| {
            couple_edges(metadata.clone(), edges.clone(), PcgCoupledEdges::loop_)
                .map_source_edges(restore_loop_edge)
        }));
        CouplingResults::new(result)
    }
}

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub enum MaybeCoupledEdge<'tcx, T> {
    Coupled(PcgCoupledEdge<'tcx>),
    NotCoupled(T),
}

impl<'tcx, T> MaybeCoupledEdge<'tcx, T> {
    pub(crate) fn map_not_coupled<U>(self, f: impl FnOnce(T) -> U) -> MaybeCoupledEdge<'tcx, U> {
        match self {
            MaybeCoupledEdge::Coupled(coupled) => MaybeCoupledEdge::Coupled(coupled),
            MaybeCoupledEdge::NotCoupled(not_coupled) => {
                MaybeCoupledEdge::NotCoupled(f(not_coupled))
            }
        }
    }
}

impl<'tcx> EdgeData<'tcx> for PcgCoupledEdge<'tcx> {
    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = crate::pcg::PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(self.inputs(ctxt).into_iter().map(|input| input.0))
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        _ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<
        dyn std::iter::Iterator<Item = crate::borrow_pcg::borrow_pcg_edge::LocalNode<'tcx>> + 'slf,
    >
    where
        'tcx: 'mir,
    {
        Box::new(self.outputs().into_iter().map(|output| output.0))
    }
}

impl<'tcx, T: EdgeData<'tcx>> EdgeData<'tcx> for MaybeCoupledEdge<'tcx, T> {
    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = crate::pcg::PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        match self {
            MaybeCoupledEdge::Coupled(coupled) => coupled.blocked_nodes(ctxt),
            MaybeCoupledEdge::NotCoupled(normal) => normal.blocked_nodes(ctxt),
        }
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<
        dyn std::iter::Iterator<Item = crate::borrow_pcg::borrow_pcg_edge::LocalNode<'tcx>> + 'slf,
    >
    where
        'tcx: 'mir,
    {
        match self {
            MaybeCoupledEdge::Coupled(coupled) => coupled.blocked_by_nodes(ctxt),
            MaybeCoupledEdge::NotCoupled(normal) => normal.blocked_by_nodes(ctxt),
        }
    }
}
