use derive_more::Deref;
use itertools::Itertools;

use crate::{
    borrow_pcg::{
        AbstractionInputTarget, AbstractionOutputTarget,
        borrow_pcg_edge::BorrowPcgEdgeLike,
        domain::{
            FunctionCallAbstractionInput, FunctionCallAbstractionOutput, LoopAbstractionInput,
            LoopAbstractionOutput,
        },
        edge::{
            abstraction::{
                AbstractionBlockEdge, AbstractionEdge, FunctionCallOrLoop,
                function::{
                    AbstractionBlockEdgeWithMetadata, FunctionCallAbstractionEdge,
                    FunctionCallAbstractionEdgeMetadata,
                },
                r#loop::{LoopAbstractionEdge, LoopAbstractionEdgeMetadata},
            },
            kind::BorrowPcgEdgeKind,
        },
        graph::BorrowsGraph,
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

#[derive(Eq, Hash, PartialEq, Clone, Debug, Deref)]
pub struct CoupledEdgeData<InputNode, OutputNode>(Vec<HyperEdge<InputNode, OutputNode>>);

impl<InputNode: Eq + Hash, OutputNode: Eq + Hash> CoupledEdgeData<InputNode, OutputNode> {
    pub fn into_hash_set(self) -> HashSet<HyperEdge<InputNode, OutputNode>> {
        self.0.into_iter().collect()
    }
}

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub enum CouplingError<'tcx> {
    CannotConstructShape { edges: Vec<AbstractionEdge<'tcx>> },
}

struct CoupleInputError;

impl<InputNode: Eq + Hash + Copy, OutputNode: Eq + Hash + Copy>
    CoupledEdgeData<InputNode, OutputNode>
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
    fn new(
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

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct CoupledEdges<Metadata, InputNode, OutputNode> {
    metadata: Metadata,
    edges: CoupledEdgeData<InputNode, OutputNode>,
}

pub type FunctionCoupledEdges<'tcx> = CoupledEdges<
    FunctionCallAbstractionEdgeMetadata<'tcx>,
    FunctionCallAbstractionInput<'tcx>,
    FunctionCallAbstractionOutput<'tcx>,
>;

pub type LoopCoupledEdges<'tcx> = CoupledEdges<
    LoopAbstractionEdgeMetadata<'tcx>,
    LoopAbstractionInput<'tcx>,
    LoopAbstractionOutput<'tcx>,
>;

pub type PcgCoupledEdge<'tcx> = FunctionCallOrLoop<
    HyperEdge<FunctionCallAbstractionInput<'tcx>, FunctionCallAbstractionOutput<'tcx>>,
    HyperEdge<LoopAbstractionInput<'tcx>, LoopAbstractionOutput<'tcx>>,
>;

impl<'tcx> PcgCoupledEdge<'tcx> {
    pub fn inputs<C: Copy>(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> Vec<AbstractionInputTarget<'tcx>> {
        match self {
            PcgCoupledEdge::FunctionCall(function) => function
                .inputs()
                .iter()
                .map(|input| AbstractionInputTarget((*input).to_pcg_node(ctxt)))
                .collect(),
            PcgCoupledEdge::Loop(loop_) => loop_
                .inputs()
                .iter()
                .map(|input| AbstractionInputTarget((*input).into()))
                .collect(),
        }
    }

    pub fn outputs(&self) -> Vec<AbstractionOutputTarget<'tcx>> {
        match self {
            PcgCoupledEdge::FunctionCall(function) => function
                .outputs()
                .iter()
                .map(|output| AbstractionOutputTarget((**output).into()))
                .collect(),
            PcgCoupledEdge::Loop(loop_) => loop_
                .outputs()
                .iter()
                .map(|output| AbstractionOutputTarget(**output))
                .collect(),
        }
    }
}

pub type PcgCoupledEdges<'tcx> =
    FunctionCallOrLoop<FunctionCoupledEdges<'tcx>, LoopCoupledEdges<'tcx>>;

impl<'tcx> PcgCoupledEdges<'tcx> {
    pub fn edges(&self) -> HashSet<PcgCoupledEdge<'tcx>> {
        fn for_function_call<'tcx>(
            data: FunctionCoupledEdges<'tcx>,
        ) -> HashSet<PcgCoupledEdge<'tcx>> {
            data.edges
                .0
                .into_iter()
                .map(PcgCoupledEdge::FunctionCall)
                .collect()
        }
        fn for_loop<'tcx>(data: LoopCoupledEdges<'tcx>) -> HashSet<PcgCoupledEdge<'tcx>> {
            data.edges.0.into_iter().map(PcgCoupledEdge::Loop).collect()
        }
        self.clone().bimap(for_function_call, for_loop)
    }
}

impl<'tcx> BorrowsGraph<'tcx> {
    /// Returns the set of successful coupling results based on the abstraction
    /// edges in the graph.  If you are also interested in the unsuccessful
    /// couplings, use [`BorrowsGraph::coupling_results`].
    pub fn coupled_edges(&self) -> HashSet<PcgCoupledEdge<'tcx>> {
        self.coupling_results()
            .into_iter()
            .flat_map(|result| {
                let set = match result {
                    Ok(result) => result.edges(),
                    Err(_) => HashSet::default(),
                };
                set.into_iter()
            })
            .collect()
    }
    pub fn coupling_results(&self) -> HashSet<Result<PcgCoupledEdges<'tcx>, CouplingError<'tcx>>> {
        let mut function_edges: HashMap<
            FunctionCallAbstractionEdgeMetadata<'tcx>,
            HashSet<FunctionCallAbstractionEdge<'tcx>>,
        > = HashMap::default();
        let mut loop_edges: HashMap<
            LoopAbstractionEdgeMetadata<'tcx>,
            HashSet<LoopAbstractionEdge<'tcx>>,
        > = HashMap::default();
        for edge in self.edges() {
            match edge.kind() {
                BorrowPcgEdgeKind::Abstraction(AbstractionEdge::FunctionCall(function_call)) => {
                    function_edges
                        .entry(function_call.metadata)
                        .or_default()
                        .insert(function_call.edge.clone());
                }
                BorrowPcgEdgeKind::Abstraction(AbstractionEdge::Loop(loop_abstraction)) => {
                    loop_edges
                        .entry(loop_abstraction.metadata)
                        .or_default()
                        .insert(loop_abstraction.edge.clone());
                }
                _ => {}
            }
        }
        let mut result = function_edges
            .into_iter()
            .map(|(metadata, edges)| couple_edges(metadata, edges, PcgCoupledEdges::FunctionCall))
            .collect::<HashSet<_>>();
        result.extend(
            loop_edges
                .into_iter()
                .map(|(metadata, edges)| couple_edges(metadata, edges, PcgCoupledEdges::Loop)),
        );
        result
    }
}

fn couple_edges<'tcx, Metadata: Copy, InputNode: Eq + Hash + Copy, OutputNode: Eq + Hash + Copy>(
    metadata: Metadata,
    edges: HashSet<AbstractionBlockEdge<'tcx, InputNode, OutputNode>>,
    f: impl FnOnce(CoupledEdges<Metadata, InputNode, OutputNode>) -> PcgCoupledEdges<'tcx>,
) -> Result<PcgCoupledEdges<'tcx>, CouplingError<'tcx>>
where
    AbstractionBlockEdgeWithMetadata<Metadata, AbstractionBlockEdge<'tcx, InputNode, OutputNode>>:
        Into<AbstractionEdge<'tcx>>,
{
    match CoupledEdgeData::new(edges.clone()) {
        Ok(coupled_edges) => Ok(f(CoupledEdges {
            metadata,
            edges: coupled_edges,
        })),
        Err(_) => Err(CouplingError::CannotConstructShape {
            edges: edges
                .into_iter()
                .map(|edge| edge.with_metadata(metadata).into())
                .collect(),
        }),
    }
}
