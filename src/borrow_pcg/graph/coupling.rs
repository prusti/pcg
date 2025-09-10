use crate::{
    borrow_pcg::{
        domain::{
            FunctionCallAbstractionInput, FunctionCallAbstractionOutput, LoopAbstractionInput,
            LoopAbstractionOutput,
        },
        edge::{abstraction::function::FunctionData, kind::BorrowPcgEdgeKind},
        graph::BorrowsGraph,
    },
    rustc_interface::middle::mir::Location,
    utils::data_structures::{HashMap, HashSet},
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
}

pub struct CoupledEdgeData<InputNode, OutputNode>(HashSet<HyperEdge<InputNode, OutputNode>>);

pub struct CouplingError;

impl<InputNode: Eq + Hash, OutputNode: Eq + Hash> CoupledEdgeData<InputNode, OutputNode> {
    fn try_couple_input(
        input: InputNode,
        inputs: &HashSet<InputNode>,
        outputs_map: &HashMap<InputNode, HashSet<OutputNode>>,
    ) -> Result<HyperEdge<InputNode, OutputNode>, CouplingError> {
        let expected_outputs = &outputs_map[&input];
        if expected_outputs.is_empty() {
            return Err(CouplingError);
        }
        let mut other_inputs_in_edge = Vec::new();
        for other_input in inputs {
            if other_input == input {
                continue;
            }
        }
    }
    pub fn new(edges: Vec<(InputNode, OutputNode)>) -> Result<Self, CouplingError> {
        let mut inputs = HashSet::default();
        let mut outputs_map: HashMap<InputNode, HashSet<OutputNode>> = HashMap::default();
        for (input, output) in edges {
            inputs.insert(input);
            outputs_map.entry(input).or_default().insert(output);
        }
        Ok(Self(HashSet::from_iter(
            edges
                .into_iter()
                .map(|(input, output)| HyperEdge { inputs, outputs }),
        )))
    }
}

pub struct FunctionCoupledEdges<'tcx> {
    location: Location,
    function_data: Option<FunctionData<'tcx>>,
    edges: CoupledEdgeData<FunctionCallAbstractionInput<'tcx>, FunctionCallAbstractionOutput<'tcx>>,
}

pub struct LoopCoupledEdges<'tcx> {
    location: Location,
    edges: CoupledEdgeData<LoopAbstractionInput<'tcx>, LoopAbstractionOutput<'tcx>>,
}

pub enum CoupledEdge<'tcx> {
    Function(FunctionCoupledEdges<'tcx>),
    Loop(LoopCoupledEdges<'tcx>),
}

impl<'tcx> BorrowsGraph<'tcx> {
    pub fn coupled_edges<'slf>(&'slf self) -> HashSet<CoupledEdge<'tcx>> {
        self.edges()
            .filter_map(|edge| match edge.kind() {
                BorrowPcgEdgeKind::Abstraction(at) => Some(at),
                _ => None,
            })
            .collect()
    }
}
