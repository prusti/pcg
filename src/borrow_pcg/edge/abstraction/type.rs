use std::marker::PhantomData;

use crate::borrow_pcg::{
    domain::{AbstractionInputTarget, AbstractionOutputTarget, FunctionCallAbstractionOutput},
    edge::abstraction::{AbstractionBlockEdge, AbstractionInputLike, AbstractionType},
};
use crate::pcg::PcgNode;
use crate::rustc_interface::middle::mir::Location;

impl<'tcx> AbstractionType<'tcx> {
    pub fn location(&self) -> Location {
        match self {
            AbstractionType::FunctionCall(c) => c.location(),
            AbstractionType::Loop(c) => c.location(),
        }
    }

    pub fn input(&self) -> AbstractionInputTarget<'tcx> {
        self.edge().input()
    }

    pub fn output(&self) -> AbstractionOutputTarget<'tcx> {
        self.edge().output()
    }

    pub fn edge(
        &self,
    ) -> AbstractionBlockEdge<'tcx, AbstractionInputTarget<'tcx>, AbstractionOutputTarget<'tcx>>
    {
        match self {
            AbstractionType::FunctionCall(c) => AbstractionBlockEdge {
                _phantom: PhantomData,
                input: c.edge().input().to_abstraction_input(),
                output: c.edge().output().into(),
            },
            AbstractionType::Loop(c) => AbstractionBlockEdge {
                _phantom: PhantomData,
                input: c.edge.input().to_abstraction_input(),
                output: c.edge.output().to_abstraction_output(),
            },
        }
    }
}

impl<'tcx> From<FunctionCallAbstractionOutput<'tcx>> for AbstractionOutputTarget<'tcx> {
    fn from(value: FunctionCallAbstractionOutput<'tcx>) -> Self {
        AbstractionOutputTarget(PcgNode::LifetimeProjection(*value))
    }
}
