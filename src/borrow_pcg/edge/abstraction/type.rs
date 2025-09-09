use std::marker::PhantomData;

use crate::pcg::PcgNode;
use crate::rustc_interface::middle::mir::Location;
use crate::{
    borrow_pcg::{
        domain::{AbstractionInputTarget, AbstractionOutputTarget, FunctionCallAbstractionOutput},
        edge::abstraction::{AbstractionBlockEdge, AbstractionInputLike, AbstractionType},
    },
    utils::CompilerCtxt,
};

impl<'tcx> AbstractionType<'tcx> {
    pub fn location(&self) -> Location {
        match self {
            AbstractionType::FunctionCall(c) => c.location(),
            AbstractionType::Loop(c) => c.location(),
        }
    }

    pub fn input<C: Copy>(&self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> AbstractionInputTarget<'tcx> {
        self.edge(ctxt).input()
    }

    pub fn output<C: Copy>(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> AbstractionOutputTarget<'tcx> {
        self.edge(ctxt).output()
    }

    pub fn edge<C: Copy>(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> AbstractionBlockEdge<'tcx, AbstractionInputTarget<'tcx>, AbstractionOutputTarget<'tcx>>
    {
        match self {
            AbstractionType::FunctionCall(c) => AbstractionBlockEdge {
                _phantom: PhantomData,
                input: c.edge().input().to_abstraction_input(ctxt),
                output: c.edge().output().into(),
            },
            AbstractionType::Loop(c) => AbstractionBlockEdge {
                _phantom: PhantomData,
                input: c.edge.input().to_abstraction_input(ctxt),
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
