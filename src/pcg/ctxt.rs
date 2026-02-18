use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::validity_conditions::effective_successors,
    pcg::{
        BodyAnalysis, CapabilityConstraint, CapabilityRule, CapabilityRules, CapabilityVar, Choice,
        IntroduceConstraints, PcgArena, PositiveCapability, SymbolicCapability,
        SymbolicCapabilityCtxt, place_capabilities::PlaceCapabilitiesReader,
    },
    rustc_interface::middle::{mir, ty},
    utils::{
        CompilerCtxt, DataflowCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasTyCtxt, PcgSettings,
        Place, SnapshotLocation, data_structures::HashMap, logging::LogPredicate,
    },
};

impl<'a, 'tcx: 'a> std::fmt::Debug for AnalysisCtxt<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AnalysisCtxt {{ block: {:?} }}", self.block)
    }
}

impl<'a, 'tcx: 'a> HasSettings<'a> for AnalysisCtxt<'a, 'tcx> {
    fn settings(&self) -> &'a PcgSettings {
        self.settings
    }
}

impl<'a, 'tcx: 'a> DataflowCtxt<'a, 'tcx> for AnalysisCtxt<'a, 'tcx> {
    fn try_into_analysis_ctxt(self) -> Option<AnalysisCtxt<'a, 'tcx>> {
        Some(self)
    }
}

pub trait HasSettings<'a> {
    fn settings(&self) -> &'a PcgSettings;
}

mod private {
    use crate::{
        borrow_pcg::region_projection::OverrideRegionDebugString,
        pcg::{BodyAnalysis, PcgArena, SymbolicCapabilityCtxt},
        rustc_interface::{
            RustBitSet,
            middle::{mir, ty},
        },
        utils::{CompilerCtxt, DebugCtxt, HasLocals, PcgSettings},
    };

    #[derive(Copy, Clone)]
    pub struct AnalysisCtxt<'a, 'tcx> {
        pub(crate) ctxt: CompilerCtxt<'a, 'tcx>,
        pub(crate) body_analysis: &'a BodyAnalysis<'a, 'tcx>,
        pub(crate) settings: &'a PcgSettings,
        #[allow(dead_code)]
        pub(crate) symbolic_capability_ctxt: SymbolicCapabilityCtxt<'a, 'tcx>,
        pub(crate) block: mir::BasicBlock,
        pub(crate) arena: PcgArena<'a>,
        #[cfg(feature = "visualization")]
        pub(crate) visualization_data:
            Option<crate::visualization::stmt_graphs::AnalysisDebugData<'a>>,
    }

    impl<'a, 'tcx: 'a> OverrideRegionDebugString for AnalysisCtxt<'a, 'tcx> {
        fn override_region_debug_string(&self, region: ty::RegionVid) -> Option<&str> {
            self.ctxt
                .borrow_checker
                .override_region_debug_string(region)
        }
    }

    impl<'a, 'tcx: 'a> DebugCtxt for AnalysisCtxt<'a, 'tcx> {
        fn func_name(&self) -> String {
            self.ctxt.func_name()
        }
        fn num_basic_blocks(&self) -> usize {
            self.ctxt.num_basic_blocks()
        }
    }

    impl<'a, 'tcx: 'a> HasLocals for AnalysisCtxt<'a, 'tcx> {
        fn always_live_locals(self) -> RustBitSet<mir::Local> {
            self.ctxt.always_live_locals()
        }
        fn arg_count(self) -> usize {
            self.ctxt.body().arg_count
        }
        fn local_count(self) -> usize {
            self.ctxt.local_count()
        }
    }
}

pub use private::*;

impl<'a, 'tcx: 'a> HasTyCtxt<'tcx> for AnalysisCtxt<'a, 'tcx> {
    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.ctxt.tcx
    }
}

impl<'a, 'tcx: 'a> AnalysisCtxt<'a, 'tcx> {
    pub(crate) fn should_join_from(&self, other: mir::BasicBlock) -> bool {
        effective_successors(other, self.body()).contains(&self.block)
            && !self.ctxt.is_back_edge(other, self.block)
    }
}

impl<'a, 'tcx> HasCompilerCtxt<'a, 'tcx> for AnalysisCtxt<'a, 'tcx> {
    fn ctxt(self) -> CompilerCtxt<'a, 'tcx, ()> {
        self.ctxt.ctxt()
    }
}

impl<'a, 'tcx> HasBorrowCheckerCtxt<'a, 'tcx> for AnalysisCtxt<'a, 'tcx> {
    fn bc(&self) -> &'a dyn BorrowCheckerInterface<'tcx> {
        self.ctxt.borrow_checker()
    }

    fn bc_ctxt(&self) -> CompilerCtxt<'a, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>> {
        self.ctxt
    }
}

impl<'a, 'tcx> AnalysisCtxt<'a, 'tcx> {
    pub(crate) fn body(&self) -> &'a mir::Body<'tcx> {
        self.ctxt.body()
    }
    pub(crate) fn new(
        ctxt: CompilerCtxt<'a, 'tcx>,
        block: mir::BasicBlock,
        body_analysis: &'a BodyAnalysis<'a, 'tcx>,
        symbolic_capability_ctxt: SymbolicCapabilityCtxt<'a, 'tcx>,
        arena: PcgArena<'a>,
        settings: &'a PcgSettings,
        #[cfg(feature = "visualization")] graphs: Option<
            crate::visualization::stmt_graphs::AnalysisDebugData<'a>,
        >,
    ) -> Self {
        Self {
            ctxt,
            body_analysis,
            settings,
            symbolic_capability_ctxt,
            block,
            arena,
            #[cfg(feature = "visualization")]
            visualization_data: graphs,
        }
    }
    pub(crate) fn matches(&self, predicate: &LogPredicate) -> bool {
        match predicate {
            LogPredicate::DebugBlock => {
                if let Some(debug_block) = self.settings.debug_block {
                    debug_block == self.block
                } else {
                    false
                }
            }
        }
    }
}
