use std::borrow::Cow;
#[cfg(feature = "visualization")]
use std::cell::RefCell;

#[cfg(feature = "visualization")]
use crate::visualization;
use crate::{
    BodyAndBorrows, HasSettings,
    borrow_checker::{BorrowCheckerInterface, r#impl::NllBorrowCheckerImpl},
    borrow_pcg::region_projection::OverrideRegionDebugString,
    rustc_interface::{
        middle::{
            mir::Body,
            ty::{self, TyCtxt},
        },
        mir_dataflow::move_paths::MoveData,
        span::def_id::LocalDefId,
    },
    utils::{
        CompilerCtxt, DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasTyCtxt, PcgSettings,
    },
};

pub struct PcgCtxt<'a, 'tcx> {
    pub(crate) compiler_ctxt: CompilerCtxt<'a, 'tcx>,
    pub(crate) move_data: MoveData<'tcx>,
    pub(crate) settings: Cow<'a, PcgSettings>,
    pub(crate) arena: bumpalo::Bump,
}

impl<'a, 'mir: 'a, 'tcx: 'mir> OverrideRegionDebugString for &'a PcgCtxt<'mir, 'tcx> {
    fn override_region_debug_string(&self, region: ty::RegionVid) -> Option<&str> {
        self.compiler_ctxt
            .borrow_checker
            .override_region_debug_string(region)
    }
}

impl<'a, 'mir: 'a, 'tcx: 'mir>
    HasBorrowCheckerCtxt<'mir, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for &'a PcgCtxt<'mir, 'tcx>
{
    fn bc_ctxt(&self) -> CompilerCtxt<'mir, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>> {
        self.compiler_ctxt.as_dyn()
    }

    fn bc(&self) -> &'a dyn BorrowCheckerInterface<'tcx> {
        self.compiler_ctxt.borrow_checker()
    }
}

impl DebugCtxt for &PcgCtxt<'_, '_> {
    fn func_name(&self) -> String {
        self.compiler_ctxt.func_name()
    }
    fn num_basic_blocks(&self) -> usize {
        self.compiler_ctxt.num_basic_blocks()
    }
}

impl<'mir, 'tcx> HasCompilerCtxt<'mir, 'tcx> for &PcgCtxt<'mir, 'tcx> {
    fn ctxt(self) -> CompilerCtxt<'mir, 'tcx, ()> {
        CompilerCtxt::new(self.compiler_ctxt.mir, self.compiler_ctxt.tcx, ())
    }
}

impl<'tcx> HasTyCtxt<'tcx> for &PcgCtxt<'_, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.compiler_ctxt.tcx
    }
}

impl<'a> HasSettings<'a> for &'a PcgCtxt<'_, '_> {
    fn settings(&self) -> &'a PcgSettings {
        &self.settings
    }
}

pub struct PcgCtxtCreator<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    arena: bumpalo::Bump,
    pub(crate) settings: PcgSettings,
    #[cfg(feature = "visualization")]
    pub(crate) debug_function_metadata: RefCell<crate::visualization::FunctionsMetadata>,
}

impl<'tcx> PcgCtxtCreator<'tcx> {
    pub fn settings(&self) -> &PcgSettings {
        &self.settings
    }

    #[must_use]
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self::with_settings(tcx, PcgSettings::new())
    }

    #[must_use]
    pub fn with_settings(tcx: TyCtxt<'tcx>, settings: PcgSettings) -> Self {
        Self {
            tcx,
            arena: bumpalo::Bump::new(),
            settings,
            #[cfg(feature = "visualization")]
            debug_function_metadata: RefCell::new(visualization::FunctionsMetadata::new()),
        }
    }

    fn alloc<'a, T: 'a>(&'a self, val: T) -> &'a T {
        self.arena.alloc(val)
    }

    pub fn new_ctxt<'slf: 'a, 'a>(
        &'slf self,
        body: &'a impl BodyAndBorrows<'tcx>,
        bc: &'a impl BorrowCheckerInterface<'tcx>,
    ) -> &'a PcgCtxt<'a, 'tcx> {
        let pcg_ctxt: PcgCtxt<'a, 'tcx> =
            PcgCtxt::with_settings(body.body(), self.tcx, bc, Cow::Borrowed(&self.settings));
        #[cfg(feature = "visualization")]
        if let Some(identifier) = pcg_ctxt.visualization_function_metadata() {
            self.debug_function_metadata
                .borrow_mut()
                .insert(pcg_ctxt.compiler_ctxt.function_metadata_slug(), identifier);
        }
        self.alloc(pcg_ctxt)
    }

    pub fn new_nll_ctxt<'slf: 'a, 'a>(
        &'slf self,
        body: &'a impl BodyAndBorrows<'tcx>,
    ) -> &'a PcgCtxt<'a, 'tcx> {
        let bc = self.arena.alloc(NllBorrowCheckerImpl::new(self.tcx, body));
        self.new_ctxt(body, bc)
    }
}

impl<'a, 'tcx> PcgCtxt<'a, 'tcx> {
    pub fn new<BC: BorrowCheckerInterface<'tcx> + ?Sized>(
        body: &'a Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        bc: &'a BC,
    ) -> Self {
        Self::with_settings(body, tcx, bc, Cow::Owned(PcgSettings::new()))
    }

    pub fn with_settings<BC: BorrowCheckerInterface<'tcx> + ?Sized>(
        body: &'a Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        bc: &'a BC,
        settings: Cow<'a, PcgSettings>,
    ) -> Self {
        let ctxt = CompilerCtxt::new(body, tcx, bc.as_dyn());
        Self {
            compiler_ctxt: ctxt,
            move_data: gather_moves(ctxt.body(), ctxt.tcx()),
            settings,
            arena: bumpalo::Bump::new(),
        }
    }

    pub fn body_def_id(&self) -> LocalDefId {
        self.compiler_ctxt.def_id()
    }
}

fn gather_moves<'tcx>(body: &Body<'tcx>, tcx: ty::TyCtxt<'tcx>) -> MoveData<'tcx> {
    MoveData::gather_moves(body, tcx, |_| true)
}
