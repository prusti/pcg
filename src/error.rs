use derive_more::From;

use crate::{
    borrow_pcg::MakeFunctionShapeError,
    coupling::CoupleInputError,
    rustc_interface::middle::{mir, ty},
    utils::{
        self, PANIC_ON_ERROR, Place,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
    },
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PcgError<'tcx> {
    pub(crate) kind: PcgErrorKind<'tcx>,
    pub(crate) context: Vec<String>,
}

impl<'tcx, Ctxt> DisplayWithCtxt<Ctxt> for PcgError<'tcx>
where
    PcgErrorKind<'tcx>: DisplayWithCtxt<Ctxt>,
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match mode {
            OutputMode::Test => format!(
                "PcgError {{ kind: {}, context: {:?} }}",
                self.kind.test_string(ctxt),
                self.context
            )
            .into(),
            _ => format!("{self:?}").into(),
        }
    }
}

impl<'tcx> From<PcgUnsupportedError<'tcx>> for PcgError<'tcx> {
    fn from(e: PcgUnsupportedError<'tcx>) -> Self {
        Self::new(PcgErrorKind::Unsupported(e), vec![])
    }
}

impl<'tcx> PcgError<'tcx> {
    pub(crate) fn new(kind: PcgErrorKind<'tcx>, context: Vec<String>) -> Self {
        assert!(
            !*PANIC_ON_ERROR,
            "PCG Error: {:?} ({})",
            kind,
            context.join(", ")
        );
        Self { kind, context }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PcgErrorKind<'tcx> {
    Unsupported(PcgUnsupportedError<'tcx>),
    Internal(PcgInternalError<'tcx>),
}

impl<'a, 'tcx: 'a, Ctxt: crate::utils::HasCompilerCtxt<'a, 'tcx> + Copy> DisplayWithCtxt<Ctxt>
    for PcgErrorKind<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match mode {
            OutputMode::Test => match self {
                PcgErrorKind::Unsupported(pcg_unsupported_error) => {
                    format!("Unsupported({})", pcg_unsupported_error.test_string(ctxt)).into()
                }
                PcgErrorKind::Internal(pcg_internal_error) => {
                    format!("Internal({})", pcg_internal_error.test_string(ctxt)).into()
                }
            },
            _ => format!("{self:?}").into(),
        }
    }
}

impl<'tcx> PcgError<'tcx> {
    pub(crate) fn internal(err: PcgInternalError<'tcx>) -> Self {
        Self {
            kind: PcgErrorKind::Internal(err),
            context: vec![],
        }
    }


    pub(crate) fn unsupported(err: PcgUnsupportedError<'tcx>) -> Self {
        Self {
            kind: PcgErrorKind::Unsupported(err),
            context: vec![],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PcgInternalError<'tcx> {
    MakeFunctionShapeError(MakeFunctionShapeError<'tcx>),
    NoCapability(Place<'tcx>, mir::Location),
    Other(String),
}

impl<'tcx> PcgInternalError<'tcx> {
    pub(crate) fn new(msg: String) -> Self {
        Self::Other(msg)
    }
}

impl<'a, 'tcx: 'a, Ctxt: crate::utils::HasCompilerCtxt<'a, 'tcx> + Copy> DisplayWithCtxt<Ctxt>
    for PcgInternalError<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        match self {
            PcgInternalError::NoCapability(place, location) => format!(
                "NoCapability({}, {:?})",
                place.display_string(ctxt),
                location
            )
            .into(),
            PcgInternalError::Other(msg) => format!("Other({msg})").into(),
            PcgInternalError::MakeFunctionShapeError(make_function_shape_error) => {
                format!("{:?}", make_function_shape_error).into()
            }
        }
    }
}

impl<'tcx> From<PcgInternalError<'tcx>> for PcgError<'tcx> {
    fn from(e: PcgInternalError<'tcx>) -> Self {
        PcgError::new(PcgErrorKind::Internal(e), vec![])
    }
}

#[derive(Debug, Clone, PartialEq, Eq, From)]
pub struct PlaceContainingPtrWithNestedLifetime<'tcx> {
    pub(crate) place: utils::Place<'tcx>,
    pub(crate) invalid_ty_chain: Vec<ty::Ty<'tcx>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PcgUnsupportedError<'tcx> {
    AssignBorrowToNonReferenceType,
    DerefUnsafePtr,
    MoveUnsafePtrWithNestedLifetime(PlaceContainingPtrWithNestedLifetime<'tcx>),
    ExpansionOfAliasType,
    CallWithUnsafePtrWithNestedLifetime(PlaceContainingPtrWithNestedLifetime<'tcx>),
    IndexingNonIndexableType,
    InlineAssembly,
    MaxNodesExceeded,
    Coupling(CoupleInputError),
}

impl<Ctxt> DisplayWithCtxt<Ctxt> for PcgUnsupportedError<'_> {
    fn display_output(&self, _ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match mode {
            OutputMode::Test => match self {
                PcgUnsupportedError::MoveUnsafePtrWithNestedLifetime(_) => {
                    "MoveUnsafePtrWithNestedLifetime".into()
                }
                PcgUnsupportedError::CallWithUnsafePtrWithNestedLifetime(_) => {
                    "CallWithUnsafePtrWithNestedLifetime".into()
                }
                _ => format!("{self:?}").into(),
            },
            _ => format!("{self:?}").into(),
        }
    }
}
