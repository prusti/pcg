use derive_more::From;

use crate::{
    coupling::CoupleInputError,
    rustc_interface::{middle::ty, span::Span},
    utils::{
        self, PANIC_ON_ERROR,
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
    Internal(PcgInternalError),
}

impl<Ctxt> DisplayWithCtxt<Ctxt> for PcgErrorKind<'_> {
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
    #[allow(dead_code)]
    pub(crate) fn internal(msg: String) -> Self {
        Self {
            kind: PcgErrorKind::Internal(PcgInternalError::new(msg)),
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
pub struct PcgInternalError(String);

impl PcgInternalError {
    pub(crate) fn new(msg: String) -> Self {
        Self(msg)
    }
}

impl<Ctxt> DisplayWithCtxt<Ctxt> for PcgInternalError {
    fn display_output(&self, _ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        format!("{self:?}").into()
    }
}

impl From<PcgInternalError> for PcgError<'_> {
    fn from(e: PcgInternalError) -> Self {
        PcgError::new(PcgErrorKind::Internal(e), vec![])
    }
}

#[derive(Debug, Clone, PartialEq, Eq, From)]
pub struct PlaceContainingPtrWithNestedLifetime<'tcx> {
    pub(crate) place: utils::Place<'tcx>,
    pub(crate) invalid_ty_chain: Vec<ty::Ty<'tcx>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallWithUnsafePtrWithNestedLifetime<'tcx> {
    pub(crate) function: String,
    pub(crate) span: Span,
    pub(crate) place: PlaceContainingPtrWithNestedLifetime<'tcx>,
}

#[derive(Debug, Clone, PartialEq, Eq, From)]
pub enum PcgUnsupportedError<'tcx> {
    AssignBorrowToNonReferenceType,
    DerefUnsafePtr,
    MoveUnsafePtrWithNestedLifetime(PlaceContainingPtrWithNestedLifetime<'tcx>),
    ExpansionOfAliasType,
    CallWithUnsafePtrWithNestedLifetime(CallWithUnsafePtrWithNestedLifetime<'tcx>),
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
