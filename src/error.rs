use derive_more::From;

use crate::{
    coupling::CoupleInputError,
    rustc_interface::middle::ty,
    utils::{
        self, PANIC_ON_ERROR,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
    },
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PcgError {
    pub(crate) kind: PcgErrorKind,
    pub(crate) context: Vec<String>,
}

impl<Ctxt> DisplayWithCtxt<Ctxt> for PcgError
where
    PcgErrorKind: DisplayWithCtxt<Ctxt>,
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

impl From<PcgUnsupportedError> for PcgError {
    fn from(e: PcgUnsupportedError) -> Self {
        Self::new(PcgErrorKind::Unsupported(e), vec![])
    }
}

impl PcgError {
    pub(crate) fn new(kind: PcgErrorKind, context: Vec<String>) -> Self {
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
pub enum PcgErrorKind {
    Unsupported(PcgUnsupportedError),
    Internal(PcgInternalError),
}

impl<Ctxt> DisplayWithCtxt<Ctxt> for PcgErrorKind {
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

impl PcgError {
    #[allow(dead_code)]
    pub(crate) fn internal(msg: String) -> Self {
        Self {
            kind: PcgErrorKind::Internal(PcgInternalError::new(msg)),
            context: vec![],
        }
    }

    pub(crate) fn unsupported(err: PcgUnsupportedError) -> Self {
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

impl From<PcgInternalError> for PcgError {
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
pub enum PcgUnsupportedError {
    AssignBorrowToNonReferenceType,
    ExpansionOfAliasType,
    IndexingNonIndexableType,
    InlineAssembly,
    MaxNodesExceeded,
    Coupling(CoupleInputError),
}

impl<Ctxt> DisplayWithCtxt<Ctxt> for PcgUnsupportedError {
    fn display_output(&self, _ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        format!("{self:?}").into()
    }
}
