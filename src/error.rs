use derive_more::From;

use crate::{coupling::CoupleInputError, utils::PANIC_ON_ERROR};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PcgError {
    pub(crate) kind: PcgErrorKind,
    pub(crate) context: Vec<String>,
}

// Deprecated: use PcgError instead
pub type PCGError = PcgError;

impl From<PcgUnsupportedError> for PcgError {
    fn from(e: PcgUnsupportedError) -> Self {
        Self::new(PcgErrorKind::Unsupported(e), vec![])
    }
}

impl PcgError {
    pub(crate) fn new(kind: PcgErrorKind, context: Vec<String>) -> Self {
        if *PANIC_ON_ERROR {
            panic!("PCG Error: {:?} ({})", kind, context.join(", "));
        }
        Self { kind, context }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PcgErrorKind {
    Unsupported(PcgUnsupportedError),
    Internal(PcgInternalError),
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

impl From<PcgInternalError> for PcgError {
    fn from(e: PcgInternalError) -> Self {
        PcgError::new(PcgErrorKind::Internal(e), vec![])
    }
}

#[derive(Debug, Clone, PartialEq, Eq, From)]
pub enum PcgUnsupportedError {
    AssignBorrowToNonReferenceType,
    DerefUnsafePtr,
    MoveUnsafePtrWithNestedLifetime,
    ExpansionOfAliasType,
    CallWithUnsafePtrWithNestedLifetime,
    IndexingNonIndexableType,
    InlineAssembly,
    MaxNodesExceeded,
    Coupling(CoupleInputError),
}
