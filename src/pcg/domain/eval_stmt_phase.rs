use serde_derive::Serialize;

#[derive(PartialEq, Eq, Copy, Clone, Debug, Ord, PartialOrd, Hash, Serialize)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
pub enum EvalStmtPhase {
    #[cfg_attr(feature = "type-export", serde(rename = "pre_operands"))]
    PreOperands,
    #[cfg_attr(feature = "type-export", serde(rename = "post_operands"))]
    PostOperands,
    #[cfg_attr(feature = "type-export", serde(rename = "pre_main"))]
    PreMain,
    #[cfg_attr(feature = "type-export", serde(rename = "post_main"))]
    PostMain,
}

impl EvalStmtPhase {
    pub(crate) const fn first() -> Self {
        EvalStmtPhase::PreOperands
    }

    pub const fn last() -> Self {
        EvalStmtPhase::PostMain
    }
}

impl EvalStmtPhase {
    pub fn is_operands_stage(&self) -> bool {
        matches!(
            self,
            EvalStmtPhase::PreOperands | EvalStmtPhase::PostOperands
        )
    }

    pub fn phases() -> [EvalStmtPhase; 4] {
        [
            EvalStmtPhase::PreOperands,
            EvalStmtPhase::PostOperands,
            EvalStmtPhase::PreMain,
            EvalStmtPhase::PostMain,
        ]
    }

    pub(crate) fn next(&self) -> Option<EvalStmtPhase> {
        match self {
            EvalStmtPhase::PreOperands => Some(EvalStmtPhase::PostOperands),
            EvalStmtPhase::PostOperands => Some(EvalStmtPhase::PreMain),
            EvalStmtPhase::PreMain => Some(EvalStmtPhase::PostMain),
            EvalStmtPhase::PostMain => None,
        }
    }
}

impl std::fmt::Display for EvalStmtPhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvalStmtPhase::PreOperands => write!(f, "pre_operands"),
            EvalStmtPhase::PostOperands => write!(f, "post_operands"),
            EvalStmtPhase::PreMain => write!(f, "pre_main"),
            EvalStmtPhase::PostMain => write!(f, "post_main"),
        }
    }
}
