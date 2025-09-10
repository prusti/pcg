use serde_json::json;

use super::{CompilerCtxt, Place, display::DisplayWithCompilerCtxt, validity::HasValidityCheck};
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        region_projection::{
            HasTy, PcgLifetimeProjectionBase, PcgLifetimeProjectionBaseLike, PlaceOrConst,
        },
    },
    pcg::{EvalStmtPhase, LocalNodeLike, PcgNode, PcgNodeLike},
    rustc_interface::middle::{
        mir::{self, BasicBlock, Location},
        ty,
    },
    utils::{HasCompilerCtxt, json::ToJsonWithCompilerCtxt},
};

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy, Ord, PartialOrd)]
pub struct AnalysisLocation {
    pub(crate) location: Location,
    pub(crate) eval_stmt_phase: EvalStmtPhase,
}

impl std::fmt::Display for AnalysisLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}:{:?}", self.location, self.eval_stmt_phase)
    }
}

impl AnalysisLocation {
    pub fn location(&self) -> Location {
        self.location
    }

    pub fn first(block: BasicBlock) -> Self {
        AnalysisLocation {
            location: Location {
                block,
                statement_index: 0,
            },
            eval_stmt_phase: EvalStmtPhase::first(),
        }
    }

    pub fn new(location: Location, eval_stmt_phase: EvalStmtPhase) -> Self {
        AnalysisLocation {
            location,
            eval_stmt_phase,
        }
    }
    pub fn next_snapshot_location(self, body: &mir::Body<'_>) -> SnapshotLocation {
        if let Some(phase) = self.eval_stmt_phase.next() {
            SnapshotLocation::Before(AnalysisLocation {
                location: self.location,
                eval_stmt_phase: phase,
            })
        } else {
            let bb = &body.basic_blocks[self.location.block];
            // Not < because the PCG also has a location for the terminator
            if self.location.statement_index == bb.statements.len() {
                SnapshotLocation::After(self.location.block)
            } else {
                let mut next_location = self.location;
                next_location.statement_index += 1;
                SnapshotLocation::Before(AnalysisLocation {
                    location: next_location,
                    eval_stmt_phase: EvalStmtPhase::first(),
                })
            }
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub enum SnapshotLocation {
    Before(AnalysisLocation),
    After(BasicBlock),
    Loop(BasicBlock),
    BeforeJoin(BasicBlock),
    BeforeRefReassignment(Location),
}

impl SnapshotLocation {
    pub fn location(self) -> Location {
        match self {
            SnapshotLocation::Before(analysis_location) => analysis_location.location(),
            SnapshotLocation::After(block) => Location {
                block,
                statement_index: 0,
            },
            SnapshotLocation::Loop(block) => Location {
                block,
                statement_index: 0,
            },
            SnapshotLocation::BeforeJoin(block) => Location {
                block,
                statement_index: 0,
            },
            SnapshotLocation::BeforeRefReassignment(location) => location,
        }
    }
    pub fn before_block(block: BasicBlock) -> Self {
        SnapshotLocation::Before(AnalysisLocation {
            location: Location {
                block,
                statement_index: 0,
            },
            eval_stmt_phase: EvalStmtPhase::first(),
        })
    }

    pub const fn first() -> Self {
        SnapshotLocation::Before(AnalysisLocation {
            location: Location::START,
            eval_stmt_phase: EvalStmtPhase::first(),
        })
    }

    pub fn after_statement_at<'a, 'tcx: 'a>(
        location: Location,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self {
        let analysis_location = AnalysisLocation {
            location,
            eval_stmt_phase: EvalStmtPhase::last(),
        };
        analysis_location.next_snapshot_location(ctxt.body())
    }

    pub(crate) fn before(analysis_location: AnalysisLocation) -> Self {
        SnapshotLocation::Before(analysis_location)
    }

    pub(crate) fn to_json(self) -> serde_json::Value {
        self.to_string().into()
    }
}

#[deprecated(note = "Use LabelledPlace instead")]
pub type PlaceSnapshot<'tcx> = LabelledPlace<'tcx>;

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub struct LabelledPlace<'tcx> {
    pub(crate) place: Place<'tcx>,
    pub(crate) at: SnapshotLocation,
}

impl<'tcx> HasTy<'tcx> for LabelledPlace<'tcx> {
    fn rust_ty<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> ty::Ty<'tcx>
    where
        'tcx: 'a,
    {
        self.place.ty(ctxt).ty
    }
}

impl std::fmt::Display for SnapshotLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SnapshotLocation::After(loc) => write!(f, "after {loc:?}"),
            SnapshotLocation::Loop(bb) => write!(f, "loop {bb:?}"),
            SnapshotLocation::BeforeJoin(bb) => write!(f, "before join {bb:?}"),
            SnapshotLocation::BeforeRefReassignment(location) => {
                write!(f, "before ref reassignment {location:?}")
            }
            SnapshotLocation::Before(eval_stmt_phase) => write!(f, "before {eval_stmt_phase}"),
        }
    }
}

impl<'tcx> PcgLifetimeProjectionBaseLike<'tcx> for LabelledPlace<'tcx> {
    fn to_pcg_lifetime_projection_base(&self) -> PcgLifetimeProjectionBase<'tcx> {
        PlaceOrConst::Place((*self).into())
    }
}

impl<'tcx> PcgNodeLike<'tcx> for LabelledPlace<'tcx> {
    fn to_pcg_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.to_local_node(repacker).into()
    }
}

impl<'tcx> LocalNodeLike<'tcx> for LabelledPlace<'tcx> {
    fn to_local_node<C: Copy>(self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::Place(self.into())
    }
}

impl<'tcx> HasValidityCheck<'tcx> for LabelledPlace<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.place.check_validity(ctxt)
    }
}

impl std::fmt::Display for LabelledPlace<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} at {:?}", self.place, self.at)
    }
}

impl<'tcx, BC: Copy> DisplayWithCompilerCtxt<'tcx, BC> for LabelledPlace<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> String {
        format!("{} at {:?}", self.place.to_short_string(repacker), self.at)
    }
}

impl<'tcx, BC: Copy> ToJsonWithCompilerCtxt<'tcx, BC> for LabelledPlace<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        json!({
            "place": self.place.to_json(repacker),
            "at": self.at.to_json(),
        })
    }
}

impl<'tcx> LabelledPlace<'tcx> {
    pub fn new<T: Into<SnapshotLocation>>(place: Place<'tcx>, at: T) -> Self {
        LabelledPlace {
            place,
            at: at.into(),
        }
    }

    pub fn place(&self) -> Place<'tcx> {
        self.place
    }

    pub fn at(&self) -> SnapshotLocation {
        self.at
    }

    pub(crate) fn with_inherent_region<'a>(
        &self,
        repacker: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> LabelledPlace<'tcx>
    where
        'tcx: 'a,
    {
        LabelledPlace {
            place: self.place.with_inherent_region(repacker),
            at: self.at,
        }
    }
}
