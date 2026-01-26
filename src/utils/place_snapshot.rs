use std::{borrow::Cow, marker::PhantomData};

use serde_json::json;

use super::{Place, validity::HasValidityCheck};
use crate::{
    borrow_pcg::{borrow_pcg_edge::LocalNode, region_projection::HasTy},
    pcg::{EvalStmtPhase, LocalNodeLike},
    rustc_interface::middle::{
        mir::{self, BasicBlock, Location},
        ty,
    },
    utils::{
        DebugCtxt, HasCompilerCtxt, PcgNodeComponent, PlaceProjectable,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        json::ToJsonWithCtxt,
    },
};

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy, Ord, PartialOrd)]
pub struct AnalysisLocation {
    pub(crate) location: Location,
    pub(crate) eval_stmt_phase: EvalStmtPhase,
}

impl DisplayWithCtxt<()> for Location {
    fn display_output(&self, _ctxt: (), _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(format!("{self:?}").into())
    }
}

impl std::fmt::Display for AnalysisLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}:{:?}", self.location, self.eval_stmt_phase)
    }
}

impl DisplayWithCtxt<()> for AnalysisLocation {
    fn display_output(&self, ctxt: (), mode: OutputMode) -> DisplayOutput {
        match mode {
            OutputMode::Short => self.location.display_output(ctxt, mode),
            OutputMode::Normal | OutputMode::Test => DisplayOutput::Seq(vec![
                self.location.display_output(ctxt, mode),
                DisplayOutput::Text(Cow::Borrowed(":")),
                self.eval_stmt_phase.display_output(ctxt, mode),
            ]),
        }
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

impl std::fmt::Display for SnapshotLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", DisplayWithCtxt::<_>::display_string(self, ()))
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub struct LabelledPlace<'tcx, P = Place<'tcx>> {
    pub(crate) place: P,
    pub(crate) at: SnapshotLocation,
    _marker: PhantomData<&'tcx ()>,
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> HasTy<'tcx, Ctxt> for LabelledPlace<'tcx> {
    fn rust_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.place.ty(ctxt).ty
    }
}

impl DisplayWithCtxt<()> for SnapshotLocation {
    fn display_output(&self, ctxt: (), mode: OutputMode) -> DisplayOutput {
        match self {
            SnapshotLocation::Before(analysis_location) => DisplayOutput::Seq(vec![
                DisplayOutput::Text(Cow::Borrowed("before ")),
                analysis_location.display_output(ctxt, mode),
            ]),
            SnapshotLocation::After(loc) => DisplayOutput::Text(format!("after {loc:?}").into()),
            SnapshotLocation::Loop(bb) => DisplayOutput::Text(format!("loop {bb:?}").into()),
            SnapshotLocation::BeforeJoin(bb) => {
                DisplayOutput::Text(format!("before join {bb:?}").into())
            }
            SnapshotLocation::BeforeRefReassignment(location) => {
                DisplayOutput::Text(format!("before ref reassignment {location:?}").into())
            }
        }
    }
}

impl<'tcx, Ctxt: Copy, P: PlaceProjectable<'tcx, Ctxt> + PcgNodeComponent>
    PlaceProjectable<'tcx, Ctxt> for LabelledPlace<'tcx, P>
{
    fn project_deeper(
        &self,
        elem: mir::PlaceElem<'tcx>,
        ctxt: Ctxt,
    ) -> std::result::Result<Self, crate::error::PcgError> {
        Ok(LabelledPlace::new(
            self.place.project_deeper(elem, ctxt)?,
            self.at,
        ))
    }

    fn iter_projections(&self, _ctxt: Ctxt) -> Vec<(Self, mir::PlaceElem<'tcx>)> {
        todo!()
    }
}

impl<'tcx, Ctxt> LocalNodeLike<'tcx, Ctxt> for LabelledPlace<'tcx> {
    fn to_local_node(self, _ctxt: Ctxt) -> LocalNode<'tcx> {
        LocalNode::Place(self.into())
    }
}

impl<'a, 'tcx: 'a, Ctxt: DebugCtxt + HasCompilerCtxt<'a, 'tcx>> HasValidityCheck<Ctxt>
    for LabelledPlace<'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        self.place.check_validity(ctxt)
    }
}

impl std::fmt::Display for LabelledPlace<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} at {:?}", self.place, self.at)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for LabelledPlace<'tcx> {
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Seq(vec![
            self.place.display_output(ctxt, mode),
            DisplayOutput::Text(format!(" at {:?}", self.at).into()),
        ])
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt> for LabelledPlace<'tcx> {
    fn to_json(&self, ctxt: Ctxt) -> serde_json::Value {
        json!({
            "place": self.place.to_json(ctxt.ctxt()),
            "at": self.at.to_json(),
        })
    }
}

impl<'tcx, P: PcgNodeComponent> LabelledPlace<'tcx, P> {
    pub fn new<T: Into<SnapshotLocation>>(place: P, at: T) -> Self {
        LabelledPlace {
            place,
            at: at.into(),
            _marker: PhantomData,
        }
    }

    pub fn place(&self) -> P {
        self.place
    }

    pub fn at(&self) -> SnapshotLocation {
        self.at
    }
}

impl<'tcx> LabelledPlace<'tcx> {
    pub(crate) fn with_inherent_region<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> LabelledPlace<'tcx>
    where
        'tcx: 'a,
    {
        LabelledPlace::new(self.place.with_inherent_region(ctxt), self.at)
    }
}
