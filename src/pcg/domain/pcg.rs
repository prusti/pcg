use std::borrow::Cow;

use crate::{
    DebugLines, Weaken,
    borrow_pcg::{
        edge::{borrow::BorrowEdge, kind::BorrowPcgEdgeKind},
        graph::{BorrowsGraph, join::JoinBorrowsArgs},
        state::{BorrowStateMutRef, BorrowStateRef, BorrowsState, BorrowsStateLike},
    },
    borrows_imgcat_debug,
    error::PcgError,
    owned_pcg::{OwnedPcg, RepackOp, join::data::JoinOwnedData},
    pcg::{
        CapabilityKind, CapabilityLike, PositiveCapability, SymbolicCapability,
        ctxt::{AnalysisCtxt, HasSettings},
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesReader},
        triple::Triple,
    },
    pcg_validity_assert, pcg_validity_expect_some,
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, DebugCtxt, DebugImgcat, HasBorrowCheckerCtxt, HasCompilerCtxt, Place,
        PlaceLike, data_structures::HashSet, display::DisplayWithCompilerCtxt,
        maybe_old::MaybeLabelledPlace, validity::HasValidityCheck,
    },
};

#[cfg(feature = "visualization")]
use crate::visualization::{dot_graph::DotGraph, generate_pcg_dot_graph};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pcg<'a, 'tcx, EdgeKind: Eq + std::hash::Hash + PartialEq = BorrowPcgEdgeKind<'tcx>> {
    pub(crate) owned: OwnedPcg<'tcx>,
    pub(crate) borrow: BorrowsState<'a, 'tcx, EdgeKind>,
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx> + DebugCtxt> PlaceCapabilitiesReader<'tcx, Ctxt>
    for Pcg<'a, 'tcx>
{
    fn get(&self, place: Place<'tcx>, ctxt: Ctxt) -> CapabilityKind {
        self.owned.capability(place, &self.borrow.graph, ctxt)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasSettings<'a> + HasBorrowCheckerCtxt<'a, 'tcx>> HasValidityCheck<Ctxt>
    for Pcg<'a, 'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> std::result::Result<(), String> {
        self.as_ref().check_validity(ctxt)
    }
}

#[derive(Clone, Copy)]
pub struct PcgRef<'pcg, 'tcx> {
    pub(crate) owned: &'pcg OwnedPcg<'tcx>,
    pub(crate) borrow: BorrowStateRef<'pcg, 'tcx>,
}

impl<'pcg, 'tcx: 'a, 'a, Ctxt: HasCompilerCtxt<'a, 'tcx> + DebugCtxt>
    PlaceCapabilitiesReader<'tcx, Ctxt> for PcgRef<'pcg, 'tcx>
{
    fn get(&self, place: Place<'tcx>, ctxt: Ctxt) -> CapabilityKind {
        self.owned.capability(place, self.borrow.graph, ctxt)
    }
}

impl<'pcg, 'tcx> PcgRef<'pcg, 'tcx> {
    pub(crate) fn new(owned: &'pcg OwnedPcg<'tcx>, borrow: BorrowStateRef<'pcg, 'tcx>) -> Self {
        Self { owned, borrow }
    }

    #[cfg(feature = "visualization")]
    pub(crate) fn render_debug_graph<'a: 'pcg>(
        self,
        location: mir::Location,
        debug_imgcat: Option<DebugImgcat>,
        comment: &str,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
    ) where
        'tcx: 'a,
    {
        if borrows_imgcat_debug(location.block, debug_imgcat, ctxt.settings()) {
            let dot_graph = generate_pcg_dot_graph(self, ctxt, Some(location)).unwrap();
            DotGraph::render_with_imgcat(&dot_graph, comment).unwrap_or_else(|e| {
                eprintln!("Error rendering self graph: {e}");
            });
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg Pcg<'_, 'tcx>> for PcgRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg Pcg<'_, 'tcx>) -> Self {
        Self {
            owned: &pcg.owned,
            borrow: pcg.borrow.as_ref(),
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg PcgMutRef<'pcg, 'tcx>> for PcgRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg PcgMutRef<'pcg, 'tcx>) -> Self {
        let borrow = pcg.borrow.as_ref();
        Self {
            owned: &*pcg.owned,
            borrow,
        }
    }
}

pub(crate) struct PcgMutRef<'pcg, 'tcx> {
    pub(crate) owned: &'pcg mut OwnedPcg<'tcx>,
    pub(crate) borrow: BorrowStateMutRef<'pcg, 'tcx>,
}

impl<'pcg, 'tcx> PcgMutRef<'pcg, 'tcx> {
    pub(crate) fn new(
        owned: &'pcg mut OwnedPcg<'tcx>,
        borrow: BorrowStateMutRef<'pcg, 'tcx>,
    ) -> Self {
        Self { owned, borrow }
    }
}

impl<'pcg, 'tcx> From<&'pcg mut Pcg<'_, 'tcx>> for PcgMutRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg mut Pcg<'_, 'tcx>) -> Self {
        Self::new(&mut pcg.owned, (&mut pcg.borrow).into())
    }
}

pub(crate) trait PcgRefLike<'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx>;

    fn borrows_graph(&self) -> &BorrowsGraph<'tcx> {
        self.as_ref().borrow.graph
    }

    fn place_capability_equals<'a>(
        &self,
        place: Place<'tcx>,
        capability: impl Into<CapabilityKind>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx> + DebugCtxt,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.owned_pcg()
            .capability(place, self.borrows_graph(), ctxt)
            == capability.into()
    }

    fn expect_positive_capability<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx> + DebugCtxt,
    ) -> PositiveCapability
    where
        'tcx: 'a,
    {
        pcg_validity_expect_some!(
            self.as_ref()
                .owned_pcg()
                .capability(place, self.borrows_graph(), ctxt)
                .into_positive(),
            fallback: PositiveCapability::Exclusive,
            [ctxt],
            "Expected positive capability for place {} but got none",
            place.display_string(ctxt)
        )
    }

    fn is_acyclic(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.borrows_graph().frozen_graph().is_acyclic(ctxt)
    }

    fn owned_pcg(&self) -> &OwnedPcg<'tcx> {
        self.as_ref().owned
    }

    fn leaf_places<'a>(&self, ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        let mut leaf_places = self.owned_pcg().leaf_places(ctxt);
        leaf_places.retain(|p| !self.borrows_graph().places(ctxt.bc_ctxt()).contains(p));
        leaf_places.extend(self.borrows_graph().leaf_places(ctxt));
        leaf_places
    }

    fn is_leaf_place<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.leaf_places(ctxt).contains(&place)
    }
}

impl<'tcx> PcgRefLike<'tcx> for PcgMutRef<'_, 'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx> {
        PcgRef::from(self)
    }
}

impl<'tcx> PcgRefLike<'tcx> for Pcg<'_, 'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx> {
        PcgRef::from(self)
    }
}

impl<'tcx> PcgRefLike<'tcx> for PcgRef<'_, 'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx> {
        *self
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasSettings<'a> + HasBorrowCheckerCtxt<'a, 'tcx>> HasValidityCheck<Ctxt>
    for PcgRef<'_, 'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> std::result::Result<(), String> {
        self.borrow.check_validity(ctxt.bc_ctxt())?;
        self.owned_pcg()
            .check_validity(self.borrow.graph, ctxt.bc_ctxt())?;

        if ctxt.settings().check_cycles && !self.is_acyclic(ctxt.bc_ctxt()) {
            return Err("PCG is not acyclic".to_owned());
        }

        for local in self.owned.unallocated_locals() {
            if self.borrow.graph.contains(local, ctxt) {
                return Err(format!(
                    "Unallocated local {} is in the borrow graph",
                    local.display_string(ctxt)
                ));
            }
        }

        // For now we don't do this, due to interactions with future nodes: we
        // detect that a node is no longer blocked but still technically not a
        // leaf due to previous reborrows that could have changed the value in
        // its lifetime projections. See format_fields in tracing-subscriber
        //
        // In the future we might want to change how this works
        //
        // let leaf_places = self.leaf_places(ctxt);
        // for place in self.places(ctxt) {
        //     if self.capabilities.get(place, ctxt) == Some(CapabilityKind::Exclusive)
        //         && !leaf_places.contains(&place)
        //     {
        //         return Err(format!(
        //             "Place {} has exclusive capability but is not a leaf place",
        //             place.display_string(ctxt)
        //         ));
        //     }
        // }

        for edge in self.borrow.graph.edges() {
            match edge.kind {
                BorrowPcgEdgeKind::Deref(deref_edge) => {}
                BorrowPcgEdgeKind::Borrow(borrow_edge) => {
                    if let MaybeLabelledPlace::Current(blocked_place) = borrow_edge.blocked_place
                        && blocked_place.is_owned(ctxt)
                        && !self.owned.contains_place(blocked_place, ctxt.bc_ctxt())
                    {
                        return Err(format!(
                            "Borrow edge {} blocks owned place {}, which is not in the owned PCG",
                            borrow_edge.display_string(ctxt.bc_ctxt()),
                            blocked_place.display_string(ctxt.bc_ctxt())
                        ));
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }
}

impl<'a, 'tcx: 'a> Pcg<'a, 'tcx> {
    pub(crate) fn is_expansion_leaf(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool {
        if self
            .borrow
            .graph()
            .edges_blocking(place.into(), ctxt.bc_ctxt())
            .any(|e| matches!(e.kind, BorrowPcgEdgeKind::BorrowPcgExpansion(_)))
        {
            return false;
        }

        return !place.is_owned(ctxt) || self.owned.leaf_places(ctxt).contains(&place);
    }

    #[must_use]
    pub fn owned_pcg(&self) -> &OwnedPcg<'tcx> {
        &self.owned
    }

    pub(crate) fn borrow_created_at(&self, location: mir::Location) -> Option<&BorrowEdge<'tcx>> {
        self.borrow.graph().borrow_created_at(location)
    }

    #[must_use]
    pub fn borrow_pcg(&self) -> &BorrowsState<'a, 'tcx> {
        &self.borrow
    }

    pub(crate) fn ensure_triple<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        t: Triple<'tcx>,
        ctxt: Ctxt,
    ) {
        self.owned.ensures(t, &self.borrow.graph(), ctxt);
    }

    pub(crate) fn join_owned_data(
        &mut self,
        block: mir::BasicBlock,
    ) -> JoinOwnedData<'a, '_, 'tcx, &mut OwnedPcg<'tcx>> {
        JoinOwnedData {
            owned: &mut self.owned,
            borrows: &mut self.borrow,
            block,
        }
    }

    #[tracing::instrument(skip(self, other, ctxt), fields(self.block = ?self_block, other.block = ?other_block), level = "warn")]
    pub(crate) fn bridge(
        &self,
        other: &Self,
        self_block: mir::BasicBlock,
        other_block: mir::BasicBlock,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>> {
        let mut slf = self.clone();
        let mut other = other.clone();
        let mut slf_owned_data = slf.join_owned_data(self_block);
        let other_owned_data = JoinOwnedData {
            owned: &other.owned,
            borrows: &mut other.borrow,
            block: other_block,
        };
        let repacks = slf_owned_data.join(other_owned_data, ctxt)?;
        tracing::warn!("self: {}", self.owned_pcg().display_string(ctxt));
        tracing::warn!("other: {}", other.owned_pcg().display_string(ctxt));
        tracing::warn!("repacks: {}", repacks.display_string(ctxt));
        Ok(repacks)
    }

    #[tracing::instrument(skip(self, other, ctxt))]
    pub(crate) fn join(
        &mut self,
        other: &Self,
        self_block: mir::BasicBlock,
        other_block: mir::BasicBlock,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>> {
        let mut other_borrows = other.borrow.clone();
        let mut self_owned_data = self.join_owned_data(self_block);
        let other_owned_data = JoinOwnedData {
            owned: &other.owned,
            borrows: &mut other_borrows,
            block: other_block,
        };
        let repack_ops = self_owned_data.join(other_owned_data, ctxt)?;
        // For edges in the other graph that actually belong to it,
        // add the path condition that leads them to this block
        let mut other = other.clone();
        other.borrow.add_cfg_edge(other_block, self_block, ctxt);
        let borrow_args = JoinBorrowsArgs {
            self_block,
            other_block,
            body_analysis: ctxt.body_analysis,
            owned: &mut self.owned,
        };
        self.borrow.join(&other_borrows, borrow_args, ctxt)?;
        Ok(repack_ops)
    }

    fn places(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>> {
        let mut result = self.borrow.graph().places(ctxt);
        result.extend(self.owned.places(ctxt));
        result
    }

    pub(crate) fn debug_lines(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Vec<Cow<'static, str>> {
        let mut result = self.borrow.debug_lines(ctxt);
        for place in self.places(ctxt) {
            result.push(Cow::Owned(format!(
                "{}: {:?}",
                place.display_string(ctxt),
                self.owned.capability(place, &self.borrow.graph(), ctxt)
            )));
        }
        result.sort();
        result
    }
}

impl<'a, 'tcx: 'a> Pcg<'a, 'tcx, BorrowPcgEdgeKind<'tcx>> {
    pub(crate) fn start_block(analysis_ctxt: AnalysisCtxt<'a, 'tcx>) -> Self {
        let owned = OwnedPcg::start_block(analysis_ctxt);
        let borrow = BorrowsState::start_block(analysis_ctxt);
        Pcg { owned, borrow }
    }
}
