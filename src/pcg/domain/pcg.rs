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
    owned_pcg::{RepackOp, join::data::JoinOwnedData},
    pcg::{
        CapabilityKind,
        ctxt::{AnalysisCtxt, HasSettings},
        owned_state::OwnedPcg,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesReader},
        triple::Triple,
    },
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, DataflowCtxt, DebugImgcat, HasBorrowCheckerCtxt, Place,
        data_structures::HashSet, display::DisplayWithCompilerCtxt, maybe_old::MaybeLabelledPlace,
        validity::HasValidityCheck,
    },
};

#[cfg(feature = "visualization")]
use crate::visualization::{dot_graph::DotGraph, generate_pcg_dot_graph};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pcg<
    'a,
    'tcx,
    Capabilities = PlaceCapabilities<'tcx>,
    EdgeKind: Eq + std::hash::Hash + PartialEq = BorrowPcgEdgeKind<'tcx>,
> {
    pub(crate) borrow: BorrowsState<'a, 'tcx, EdgeKind>,

    /// Capabilities for all places in the PCG.
    /// TODO[capability-refactor]: This map will be removed, ultimately capabilities should be
    /// computed based on the initialisation tree in the Owned PCG and the `BorrowState`
    pub(crate) place_capabilities: Capabilities,
    pub(crate) owned: OwnedPcg<'tcx>,
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
    pub(crate) borrow: BorrowStateRef<'pcg, 'tcx>,
    pub(crate) place_capabilities: &'pcg PlaceCapabilities<'tcx>,
    pub(crate) owned: &'pcg OwnedPcg<'tcx>,
}

impl<'tcx> PcgRef<'_, 'tcx> {
    #[cfg(feature = "visualization")]
    pub(crate) fn render_debug_graph<'slf, 'a>(
        &'slf self,
        location: mir::Location,
        debug_imgcat: Option<DebugImgcat>,
        comment: &str,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) {
        if borrows_imgcat_debug(location.block, debug_imgcat) {
            let dot_graph = generate_pcg_dot_graph(self.as_ref(), ctxt, location).unwrap();
            DotGraph::render_with_imgcat(&dot_graph, comment).unwrap_or_else(|e| {
                eprintln!("Error rendering self graph: {e}");
            });
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg Pcg<'_, 'tcx>> for PcgRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg Pcg<'_, 'tcx>) -> Self {
        Self {
            borrow: pcg.borrow.as_ref(),
            place_capabilities: &pcg.place_capabilities,
            owned: &pcg.owned,
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg PcgMutRef<'pcg, 'tcx>> for PcgRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg PcgMutRef<'pcg, 'tcx>) -> Self {
        let borrow = pcg.borrow.as_ref();
        Self {
            borrow,
            place_capabilities: &*pcg.place_capabilities,
            owned: &*pcg.owned,
        }
    }
}

pub(crate) struct PcgMutRef<'pcg, 'tcx> {
    pub(crate) borrow: BorrowStateMutRef<'pcg, 'tcx>,
    pub(crate) place_capabilities: &'pcg mut PlaceCapabilities<'tcx>,
    pub(crate) owned: &'pcg mut OwnedPcg<'tcx>,
}

impl<'pcg, 'tcx> PcgMutRef<'pcg, 'tcx> {
    pub(crate) fn new(
        borrow: BorrowStateMutRef<'pcg, 'tcx>,
        place_capabilities: &'pcg mut PlaceCapabilities<'tcx>,
        owned: &'pcg mut OwnedPcg<'tcx>,
    ) -> Self {
        Self {
            borrow,
            place_capabilities,
            owned,
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg mut Pcg<'_, 'tcx>> for PcgMutRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg mut Pcg<'_, 'tcx>) -> Self {
        Self::new(
            (&mut pcg.borrow).into(),
            &mut pcg.place_capabilities,
            &mut pcg.owned,
        )
    }
}

pub(crate) trait PcgRefLike<'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx>;

    fn borrows_graph(&self) -> &BorrowsGraph<'tcx> {
        self.as_ref().borrow.graph
    }

    fn place_capability_equals<'b>(
        &self,
        place: Place<'tcx>,
        capability: CapabilityKind,
        ctxt: impl HasBorrowCheckerCtxt<'b, 'tcx>,
    ) -> bool
    where
        'tcx: 'b,
    {
        self.capability_of(place, ctxt)
            .is_some_and(|c| c == capability)
    }

    // TODO[capability-refactor]: This method will be removed, ultimately capabilities will be
    // computed based on the initialisation tree in the Owned PCG and the BorrowState.
    fn capability_of<'b>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'b, 'tcx>,
    ) -> Option<CapabilityKind>
    where
        'tcx: 'b,
    {
        self.as_ref().place_capabilities.get(place, ctxt)
    }

    fn is_acyclic(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.borrows_graph().frozen_graph().is_acyclic(ctxt)
    }

    fn owned(&self) -> &OwnedPcg<'tcx> {
        self.as_ref().owned
    }

    fn leaf_places<'a>(&self, ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        let borrows_places = self.borrows_graph().places(ctxt.bc_ctxt());
        let mut leaf_places: HashSet<Place<'tcx>> = self
            .owned()
            .leaf_places(ctxt)
            .into_iter()
            .map(Into::into)
            .filter(|p| !borrows_places.contains(p))
            .collect();
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
        self.place_capabilities.check_validity(ctxt)?;
        self.borrow.check_validity(ctxt.bc_ctxt())?;
        self.owned
            .check_validity(self.place_capabilities, ctxt.bc_ctxt())?;

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

        for (place, cap) in self.place_capabilities.iter() {
            if !self.owned.contains_place(place, ctxt.bc_ctxt())
                && !self.borrow.graph.places(ctxt.bc_ctxt()).contains(&place)
            {
                return Err(format!(
                    "Place {} has capability {:?} but is not in the owned PCG or borrow graph",
                    place.display_string(ctxt.bc_ctxt()),
                    cap
                ));
            }
        }

        for edge in self.borrow.graph.edges() {
            match edge.kind {
                BorrowPcgEdgeKind::Deref(deref_edge) => {
                    if let MaybeLabelledPlace::Current(blocked_place) = deref_edge.blocked_place
                        && let MaybeLabelledPlace::Current(deref_place) = deref_edge.deref_place
                        && let Some(c @ (CapabilityKind::Read | CapabilityKind::Exclusive)) =
                            self.place_capabilities.get(blocked_place, ctxt)
                        && self.place_capabilities.get(deref_place, ctxt).is_none()
                    {
                        return Err(format!(
                            "Deref edge {} blocked place {} has capability {:?} but deref place {} has no capability",
                            deref_edge.display_string(ctxt.bc_ctxt()),
                            blocked_place.display_string(ctxt.bc_ctxt()),
                            c,
                            deref_place.display_string(ctxt.bc_ctxt())
                        ));
                    }
                }
                BorrowPcgEdgeKind::Borrow(borrow_edge) => {
                    if let MaybeLabelledPlace::Current(blocked_place) = borrow_edge.blocked_place
                        && blocked_place.as_owned_place(ctxt).is_some()
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

        match place.as_owned_place(ctxt) {
            Some(owned) => self.owned.leaf_places(ctxt).contains(&owned),
            None => true,
        }
    }

    #[must_use]
    pub fn places_with_capapability(&self, capability: CapabilityKind) -> HashSet<Place<'tcx>> {
        self.place_capabilities
            .iter()
            .filter_map(|(p, c)| if c == capability { Some(p) } else { None })
            .collect()
    }

    #[must_use]
    pub fn capabilities(&self) -> &PlaceCapabilities<'tcx> {
        &self.place_capabilities
    }

    pub(crate) fn borrow_created_at(&self, location: mir::Location) -> Option<&BorrowEdge<'tcx>> {
        self.borrow.graph().borrow_created_at(location)
    }

    #[must_use]
    pub fn borrow_pcg(&self) -> &BorrowsState<'a, 'tcx> {
        &self.borrow
    }

    pub(crate) fn ensure_triple<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>>(
        &mut self,
        t: Triple<'tcx>,
        ctxt: Ctxt,
    ) {
        self.owned.ensures(t, &mut self.place_capabilities, ctxt);
    }

    /// Compute the [`CapabilityKind`] of the owned place `place` from
    /// the initialisation tree alone (i.e. ignoring borrowing). See
    /// <https://prusti.github.io/pcg-docs/computing-place-capabilities.html>.
    #[must_use]
    pub fn computed_owned_capability<'b>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'b, 'tcx>,
    ) -> Option<CapabilityKind>
    where
        'tcx: 'b,
    {
        let owned = place.as_owned_place(ctxt)?;
        self.owned.owned_capability(owned)
    }

    // Unified capability lookup `capability_of` is provided as a
    // default method on [`PcgRefLike`] — see that trait's definition.

    /// View the maintained per-local owned-PCG state.
    #[must_use]
    pub fn owned(&self) -> &OwnedPcg<'tcx> {
        &self.owned
    }

    pub(crate) fn join_owned_data(
        &mut self,
        block: mir::BasicBlock,
    ) -> JoinOwnedData<'a, '_, 'tcx, &mut OwnedPcg<'tcx>> {
        JoinOwnedData {
            owned: &mut self.owned,
            borrows: &mut self.borrow,
            capabilities: &mut self.place_capabilities,
            block,
        }
    }

    pub(crate) fn bridge(
        &self,
        other: &Self,
        self_block: mir::BasicBlock,
        other_block: mir::BasicBlock,
        ctxt: impl DataflowCtxt<'a, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>> {
        let mut slf = self.clone();
        let mut other = other.clone();
        let mut slf_owned_data = slf.join_owned_data(self_block);
        let other_owned_data = JoinOwnedData {
            owned: &other.owned,
            borrows: &mut other.borrow,
            capabilities: &mut other.place_capabilities,
            block: other_block,
        };
        let mut repacks =
            slf_owned_data.join(other_owned_data, ctxt.compiler_ctxt_with_settings())?;
        for (place, cap) in slf.place_capabilities.iter() {
            let Some(_owned) = place.as_owned_place(ctxt) else {
                continue;
            };
            if let Some(other_cap) = other.place_capabilities.get(place, ctxt)
                && cap > other_cap
            {
                repacks.push(RepackOp::Weaken(Weaken::new(place, cap, other_cap)));
            }
        }
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
        let mut other_capabilities = other.place_capabilities.clone();
        let mut other_borrows = other.borrow.clone();
        let mut self_owned_data = self.join_owned_data(self_block);
        let other_owned_data = JoinOwnedData {
            owned: &other.owned,
            borrows: &mut other_borrows,
            capabilities: &mut other_capabilities,
            block: other_block,
        };
        let repack_ops =
            self_owned_data.join(other_owned_data, ctxt.compiler_ctxt_with_settings())?;
        // For edges in the other graph that actually belong to it,
        // add the path condition that leads them to this block
        let mut other = other.clone();
        other.borrow.add_cfg_edge(other_block, self_block, ctxt);
        self.place_capabilities.join(&other_capabilities, ctxt);
        self.owned.join_capabilities(&other.owned);
        let borrow_args = JoinBorrowsArgs {
            self_block,
            other_block,
            body_analysis: ctxt.body_analysis,
            capabilities: &mut self.place_capabilities,
            owned: &mut self.owned,
        };
        self.borrow.join(&other_borrows, borrow_args, ctxt)?;
        Ok(repack_ops)
    }

    pub(crate) fn debug_lines<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>>(
        &self,
        ctxt: Ctxt,
    ) -> Vec<Cow<'static, str>> {
        let mut result = self.borrow.debug_lines(ctxt);
        result.sort();
        let mut capabilities = self.place_capabilities.debug_lines(ctxt);
        capabilities.sort();
        result.extend(capabilities);
        result
    }
}

impl<'a, 'tcx: 'a> Pcg<'a, 'tcx> {
    pub(crate) fn start_block(analysis_ctxt: AnalysisCtxt<'a, 'tcx>) -> Self {
        let mut capabilities: PlaceCapabilities<'tcx> = PlaceCapabilities::default();
        let owned = OwnedPcg::start_block(&mut capabilities, analysis_ctxt);
        let borrow = BorrowsState::start_block(&mut capabilities, analysis_ctxt);
        Pcg {
            borrow,
            place_capabilities: capabilities,
            owned,
        }
    }
}
