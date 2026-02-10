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
        CapabilityKind, CapabilityLike, SymbolicCapability,
        ctxt::{AnalysisCtxt, HasSettings},
        place_capabilities::{
            PlaceCapabilities, PlaceCapabilitiesReader, SymbolicPlaceCapabilities,
        },
        triple::Triple,
    },
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, DebugImgcat, HasBorrowCheckerCtxt, Place, PlaceLike,
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
    Capabilities = SymbolicPlaceCapabilities<'tcx>,
    EdgeKind: Eq + std::hash::Hash + PartialEq = BorrowPcgEdgeKind<'tcx>,
> {
    pub(crate) owned: OwnedPcg<'tcx>,
    pub(crate) borrow: BorrowsState<'a, 'tcx, EdgeKind>,
    pub(crate) capabilities: Capabilities,
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
    pub(crate) capabilities: &'pcg SymbolicPlaceCapabilities<'tcx>,
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
            owned: &pcg.owned,
            borrow: pcg.borrow.as_ref(),
            capabilities: &pcg.capabilities,
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg PcgMutRef<'pcg, 'tcx>> for PcgRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg PcgMutRef<'pcg, 'tcx>) -> Self {
        let borrow = pcg.borrow.as_ref();
        Self {
            owned: &*pcg.owned,
            borrow,
            capabilities: &*pcg.capabilities,
        }
    }
}

pub(crate) struct PcgMutRef<'pcg, 'tcx> {
    pub(crate) owned: &'pcg mut OwnedPcg<'tcx>,
    pub(crate) borrow: BorrowStateMutRef<'pcg, 'tcx>,
    pub(crate) capabilities: &'pcg mut SymbolicPlaceCapabilities<'tcx>,
}

impl<'pcg, 'tcx> PcgMutRef<'pcg, 'tcx> {
    pub(crate) fn new(
        owned: &'pcg mut OwnedPcg<'tcx>,
        borrow: BorrowStateMutRef<'pcg, 'tcx>,
        capabilities: &'pcg mut SymbolicPlaceCapabilities<'tcx>,
    ) -> Self {
        Self {
            owned,
            borrow,
            capabilities,
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg mut Pcg<'_, 'tcx>> for PcgMutRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg mut Pcg<'_, 'tcx>) -> Self {
        Self::new(
            &mut pcg.owned,
            (&mut pcg.borrow).into(),
            &mut pcg.capabilities,
        )
    }
}

pub(crate) trait PcgRefLike<'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx>;

    fn borrows_graph(&self) -> &BorrowsGraph<'tcx> {
        self.as_ref().borrow.graph
    }

    fn place_capability_equals(
        &self,
        place: Place<'tcx>,
        capability: impl Into<SymbolicCapability>,
    ) -> bool {
        self.as_ref()
            .capabilities
            .get(place, ())
            .is_some_and(|c| c == capability.into())
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
        self.capabilities
            .to_concrete(ctxt)
            .check_validity(ctxt.bc_ctxt())?;
        self.borrow.check_validity(ctxt.bc_ctxt())?;
        self.owned
            .check_validity(&self.capabilities.to_concrete(ctxt), ctxt.bc_ctxt())?;

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

        for (place, cap) in self.capabilities.to_concrete(ctxt).iter() {
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
                BorrowPcgEdgeKind::Deref(deref_edge) => {
                    if let MaybeLabelledPlace::Current(blocked_place) = deref_edge.blocked_place
                        && let MaybeLabelledPlace::Current(deref_place) = deref_edge.deref_place
                        && let Some(c @ (CapabilityKind::Read | CapabilityKind::Exclusive)) = self
                            .capabilities
                            .get(blocked_place, ctxt)
                            .map(super::super::capabilities::SymbolicCapability::expect_concrete)
                        && self.capabilities.get(deref_place, ctxt).is_none()
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
    pub fn places_with_capapability(&self, capability: CapabilityKind) -> HashSet<Place<'tcx>> {
        self.capabilities
            .iter()
            .filter_map(|(p, c)| {
                if c == capability.into() {
                    Some(p)
                } else {
                    None
                }
            })
            .collect()
    }

    #[must_use]
    pub fn capabilities(&self) -> &SymbolicPlaceCapabilities<'tcx> {
        &self.capabilities
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
        self.owned.ensures(t, &mut self.capabilities, ctxt);
    }

    pub(crate) fn join_owned_data(
        &mut self,
        block: mir::BasicBlock,
    ) -> JoinOwnedData<'a, '_, 'tcx, &mut OwnedPcg<'tcx>> {
        JoinOwnedData {
            owned: &mut self.owned,
            borrows: &mut self.borrow,
            capabilities: &mut self.capabilities,
            block,
        }
    }

    pub(crate) fn bridge(
        &self,
        other: &Self,
        self_block: mir::BasicBlock,
        other_block: mir::BasicBlock,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError<'tcx>> {
        let mut slf = self.clone();
        let mut other = other.clone();
        let mut slf_owned_data = slf.join_owned_data(self_block);
        let other_owned_data = JoinOwnedData {
            owned: &other.owned,
            borrows: &mut other.borrow,
            capabilities: &mut other.capabilities,
            block: other_block,
        };
        let mut repacks = slf_owned_data.join(other_owned_data, ctxt)?;
        for (place, cap) in slf.capabilities.iter() {
            if !place.is_owned(ctxt) {
                continue;
            }
            if let Some(other_cap) = other.capabilities.get(place, ctxt)
                && cap.expect_concrete() > other_cap.expect_concrete()
            {
                repacks.push(RepackOp::Weaken(Weaken::new(
                    place,
                    cap.expect_concrete(),
                    other_cap.expect_concrete(),
                )));
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
        let mut other_capabilities = other.capabilities.clone();
        let mut other_borrows = other.borrow.clone();
        let mut self_owned_data = self.join_owned_data(self_block);
        let other_owned_data = JoinOwnedData {
            owned: &other.owned,
            borrows: &mut other_borrows,
            capabilities: &mut other_capabilities,
            block: other_block,
        };
        let repack_ops = self_owned_data.join(other_owned_data, ctxt.ctxt)?;
        // For edges in the other graph that actually belong to it,
        // add the path condition that leads them to this block
        let mut other = other.clone();
        other.borrow.add_cfg_edge(other_block, self_block, ctxt);
        self.capabilities.join(&other_capabilities, ctxt);
        let borrow_args = JoinBorrowsArgs {
            self_block,
            other_block,
            body_analysis: ctxt.body_analysis,
            capabilities: &mut self.capabilities,
            owned: &mut self.owned,
        };
        self.borrow.join(&other_borrows, borrow_args, ctxt)?;
        Ok(repack_ops)
    }

    pub(crate) fn debug_lines(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Vec<Cow<'static, str>> {
        let mut result = self.borrow.debug_lines(ctxt);
        result.sort();
        let mut capabilities = self.capabilities.debug_lines(ctxt);
        capabilities.sort();
        result.extend(capabilities);
        result
    }
}

impl<'a, 'tcx: 'a, C: CapabilityLike>
    Pcg<'a, 'tcx, PlaceCapabilities<'tcx, C, Place<'tcx>>, BorrowPcgEdgeKind<'tcx>>
{
    pub(crate) fn start_block(analysis_ctxt: AnalysisCtxt<'a, 'tcx>) -> Self {
        let mut capabilities: PlaceCapabilities<'tcx, C, Place<'tcx>> =
            PlaceCapabilities::default();
        let owned = OwnedPcg::start_block(&mut capabilities, analysis_ctxt);
        let borrow = BorrowsState::start_block(&mut capabilities, analysis_ctxt);
        Pcg {
            owned,
            borrow,
            capabilities,
        }
    }
}
