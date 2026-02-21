use crate::{
    borrow_pcg::{
        borrow_pcg_edge::BorrowPcgEdgeLike,
        edge::kind::BorrowPcgEdgeKind,
        edge_data::{LabelEdgeLifetimeProjections, LabelNodePredicate},
        graph::loop_abstraction::{ConstructAbstractionGraphResult, MaybeRemoteCurrentPlace},
        region_projection::{HasRegions, LifetimeProjectionLabel},
        validity_conditions::ValidityConditions,
    },
    error::{PcgError, PcgUnsupportedError},
    r#loop::PlaceUsages,
    owned_pcg::OwnedPcg,
    pcg::{BodyAnalysis, PcgNode, PcgNodeLike, ctxt::AnalysisCtxt},
    pcg_validity_assert,
    rustc_interface::middle::mir::{self, BasicBlock},
    utils::{
        DebugRepr, HasBorrowCheckerCtxt, SnapshotLocation,
        data_structures::HashSet,
        display::DisplayWithCtxt,
        logging::{self, LogPredicate},
        validity::HasValidityCheck,
    },
    validity_checks_enabled,
    visualization::stmt_graphs::PcgLoopDebugData,
};

#[cfg(feature = "visualization")]
use crate::visualization::generate_pcg_dot_graph;

use super::BorrowsGraph;

pub(crate) struct JoinBorrowsArgs<'pcg, 'a, 'tcx> {
    pub(crate) self_block: BasicBlock,
    pub(crate) other_block: BasicBlock,
    pub(crate) body_analysis: &'pcg BodyAnalysis<'a, 'tcx>,
    pub(crate) owned: &'pcg mut OwnedPcg<'tcx>,
}

impl<'mir, 'tcx> JoinBorrowsArgs<'_, 'mir, 'tcx> {
    pub(crate) fn reborrow<'slf>(&'slf mut self) -> JoinBorrowsArgs<'slf, 'mir, 'tcx> {
        JoinBorrowsArgs {
            self_block: self.self_block,
            other_block: self.other_block,
            body_analysis: self.body_analysis,
            owned: self.owned,
        }
    }
}

impl<'tcx> BorrowsGraph<'tcx> {
    fn apply_placeholder_labels<'mir>(&mut self, ctxt: impl HasBorrowCheckerCtxt<'mir, 'tcx>)
    where
        'tcx: 'mir,
    {
        let nodes = self.nodes(ctxt.bc_ctxt());
        for node in nodes {
            if let PcgNode::LifetimeProjection(rp) = node
                && rp.is_future()
                && let Some(PcgNode::LifetimeProjection(local_rp)) =
                    rp.try_to_local_node(ctxt.bc_ctxt())
            {
                let orig_rp = local_rp.with_label(None, ctxt.bc_ctxt());
                self.filter_mut_edges(|edge| {
                    edge.value
                        .label_lifetime_projections(
                            &LabelNodePredicate::equals_lifetime_projection(orig_rp),
                            Some(LifetimeProjectionLabel::Future),
                            ctxt.bc_ctxt(),
                        )
                        .to_filter_mut_result()
                });
            }
        }
    }

    pub(crate) fn join<'slf, 'a>(
        &'slf mut self,
        other_graph: &'slf BorrowsGraph<'tcx>,
        validity_conditions: &'slf ValidityConditions,
        mut args: JoinBorrowsArgs<'slf, 'a, 'tcx>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError<'tcx>> {
        let other_block = args.other_block;
        let self_block = args.self_block;
        pcg_validity_assert!(
            other_graph.is_valid(ctxt.bc_ctxt()),
            [ctxt],
            "Other graph is invalid"
        );
        pcg_validity_assert!(
            !ctxt.ctxt.is_back_edge(other_block, self_block),
            [ctxt],
            "Joining back edge from {other_block:?} to {self_block:?}"
        );
        if let Some(used_places) = args.body_analysis.get_places_used_in_loop(self_block) {
            self.join_loop(used_places, validity_conditions, args.reborrow(), ctxt)?;
            pcg_validity_assert!(
                self.is_valid(ctxt.bc_ctxt()),
                [ctxt],
                "Graph became invalid after join"
            );
            return Ok(());
        }
        for other_edge in other_graph.edges() {
            self.insert(other_edge.to_owned_edge(), ctxt);
        }

        for edge in self
            .edges()
            .map(super::super::borrow_pcg_edge::BorrowPcgEdgeLike::to_owned_edge)
            .collect::<Vec<_>>()
        {
            if let BorrowPcgEdgeKind::Abstraction(_) = edge.kind() {
                continue;
            }
            if self.is_encapsulated_by_abstraction(&edge.value, ctxt.ctxt) {
                self.remove(edge.kind());
            }
        }

        self.apply_placeholder_labels(ctxt);

        if validity_checks_enabled() && !self.is_valid(ctxt.bc_ctxt()) {
            pcg_validity_assert!(
                false,
                [ctxt],
                "Graph became invalid after join. self: {self_block:?}, other: {other_block:?}"
            );
        }
        Ok(())
    }

    #[cfg(feature = "visualization")]
    fn debug_graph<'a>(
        &self,
        owned: &OwnedPcg<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> String
    where
        'tcx: 'a,
    {
        use crate::{
            borrow_pcg::{state::BorrowStateRef, validity_conditions::ValidityConditionsLike},
            pcg::PcgRef,
        };

        let pcg_ref = PcgRef::new(owned, BorrowStateRef::new(self, ValidityConditions::EMPTY));
        generate_pcg_dot_graph(pcg_ref, ctxt, None).unwrap()
    }

    fn join_loop<'mir>(
        &mut self,
        used_places: &PlaceUsages<'tcx>,
        validity_conditions: &ValidityConditions,
        mut args: JoinBorrowsArgs<'_, 'mir, 'tcx>,
        ctxt: AnalysisCtxt<'mir, 'tcx>,
    ) -> Result<(), PcgError<'tcx>> {
        let loop_head = args.self_block;
        logging::log!(
            &LogPredicate::DebugBlock,
            ctxt,
            "used places: {}",
            used_places.display_string(ctxt.ctxt)
        );
        // p_loop
        let live_loop_places = used_places.usages_where(|p| {
            args.body_analysis.is_live_and_initialized_at(
                mir::Location {
                    block: args.self_block,
                    statement_index: 0,
                },
                p.place,
            )
        });

        if !live_loop_places
            .usages_where(|p| p.place.contains_unsafe_deref(ctxt.ctxt))
            .is_empty()
        {
            return Err(PcgUnsupportedError::DerefUnsafePtr.into());
        }

        logging::log!(
            &LogPredicate::DebugBlock,
            ctxt,
            "live loop places: {}",
            live_loop_places.display_string(ctxt.ctxt)
        );

        let loop_blocked_places = live_loop_places.usages_where(|p| {
            ctxt.ctxt.borrow_checker.is_directly_blocked(
                p.place,
                mir::Location {
                    block: args.self_block,
                    statement_index: 0,
                },
                ctxt.ctxt,
            )
        });

        logging::log!(
            &LogPredicate::DebugBlock,
            ctxt,
            "loop_blocked_places: {}",
            loop_blocked_places.display_string(ctxt.ctxt)
        );

        let loop_blocker_places =
            live_loop_places.usages_where(|p| !p.place.regions(ctxt.ctxt).is_empty());

        logging::log!(
            &LogPredicate::DebugBlock,
            ctxt,
            "loop_blocker_places: {}",
            loop_blocker_places.display_string(ctxt.ctxt)
        );

        let expand_places = loop_blocker_places.joined_with(&loop_blocked_places);

        self.expand_places_for_abstraction(
            &loop_blocked_places,
            &expand_places,
            validity_conditions,
            &mut args.reborrow(),
            ctxt,
        );

        let pre_loop_dot_graph = self.debug_graph(args.owned, ctxt);

        // p_roots
        let roots_of_live_places = live_loop_places
            .iter()
            .map(|p| (p, self.get_borrow_roots(p.place, loop_head, ctxt.ctxt)));

        fn roots_to_places<'tcx>(
            roots: &HashSet<PcgNode<'tcx>>,
            live_loop_places: &PlaceUsages<'tcx>,
        ) -> HashSet<MaybeRemoteCurrentPlace<'tcx>> {
            roots
                .iter()
                .filter_map(PcgNode::related_maybe_remote_current_place)
                .filter(|p| {
                    !(p.is_local() && live_loop_places.contains(p.relevant_place_for_blocking()))
                })
                .collect()
        }

        let root_places = roots_of_live_places
            .map(|(p, roots)| (p, roots_to_places(&roots, &live_loop_places)))
            .collect::<Vec<_>>();

        let ConstructAbstractionGraphResult {
            graph: abstraction_graph,
            to_label,
            ..
        } = self.get_loop_abstraction_graph(
            &loop_blocked_places,
            &root_places
                .iter()
                .flat_map(|(_, snd)| snd)
                .copied()
                .collect::<HashSet<_>>(),
            &loop_blocker_places,
            loop_head,
            validity_conditions,
            ctxt,
        );

        // abstraction_graph.render_debug_graph(
        //     loop_head,
        //     Some(DebugImgcat::JoinLoop),
        //     capabilities,
        //     "Abstraction graph",
        //     ctxt,
        // );

        for rp in &to_label {
            self.filter_mut_edges(|edge| {
                edge.value
                    .label_lifetime_projections(
                        rp,
                        Some(LifetimeProjectionLabel::Location(SnapshotLocation::Loop(
                            loop_head,
                        ))),
                        ctxt.ctxt,
                    )
                    .to_filter_mut_result()
            });
        }

        // for (place, cap) in capability_updates {
        //     capabilities.insert(place, cap, ctxt);
        // }

        let abstraction_graph_pcg_nodes = abstraction_graph.nodes(ctxt.ctxt);
        let to_cut = self.identify_subgraph_to_cut(loop_head, &abstraction_graph_pcg_nodes, ctxt);
        ctxt.set_debug_loop_data(PcgLoopDebugData::new(
            used_places.debug_repr(ctxt),
            live_loop_places.debug_repr(ctxt),
            loop_blocked_places.debug_repr(ctxt),
            loop_blocker_places.debug_repr(ctxt),
            root_places
                .iter()
                .map(|(p, roots)| {
                    (
                        p.display_string(ctxt),
                        roots
                            .iter()
                            .map(|p| p.display_string(ctxt))
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
            pre_loop_dot_graph,
            abstraction_graph.debug_graph(args.owned, ctxt),
            to_cut.debug_graph(args.owned, ctxt),
        ));
        for edge in to_cut.edges() {
            self.remove(edge.kind());
        }
        for edge in abstraction_graph.into_edges() {
            self.insert(edge, ctxt.ctxt);
        }
        Ok(())
    }
}
