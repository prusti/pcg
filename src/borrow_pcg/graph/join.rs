use crate::{
    HasSettings,
    borrow_pcg::{
        action::LabelPlaceReason,
        borrow_pcg_edge::BorrowPcgEdgeLike,
        edge::kind::BorrowPcgEdgeKind,
        edge_data::{LabelEdgeLifetimeProjections, LabelNodePredicate},
        graph::loop_abstraction::ConstructAbstractionGraphResult,
        has_pcs_elem::SetLabel,
        region_projection::LifetimeProjectionLabel,
        state::BorrowStateRef,
        validity_conditions::ValidityConditions,
    },
    error::{PcgError, PcgUnsupportedError},
    r#loop::{PlaceUsageType, PlaceUsages},
    pcg::{
        BodyAnalysis, PcgNode, PcgNodeLike, PcgRef, PcgRefLike,
        ctxt::AnalysisCtxt,
        owned_state::OwnedPcg,
        place_capabilities::{
            PlaceCapabilities, PlaceCapabilitiesInterface, PlaceCapabilitiesReader,
        },
    },
    pcg_validity_assert,
    rustc_interface::middle::mir::{self, BasicBlock},
    utils::{
        DebugImgcat, HasBorrowCheckerCtxt, SnapshotLocation,
        data_structures::HashSet,
        display::DisplayWithCompilerCtxt,
        logging::{self, LogPredicate},
        validity::HasValidityCheck,
    },
    validity_checks_enabled,
};

#[cfg(feature = "visualization")]
use crate::visualization::{
    dot_graph::DotGraph,
    generate_borrows_dot_graph,
    stmt_graphs::{PcgLoopDebugData, PlaceLabelReplacement},
};

use super::{BorrowsGraph, borrows_imgcat_debug};

pub(crate) struct JoinBorrowsArgs<'pcg, 'a, 'tcx> {
    pub(crate) self_block: BasicBlock,
    pub(crate) other_block: BasicBlock,
    pub(crate) body_analysis: &'pcg BodyAnalysis<'a, 'tcx>,
    pub(crate) capabilities: &'pcg mut PlaceCapabilities<'tcx>,
    pub(crate) owned: &'pcg mut OwnedPcg<'tcx>,
}

impl<'mir, 'tcx> JoinBorrowsArgs<'_, 'mir, 'tcx> {
    pub(crate) fn reborrow<'slf>(&'slf mut self) -> JoinBorrowsArgs<'slf, 'mir, 'tcx> {
        JoinBorrowsArgs {
            self_block: self.self_block,
            other_block: self.other_block,
            body_analysis: self.body_analysis,
            capabilities: self.capabilities,
            owned: self.owned,
        }
    }
}

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn render_debug_graph<'a>(
        &self,
        block: mir::BasicBlock,
        debug_imgcat: Option<DebugImgcat>,
        capabilities: &impl PlaceCapabilitiesReader<'tcx>,
        comment: &str,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) where
        'tcx: 'a,
    {
        #[cfg(feature = "visualization")]
        if borrows_imgcat_debug(block, debug_imgcat)
            && let Ok(dot_graph) = generate_borrows_dot_graph(ctxt.bc_ctxt(), capabilities, self)
        {
            DotGraph::render_with_imgcat(&dot_graph, comment).unwrap_or_else(|e| {
                eprintln!("Error rendering self graph: {e}");
            });
        }
    }

    /// Generate a DOT graph string for the borrows graph state (for debug visualization).
    #[cfg(feature = "visualization")]
    fn debug_graph<'a>(
        &self,
        capabilities: &impl PlaceCapabilitiesReader<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> String
    where
        'tcx: 'a,
    {
        generate_borrows_dot_graph(ctxt.bc_ctxt(), capabilities, self).unwrap_or_default()
    }

    fn apply_placeholder_labels<'mir, Ctxt>(
        &mut self,
        _capabilities: &impl PlaceCapabilitiesReader<'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'mir,
        Ctxt: HasBorrowCheckerCtxt<'mir, 'tcx> + HasSettings<'mir>,
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
                            ctxt,
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
        let old_self = self.clone();

        if let Some(used_places) = args
            .body_analysis
            .get_places_used_in_loop_with_head(self_block)
        {
            self.join_loop(used_places, validity_conditions, args.reborrow(), ctxt)?;
            #[cfg(feature = "visualization")]
            if borrows_imgcat_debug(self_block, Some(DebugImgcat::JoinLoop))
                && let Ok(dot_graph) =
                    generate_borrows_dot_graph(ctxt.ctxt, args.capabilities, self)
            {
                DotGraph::render_with_imgcat(&dot_graph, "After join (loop):").unwrap_or_else(
                    |e| {
                        eprintln!("Error rendering self graph: {e}");
                    },
                );
            }
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
            .map(BorrowPcgEdgeLike::to_owned_edge)
            .collect::<Vec<_>>()
        {
            if let BorrowPcgEdgeKind::Abstraction(_) = edge.kind() {
                continue;
            }
            if self.is_encapsulated_by_abstraction(&edge.value, ctxt.ctxt) {
                self.remove(edge.kind());
            }
        }

        self.apply_placeholder_labels(args.capabilities, ctxt);

        if validity_checks_enabled() && !self.is_valid(ctxt.bc_ctxt()) {
            pcg_validity_assert!(
                false,
                [ctxt],
                "Graph became invalid after join. self: {self_block:?}, other: {other_block:?}"
            );
            #[cfg(feature = "visualization")]
            {
                if let Ok(dot_graph) =
                    generate_borrows_dot_graph(ctxt.ctxt, args.capabilities, self)
                {
                    DotGraph::render_with_imgcat(&dot_graph, "Invalid self graph").unwrap_or_else(
                        |e| {
                            eprintln!("Error rendering self graph: {e}");
                        },
                    );
                }
                if let Ok(dot_graph) =
                    generate_borrows_dot_graph(ctxt.ctxt, args.capabilities, &old_self)
                {
                    DotGraph::render_with_imgcat(&dot_graph, "Old self graph").unwrap_or_else(
                        |e| {
                            eprintln!("Error rendering old self graph: {e}");
                        },
                    );
                }
                if let Ok(dot_graph) =
                    generate_borrows_dot_graph(ctxt.ctxt, args.capabilities, other_graph)
                {
                    DotGraph::render_with_imgcat(&dot_graph, "Other graph").unwrap_or_else(|e| {
                        eprintln!("Error rendering other graph: {e}");
                    });
                }
            }
        }
        Ok(())
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

        #[cfg(feature = "visualization")]
        let mut dot_graphs: Vec<(String, String)> = vec![];

        #[cfg(feature = "visualization")]
        dot_graphs.push((
            "Pre-Loop".to_owned(),
            self.debug_graph(args.capabilities, ctxt),
        ));

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

        // Label mutated places before expansion
        #[cfg(feature = "visualization")]
        let mut place_labels: Vec<(String, Vec<PlaceLabelReplacement>)> = Vec::new();
        for pu in used_places.iter() {
            let owned: &_ = args.owned;
            let pcg_ref = PcgRef {
                borrow: BorrowStateRef::new(self, validity_conditions),
                place_capabilities: args.capabilities,
                owned,
            };
            if !pcg_ref.is_leaf_place(pu.place, ctxt) && pu.usage == PlaceUsageType::Mutate {
                let replacements = self.label_place(
                    pu.place,
                    LabelPlaceReason::JoinLoop,
                    &SetLabel(SnapshotLocation::BeforeJoin(loop_head)),
                    ctxt,
                );
                #[cfg(feature = "visualization")]
                if !replacements.is_empty() {
                    place_labels.push((
                        pu.place.display_string(ctxt),
                        replacements
                            .into_iter()
                            .map(|r| {
                                PlaceLabelReplacement::new(
                                    r.from.display_string(ctxt),
                                    r.to.display_string(ctxt),
                                )
                            })
                            .collect(),
                    ));
                }
                #[cfg(not(feature = "visualization"))]
                let _ = replacements;
            }
        }

        #[cfg(feature = "visualization")]
        dot_graphs.push((
            "Place-Label".to_owned(),
            self.debug_graph(args.capabilities, ctxt),
        ));

        let expand_places = loop_blocker_places.joined_with(&loop_blocked_places);

        self.expand_places_for_abstraction(
            &loop_blocked_places,
            &expand_places,
            validity_conditions,
            &mut args.reborrow(),
            ctxt,
        );
        let capabilities = args.capabilities;
        self.render_debug_graph(
            loop_head,
            Some(DebugImgcat::JoinLoop),
            capabilities,
            "G_Pre'",
            ctxt.ctxt,
        );

        #[cfg(feature = "visualization")]
        dot_graphs.push((
            "Post-Expand".to_owned(),
            self.debug_graph(capabilities, ctxt),
        ));

        // p_roots: compute per-place ancestors
        let ancestors_of_live_places: Vec<_> = live_loop_places
            .iter()
            .map(|p| {
                let roots = self.get_borrow_roots(p.place, loop_head, ctxt.ctxt);
                (p, roots)
            })
            .collect();

        let live_roots: HashSet<_> = ancestors_of_live_places
            .iter()
            .flat_map(|(_, roots)| roots.iter().copied())
            .collect();

        logging::log!(
            &LogPredicate::DebugBlock,
            ctxt,
            "live roots: {}",
            live_roots.display_string(ctxt.ctxt)
        );

        let root_places = live_roots
            .iter()
            .filter_map(PcgNode::related_maybe_remote_current_place)
            .filter(|p| {
                !(p.is_local() && live_loop_places.contains(p.relevant_place_for_blocking()))
            })
            .collect::<HashSet<_>>();

        logging::log!(
            &LogPredicate::DebugBlock,
            ctxt,
            "root places: {}",
            root_places.display_string(ctxt.ctxt)
        );

        let ConstructAbstractionGraphResult {
            graph: abstraction_graph,
            to_label,
            capability_updates,
        } = self.get_loop_abstraction_graph(
            &loop_blocked_places,
            &root_places,
            &loop_blocker_places,
            loop_head,
            validity_conditions,
            ctxt,
        );

        abstraction_graph.render_debug_graph(
            loop_head,
            Some(DebugImgcat::JoinLoop),
            capabilities,
            "Abstraction graph",
            ctxt.ctxt,
        );

        for rp in &to_label {
            self.filter_mut_edges(|edge| {
                edge.value
                    .label_lifetime_projections(
                        rp,
                        Some(LifetimeProjectionLabel::Location(SnapshotLocation::Loop(
                            loop_head,
                        ))),
                        ctxt,
                    )
                    .to_filter_mut_result()
            });
        }

        for (place, cap_option) in capability_updates {
            if let Some(cap) = cap_option {
                capabilities.insert(place, cap, ctxt);
            } else {
                capabilities.remove(place, ctxt);
            }
        }

        let abstraction_graph_pcg_nodes = abstraction_graph.nodes(ctxt.ctxt);
        let to_cut = self.identify_subgraph_to_cut(loop_head, &abstraction_graph_pcg_nodes, ctxt);

        #[cfg(feature = "visualization")]
        dot_graphs.push((
            "Abstraction".to_owned(),
            abstraction_graph.debug_graph(capabilities, ctxt),
        ));
        #[cfg(feature = "visualization")]
        dot_graphs.push(("To Cut".to_owned(), to_cut.debug_graph(capabilities, ctxt)));

        to_cut.render_debug_graph(
            loop_head,
            Some(DebugImgcat::JoinLoop),
            capabilities,
            "To cut",
            ctxt.ctxt,
        );
        self.render_debug_graph(
            loop_head,
            Some(DebugImgcat::JoinLoop),
            capabilities,
            "Self before cut",
            ctxt.ctxt,
        );

        // Store the loop debug data for the visualization
        #[cfg(feature = "visualization")]
        ctxt.set_debug_loop_data(PcgLoopDebugData {
            used_places: used_places.to_debug_repr(ctxt),
            live_loop_places: live_loop_places.to_debug_repr(ctxt),
            loop_blocked_places: loop_blocked_places.to_debug_repr(ctxt),
            loop_blocker_places: loop_blocker_places.to_debug_repr(ctxt),
            ancestors_of_live_places: ancestors_of_live_places
                .iter()
                .map(|(p, ancestors)| {
                    (
                        p.display_string(ctxt),
                        ancestors
                            .iter()
                            .map(|n| n.display_string(ctxt))
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
            root_places: root_places
                .iter()
                .map(|p| (p.display_string(ctxt), Vec::<String>::new()))
                .collect::<Vec<_>>(),
            dot_graphs,
            place_labels,
        });

        for edge in to_cut.edges() {
            self.remove(edge.kind());
        }
        self.render_debug_graph(
            loop_head,
            Some(DebugImgcat::JoinLoop),
            capabilities,
            "Self after cut",
            ctxt.ctxt,
        );
        for edge in abstraction_graph.into_edges() {
            self.insert(edge, ctxt.ctxt);
        }
        let self_places = self.places(ctxt.ctxt);
        for place in to_cut.places(ctxt.ctxt) {
            if place.as_borrowed_place(ctxt.ctxt).is_some()
                && capabilities.get(place, ctxt.ctxt).is_some()
                && !self_places.contains(&place)
            {
                capabilities.remove(place, ctxt);
            }
        }
        self.render_debug_graph(
            loop_head,
            Some(DebugImgcat::JoinLoop),
            capabilities,
            "Final graph",
            ctxt.ctxt,
        );
        Ok(())
    }
}
