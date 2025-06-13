use crate::borrow_pcg::abstraction_graph_constructor::AbstractionGraphConstructor;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike};
use crate::borrow_pcg::borrow_pcg_expansion::{BorrowPcgExpansion, PlaceExpansion};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::has_pcs_elem::LabelRegionProjection;
use crate::borrow_pcg::region_projection::RegionProjectionLabel;
use crate::pcg::place_capabilities::PlaceCapabilities;
use crate::pcg::{PCGNode, PCGNodeLike};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::loop_usage::LoopUsage;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::{CompilerCtxt, SnapshotLocation};
use crate::visualization::dot_graph::DotGraph;
use crate::visualization::generate_borrows_dot_graph;
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::ToBorrowsEdge,
        edge::abstraction::{r#loop::LoopAbstraction, AbstractionBlockEdge},
        path_condition::PathConditions,
    },
    rustc_interface::middle::mir::BasicBlock,
    utils::{display::DisplayDiff, validity::HasValidityCheck},
    validity_checks_enabled,
};

use super::{borrows_imgcat_debug, coupling_imgcat_debug, BorrowsGraph};

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn render_debug_graph(&self, ctxt: CompilerCtxt<'_, 'tcx>, comment: &str) {
        if borrows_imgcat_debug()
            && let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, self)
        {
            DotGraph::render_with_imgcat(&dot_graph, comment).unwrap_or_else(|e| {
                eprintln!("Error rendering self graph: {e}");
            });
        }
    }

    fn apply_placeholder_labels<'mir>(
        &mut self,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) {
        let nodes = self.nodes(ctxt);
        for node in nodes {
            if let PCGNode::RegionProjection(rp) = node
                && rp.is_placeholder()
                && let Some(PCGNode::RegionProjection(local_rp)) = rp.try_to_local_node(ctxt)
            {
                if let MaybeOldPlace::Current { place } = local_rp.base
                    && capabilities.get(place).is_some()
                {
                    self.mut_edges(|edge| edge.label_region_projection(&local_rp, None, ctxt));
                } else {
                    let orig_rp = local_rp.with_label(None, ctxt);
                    self.mut_edges(|edge| {
                        edge.label_region_projection(
                            &orig_rp,
                            Some(RegionProjectionLabel::Placeholder),
                            ctxt,
                        )
                    });
                }
            }
        }
    }

    pub(crate) fn join<'mir>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        loop_usage: &LoopUsage<'tcx, '_>,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> bool {
        tracing::debug!("join {self_block:?} {other_block:?} start");
        // For performance reasons we don't check validity here.
        // if validity_checks_enabled() {
        //     pcg_validity_assert!(other.is_valid(repacker), "Other graph is invalid");
        // }
        let old_self = self.clone();

        if ctxt.is_back_edge(other_block, self_block) {
            self.render_debug_graph(ctxt, &format!("Self graph: {self_block:?}"));
            other.render_debug_graph(ctxt, &format!("Other graph: {other_block:?}"));
            self.join_loop(other, self_block, other_block, loop_usage, ctxt);
            let result = *self != old_self;
            if borrows_imgcat_debug()
                && let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, self)
            {
                DotGraph::render_with_imgcat(
                    &dot_graph,
                    &format!("After join (loop, changed={result:?}):"),
                )
                .unwrap_or_else(|e| {
                    eprintln!("Error rendering self graph: {e}");
                });
                if result {
                    eprintln!("{}", old_self.fmt_diff(self, ctxt))
                }
            }
            // For performance reasons we don't check validity here.
            // if validity_checks_enabled() {
            //     assert!(self.is_valid(repacker), "Graph became invalid after join");
            // }
            self.apply_placeholder_labels(capabilities, ctxt);
            return result;
        }
        for other_edge in other.edges() {
            self.insert(other_edge.to_owned_edge(), ctxt);
        }
        for edge in self
            .edges()
            .map(|edge| edge.to_owned_edge())
            .collect::<Vec<_>>()
        {
            if let BorrowPcgEdgeKind::Abstraction(_) = edge.kind() {
                continue;
            }
            if self.is_encapsulated_by_abstraction(&edge, ctxt) {
                self.remove(edge.kind());
            }
        }

        self.apply_placeholder_labels(capabilities, ctxt);

        let changed = old_self != *self;

        if borrows_imgcat_debug()
            && let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, self)
        {
            DotGraph::render_with_imgcat(&dot_graph, &format!("After join: (changed={changed:?})"))
                .unwrap_or_else(|e| {
                    eprintln!("Error rendering self graph: {e}");
                });
            if changed {
                eprintln!("{}", old_self.fmt_diff(self, ctxt))
            }
        }

        // For performance reasons we only check validity here if we are also producing debug graphs
        if validity_checks_enabled() && borrows_imgcat_debug() && !self.is_valid(ctxt) {
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, self) {
                DotGraph::render_with_imgcat(&dot_graph, "Invalid self graph").unwrap_or_else(
                    |e| {
                        eprintln!("Error rendering self graph: {e}");
                    },
                );
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, &old_self) {
                DotGraph::render_with_imgcat(&dot_graph, "Old self graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering old self graph: {e}");
                });
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(ctxt, other) {
                DotGraph::render_with_imgcat(&dot_graph, "Other graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering other graph: {e}");
                });
            }
            panic!("Graph became invalid after join. self: {self_block:?}, other: {other_block:?}");
        }
        changed
    }

    fn join_loop<'mir>(
        &mut self,
        other: &Self,
        loop_head: BasicBlock,
        from_block: BasicBlock,
        loop_usage: &LoopUsage<'tcx, '_>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) {
        tracing::debug!("join_loop {from_block:?} {loop_head:?} start");
        tracing::debug!("Self has {} edges", self.edges.len());
        tracing::debug!("Other has {} edges", other.edges.len());

        let old_self = self.clone();
        let self_abstraction_graph = AbstractionGraphConstructor::new(ctxt, loop_head)
            .construct_abstraction_graph(&old_self, ctxt.bc);
        // `loop_head` is the correct block to use here
        let other_coupling_graph = AbstractionGraphConstructor::new(ctxt, loop_head)
            .construct_abstraction_graph(other, ctxt.bc);

        if coupling_imgcat_debug() {
            self_abstraction_graph
                .render_with_imgcat(ctxt, &format!("self coupling graph: {from_block:?}"));
            other_coupling_graph
                .render_with_imgcat(ctxt, &format!("other coupling graph: {loop_head:?}"));
        }

        let mut result = self_abstraction_graph.clone();
        result.merge(&other_coupling_graph, loop_usage, ctxt);
        if coupling_imgcat_debug() {
            result.render_with_imgcat(ctxt, "merged coupling graph");
        }

        // First only keep edges present in both graphs (remove other edges from `self`)
        let to_keep = self.common_edges(other);
        self.edges
            .retain(|edge_kind, _| to_keep.contains(edge_kind));

        if borrows_imgcat_debug() {
            self.render_debug_graph(ctxt, "common edges");
        }

        let other_coupling_edges = other_coupling_graph.edges().collect::<Vec<_>>();
        let self_coupling_edges = self_abstraction_graph.edges().collect::<Vec<_>>();
        let unique_edges = result
            .edges()
            .filter(|edge| {
                self_coupling_edges.iter().all(|other| other != edge)
                    || other_coupling_edges.iter().all(|other| other != edge)
            })
            .collect::<Vec<_>>();

        // Add any edges that are missing in either graph
        for (blocked, assigned, to_remove) in unique_edges.iter() {
            tracing::debug!(
                "Adding edge {} -> {}",
                blocked.to_short_string(ctxt),
                assigned.to_short_string(ctxt)
            );
            // This edge is missing from one of the graphs
            let abstraction = LoopAbstraction::new(
                AbstractionBlockEdge::new(
                    blocked.clone().into_iter().map(|node| *node).collect(),
                    assigned
                        .clone()
                        .into_iter()
                        .map(|node| {
                            node.try_into().unwrap_or_else(|_e| {
                                panic!("Failed to convert node {node:?} to node index");
                            })
                        })
                        .collect(),
                    ctxt,
                ),
                loop_head,
            )
            .to_borrow_pcg_edge(PathConditions::new());

            self.insert(abstraction, ctxt);
            self.edges
                .retain(|edge_kind, _| !to_remove.contains(edge_kind));
        }

        // This is somewhat of a hack: we want to re-introduce borrow expansions
        // that were removed simply due to being re-introduced at different
        // times in the loop
        for (blocked, assigned, _) in unique_edges.iter() {
            for node in blocked.iter().chain(assigned.iter()) {
                if let Some(PCGNode::RegionProjection(rp)) =
                    node.to_pcg_node().try_to_local_node(ctxt)
                    && let Some(place) = rp.deref(ctxt)
                    && self.is_root(place, ctxt)
                {
                    self.insert(
                        BorrowPcgEdge::new(
                            BorrowPcgEdgeKind::BorrowPcgExpansion(
                                BorrowPcgExpansion::new(
                                    rp.base.into(),
                                    PlaceExpansion::Deref,
                                    Some(RegionProjectionLabel::Location(SnapshotLocation::Start(
                                        loop_head,
                                    ))),
                                    ctxt,
                                )
                                .unwrap(),
                            ),
                            PathConditions::new(),
                        ),
                        ctxt,
                    );
                }
            }
        }

        if borrows_imgcat_debug() {
            self.render_debug_graph(ctxt, "done");
        }
        tracing::debug!("join_loop {from_block:?} {loop_head:?} end");
    }
}
