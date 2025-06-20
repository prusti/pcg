use std::borrow::Cow;

use itertools::Itertools;

use super::PcgError;
use super::PcgVisitor;
use crate::action::PcgAction;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike, LocalNode};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::graph::frozen::FrozenGraphRef;
use crate::free_pcs::CapabilityKind;
use crate::pcg::PCGNode;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::HasPlace;

type EdgesToTrim<'tcx> = Vec<(BorrowPcgEdge<'tcx>, Cow<'static, str>)>;

impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    /// Removes leaves that are old or dead (based on the borrow checker). This
    /// function should called prior to evaluating the effect of the statement
    /// at `location`.
    ///
    /// Note that the liveness calculation is performed based on what happened
    /// at the end of the *previous* statement.
    ///
    /// For example when evaluating:
    /// ```text
    /// bb0[1]: let x = &mut y;
    /// bb0[2]: *x = 2;
    /// bb0[3]: ... // x is dead
    /// ```
    /// we do not remove the `*x -> y` edge until `bb0[3]`.
    /// This ensures that the edge appears in the graph at the end of `bb0[2]`
    /// (rather than never at all).
    ///
    /// Additional caveat: we do not remove dead places that are function
    /// arguments. At least for now this interferes with the implementation in
    /// the Prusti purified encoding for accessing the final value of a
    /// reference-typed function argument in its postcondition.
    pub(crate) fn pack_old_and_dead_borrow_leaves(&mut self) -> Result<(), PcgError> {
        let debug_iteration_limit = 10000;
        let mut iteration = 0;
        self.restore_capability_to_leaf_places()?;
        loop {
            iteration += 1;
            let edges_to_trim = self.pack_iteration()?;
            if edges_to_trim.is_empty() {
                break Ok(());
            }
            for (edge, reason) in edges_to_trim {
                self.remove_edge_and_perform_associated_state_updates(
                    edge,
                    &format!("Trim Old Leaves (iteration {}): {}", iteration, reason),
                )?
            }
            if iteration % 10 == 0 {
                tracing::info!(
                    "Packing old and dead borrow leaves: iteration {}",
                    iteration
                );
            }
            if iteration > debug_iteration_limit {
                panic!(
                    "Packing old and dead borrow leaves took more than {debug_iteration_limit} iterations"
                );
            }
        }
    }

    fn restore_capability_to_leaf_places(&mut self) -> Result<(), PcgError> {
        let leaf_places = self.pcg.leaf_places_where(
            |p| {
                self.pcg.capabilities.get(p) == Some(CapabilityKind::Read)
                    && !p.projects_shared_ref(self.ctxt)
            },
            self.ctxt,
        );
        for place in leaf_places {
            let action = PcgAction::restore_capability(
                place,
                CapabilityKind::Exclusive,
                "restore capability to leaf place",
                self.ctxt,
            );
            self.record_and_apply_action(action)?;
        }
        Ok(())
    }

    fn pack_iteration<'slf>(&'slf mut self) -> Result<EdgesToTrim<'tcx>, PcgError> {
        enum ShouldKillNode {
            Yes { reason: Cow<'static, str> },
            No,
        }

        let ctxt = self.ctxt;
        let location = self.location;

        let should_kill_node = |p: LocalNode<'tcx>, fg: &FrozenGraphRef<'slf, 'tcx>| {
            let place = match p {
                PCGNode::Place(p) => p,
                PCGNode::RegionProjection(rp) => rp.place(),
            };
            if place.is_old() {
                return ShouldKillNode::Yes {
                    reason: "Place is old".into(),
                };
            }

            if ctxt.is_arg(place.local()) {
                return ShouldKillNode::No;
            }

            if p.is_place()
                && !place.place().projection.is_empty()
                && !fg.has_edge_blocking(place.into(), ctxt)
            {
                return ShouldKillNode::Yes {
                    reason:
                        "Node is a place with a non-empty projection and is not blocked by an edge"
                            .into(),
                };
            }

            if ctxt.bc.is_dead(p.into(), location, true) {
                return ShouldKillNode::Yes {
                    reason: "Borrow-checker reports node as dead".into(),
                };
            }

            ShouldKillNode::No
        };

        enum ShouldPackEdge {
            Yes { reason: Cow<'static, str> },
            No,
        }

        let mut edges_to_trim = Vec::new();
        let fg = self.pcg.borrow.graph().frozen_graph();
        let location = self.location;
        let should_pack_edge = |edge: &BorrowPcgEdgeKind<'tcx>| match edge {
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                if expansion.expansion().iter().all(|node| {
                    node.is_old() || self.ctxt.bc.is_dead(node.place().into(), location, true)
                }) {
                    ShouldPackEdge::Yes {
                        reason: "Expansion is old or dead".into(),
                    }
                } else if expansion.is_packable(&self.pcg.capabilities) {
                    ShouldPackEdge::Yes {
                        reason: format!(
                            "Expansion {} is packable",
                            expansion.to_short_string(self.ctxt)
                        )
                        .into(),
                    }
                } else {
                    ShouldPackEdge::No
                }
            }
            _ => {
                let mut why_killed_reasons = Vec::new();
                for node in edge.blocked_by_nodes(self.ctxt) {
                    if let ShouldKillNode::Yes { reason } = should_kill_node(node, &fg) {
                        why_killed_reasons.push(format!(
                            "{}: {}",
                            node.to_short_string(self.ctxt),
                            reason
                        ));
                    } else {
                        return ShouldPackEdge::No;
                    }
                }
                ShouldPackEdge::Yes {
                    reason: format!(
                        "Edge is blocked by nodes that should be killed: {}",
                        why_killed_reasons.join(", ")
                    )
                    .into(),
                }
            }
        };
        for edge in fg
            .leaf_edges(self.ctxt)
            .into_iter()
            .map(|e| e.to_owned_edge())
        {
            if let ShouldPackEdge::Yes { reason } = should_pack_edge(edge.kind()) {
                edges_to_trim.push((edge, reason));
            }
        }
        Ok(edges_to_trim)
    }

    pub(crate) fn collapse_owned_places(&mut self) -> Result<(), PcgError> {
        for caps in self
            .pcg
            .owned
            .data
            .clone()
            .unwrap()
            .capability_projections()
        {
            let mut expansions = caps
                .expansions()
                .clone()
                .into_iter()
                .sorted_by_key(|(p, _)| p.projection.len())
                .collect::<Vec<_>>();
            while let Some((base, expansion)) = expansions.pop() {
                let expansion_places = base.expansion_places(&expansion, self.ctxt);
                if expansion_places
                    .iter()
                    .all(|p| !self.pcg.borrow.graph().contains(*p, self.ctxt))
                    && let Some(candidate_cap) = self.pcg.capabilities.get(expansion_places[0])
                    && expansion_places
                        .iter()
                        .all(|p| self.pcg.capabilities.get(*p) == Some(candidate_cap))
                {
                    self.collapse(
                        base,
                        candidate_cap,
                        format!("Collapse owned place {}", base.to_short_string(self.ctxt)),
                    )?;
                    if base.projection.is_empty()
                        && self.pcg.capabilities.get(base) == Some(CapabilityKind::Read)
                    {
                        self.pcg
                            .capabilities
                            .insert(base, CapabilityKind::Exclusive);
                    }
                }
            }
        }
        Ok(())
    }
}
