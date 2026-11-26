//! Invariants of every state:
//! - `leaves`: a place with W holds no valid value (it is uninitialised or
//!   moved out), so nothing reached through it holds a capability. The
//!   other parent-child rules are checked by `PlaceCapabilities`'s validity
//!   check.
//! - `cycle`: on every path, the borrow graph is acyclic: a place cannot
//!   (transitively) block itself. A cycle counts if one path satisfies the
//!   validity conditions of all its edges.

use std::collections::{BTreeSet, HashMap, HashSet};

use itertools::Itertools;

use super::{fail, show};
use crate::{
    borrow_pcg::{
        edge::kind::BorrowPcgEdgeKind, edge_data::EdgeData, validity_conditions::ValidityConditions,
    },
    pcg::{CapabilityKind, Pcg, PcgNode, place_capabilities::PlaceCapabilitiesReader},
    rustc_interface::middle::mir::{self, BasicBlock},
    utils::{CompilerCtxt, Place, display::DisplayWithCompilerCtxt},
};

/// The most steps the cycle search takes in one state.
const CYCLE_SEARCH_BUDGET: usize = 20_000;

pub(crate) fn check<'a, 'tcx: 'a>(
    pcg: &Pcg<'a, 'tcx>,
    location: mir::Location,
    ctxt: CompilerCtxt<'a, 'tcx>,
) {
    let capabilities = &pcg.place_capabilities;
    // The places below each W place that hold a capability, found from the
    // places up, so that the check is linear in the places and their depth.
    let mut below_write: HashMap<Place<'tcx>, Vec<String>> = HashMap::new();
    for (part, capability) in capabilities.iter() {
        if part.contains_unsafe_deref(ctxt) {
            continue;
        }
        for ancestor in std::iter::successors(part.parent_place(), |p| p.parent_place()) {
            if capabilities.get(ancestor, ctxt) == Some(CapabilityKind::Write)
                && !ancestor.is_raw_ptr(ctxt)
            {
                below_write.entry(ancestor).or_default().push(format!(
                    "{}: {}",
                    part.display_string(ctxt),
                    show(Some(capability))
                ));
            }
        }
    }
    let mut below_write = below_write.into_iter().collect::<Vec<_>>();
    below_write.sort_by_key(|(place, _)| place.display_string(ctxt));
    for (place, mut below) in below_write {
        below.sort();
        fail(
            ctxt,
            "leaves",
            &format!(
                "{location:?}: {} holds W, but places reached through it hold {}",
                place.display_string(ctxt),
                below.join(", ")
            ),
        );
    }
    if let Some(cycle) = cycle_on_one_path(pcg.borrow.graph.edges.iter(), ctxt) {
        fail(
            ctxt,
            "cycle",
            &format!(
                "{location:?}: the borrow graph has a cycle on one path: {}",
                cycle
                    .iter()
                    .map(|edge| edge.display_string(ctxt))
                    .join(", ")
            ),
        );
    }
}

/// The branch choices a set of paths makes: the successors each constrained
/// block may go to.
type Choices = HashMap<BasicBlock, HashSet<BasicBlock>>;

/// The choices of `choices` and `conditions` together, or `None` if no path
/// makes both.
fn conjoin(
    choices: &Choices,
    conditions: &ValidityConditions,
    body: &mir::Body<'_>,
) -> Option<Choices> {
    let mut result = choices.clone();
    for branch in conditions.all_branch_choices() {
        let allowed = branch.successors(body).into_iter().collect::<HashSet<_>>();
        let entry = result
            .entry(branch.from())
            .or_insert_with(|| allowed.clone());
        entry.retain(|s| allowed.contains(s));
        if entry.is_empty() {
            return None;
        }
    }
    Some(result)
}

/// For each of `edges`, the edges that block what it is blocked by, in
/// order.
fn successors<'a, 'tcx: 'a>(
    edges: &[(&BorrowPcgEdgeKind<'tcx>, &ValidityConditions)],
    ctxt: CompilerCtxt<'a, 'tcx>,
) -> Vec<Vec<usize>> {
    let mut blocking: HashMap<PcgNode<'tcx>, Vec<usize>> = HashMap::new();
    for (index, (edge, _)) in edges.iter().enumerate() {
        for node in edge.blocked_nodes(ctxt) {
            blocking.entry(node).or_default().push(index);
        }
    }
    edges
        .iter()
        .map(|(edge, _)| {
            edge.blocked_by_nodes(ctxt)
                .flat_map(|node| blocking.get(&node.into()).cloned().unwrap_or_default())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect()
        })
        .collect()
}

/// Whether the graph with `successors` has a cycle, ignoring conditions.
fn has_cycle(successors: &[Vec<usize>]) -> bool {
    // 0: not visited, 1: on the current path, 2: done.
    let mut state = vec![0u8; successors.len()];
    for root in 0..successors.len() {
        if state[root] != 0 {
            continue;
        }
        state[root] = 1;
        let mut stack = vec![(root, 0)];
        while let Some((node, next)) = stack.last_mut() {
            if let Some(&successor) = successors[*node].get(*next) {
                *next += 1;
                match state[successor] {
                    0 => {
                        state[successor] = 1;
                        stack.push((successor, 0));
                    }
                    1 => return true,
                    _ => {}
                }
            } else {
                state[*node] = 2;
                stack.pop();
            }
        }
    }
    false
}

/// A cycle of `edges` whose conditions one path satisfies, if the search
/// finds one within its budget. The search visits the edges in the order of
/// their text, so that its result does not depend on the order of the graph.
fn cycle_on_one_path<'e, 'a, 'tcx: 'a + 'e>(
    edges: impl Iterator<Item = (&'e BorrowPcgEdgeKind<'tcx>, &'e ValidityConditions)>,
    ctxt: CompilerCtxt<'a, 'tcx>,
) -> Option<Vec<&'e BorrowPcgEdgeKind<'tcx>>> {
    let edges = edges.collect::<Vec<_>>();
    if !has_cycle(&successors(&edges, ctxt)) {
        return None;
    }
    let mut edges = edges
        .into_iter()
        .map(|(edge, conditions)| (edge.display_string(ctxt), edge, conditions))
        .collect::<Vec<_>>();
    edges.sort_by(|a, b| a.0.cmp(&b.0));
    let edges = edges
        .into_iter()
        .map(|(_, edge, conditions)| (edge, conditions))
        .collect::<Vec<_>>();
    let next = successors(&edges, ctxt);
    let mut budget = CYCLE_SEARCH_BUDGET;
    for root in 0..edges.len() {
        let Some(choices) = conjoin(&Choices::new(), edges[root].1, ctxt.body()) else {
            continue;
        };
        let mut stack = vec![(vec![root], choices)];
        while let Some((path, choices)) = stack.pop() {
            for &successor in &next[*path.last().unwrap()] {
                budget = budget.checked_sub(1)?;
                if successor < root || (successor != root && path.contains(&successor)) {
                    continue;
                }
                let Some(choices) = conjoin(&choices, edges[successor].1, ctxt.body()) else {
                    continue;
                };
                if successor == root {
                    return Some(path.iter().map(|&i| edges[i].0).collect());
                }
                let mut path = path.clone();
                path.push(successor);
                stack.push((path, choices));
            }
        }
    }
    None
}
