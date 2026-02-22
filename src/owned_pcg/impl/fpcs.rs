// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use crate::{
    borrow_pcg::{graph::BorrowsGraph, region_projection::HasRegions},
    owned_pcg::{
        OwnedPcgNode,
        traverse::{FindSubtreeResult, Traversable},
    },
    pcg::{
        CapabilityKind, CapabilityLike, OwnedCapability, PositiveCapability,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesReader},
    },
    rustc_interface::{
        ast::Mutability,
        index::{Idx, IndexVec},
        middle::mir::{self, Local, RETURN_PLACE},
    },
    utils::{
        DebugCtxt, HasCompilerCtxt, HasLocals, Place, PlaceLike,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        place::PlaceProjectable,
    },
};
use derive_more::{Deref, DerefMut};

use crate::{owned_pcg::OwnedPcgLocal, utils::CompilerCtxt};

#[derive(Clone, PartialEq, Eq, Deref, DerefMut)]
/// The expansions of all locals.
pub struct OwnedPcg<'tcx>(IndexVec<Local, OwnedPcgLocal<'tcx>>);

impl<'tcx> OwnedPcg<'tcx> {
    pub(crate) fn places(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> HashSet<Place<'tcx>> {
        self.0
            .iter_enumerated()
            .filter(|(_, c)| !c.is_unallocated())
            .flat_map(|(local, e)| e.get_allocated().places(local, ctxt))
            .collect()
    }
}

impl Debug for OwnedPcg<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let v: Vec<_> = self.0.iter().filter(|c| !c.is_unallocated()).collect();
        v.fmt(f)
    }
}

fn child_nodes<'a, 'tcx: 'a, 'node, Ctxt: HasCompilerCtxt<'a, 'tcx> + Copy>(
    node: &'node OwnedPcgNode<'tcx>,
    place: Place<'tcx>,
    ctxt: Ctxt,
) -> Vec<(Place<'tcx>, &'node OwnedPcgNode<'tcx>)> {
    let OwnedPcgNode::Internal(internal) = node else {
        return vec![];
    };
    internal
        .expansions()
        .into_iter()
        .flat_map(|expansion| {
            expansion
                .expansion
                .data()
                .into_iter()
                .map(|(elem, child)| {
                    let child_place = place.project_deeper(elem, ctxt).unwrap_or_else(|err| {
                        panic!(
                            "Failed to project place {} with element {elem:?}: {err:?}",
                            place.display_string(ctxt)
                        )
                    });
                    (child_place, child)
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

fn push_subtree_lines<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx> + Copy>(
    node: &OwnedPcgNode<'tcx>,
    place: Place<'tcx>,
    ctxt: Ctxt,
    prefix: &str,
    is_last: bool,
    lines: &mut Vec<String>,
) {
    let connector = if is_last { "`-- " } else { "|-- " };
    lines.push(format!(
        "{prefix}{connector}{} ({:?})",
        place.display_string(ctxt),
        node.owned_capability()
    ));

    let child_prefix = format!("{prefix}{}", if is_last { "    " } else { "|   " });
    let children = child_nodes(node, place, ctxt);
    let children_len = children.len();
    for (index, (child_place, child_node)) in children.into_iter().enumerate() {
        push_subtree_lines(
            child_node,
            child_place,
            ctxt,
            &child_prefix,
            index + 1 == children_len,
            lines,
        );
    }
}

pub(crate) struct DisplayNodeCtxt<'tcx> {
    place: Place<'tcx>,
    prefix: String,
    is_last: bool,
}

impl<'tcx> DisplayNodeCtxt<'tcx> {
    pub(crate) fn new(place: Place<'tcx>) -> Self {
        Self {
            place,
            prefix: "".to_owned(),
            is_last: true,
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx> + Copy>
    DisplayWithCtxt<(Ctxt, DisplayNodeCtxt<'tcx>)> for OwnedPcgNode<'tcx>
{
    fn display_output(
        &self,
        ctxt: (Ctxt, DisplayNodeCtxt<'tcx>),
        mode: OutputMode,
    ) -> DisplayOutput {
        let mut lines: Vec<DisplayOutput> = vec![];
        let d_ctxt = ctxt.1;
        let connector = if d_ctxt.is_last { "`-- " } else { "|-- " };
        lines.push(
            format!(
                "{}{connector}{} ({:?})",
                d_ctxt.prefix,
                d_ctxt.place.display_string(ctxt.0),
                self.owned_capability()
            )
            .into(),
        );

        let child_prefix = format!(
            "{}{}",
            d_ctxt.prefix,
            if d_ctxt.is_last { "    " } else { "|   " }
        );
        let children = child_nodes(self, d_ctxt.place, ctxt.0);
        let children_len = children.len();
        for (index, (child_place, child_node)) in children.into_iter().enumerate() {
            lines.push(child_node.display_output(
                (
                    ctxt.0,
                    DisplayNodeCtxt {
                        place: child_place,
                        prefix: child_prefix.clone(),
                        is_last: index + 1 == children_len,
                    },
                ),
                mode,
            ))
        }
        DisplayOutput::join(lines, &DisplayOutput::NEWLINE)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx> + Copy> DisplayWithCtxt<Ctxt>
    for OwnedPcg<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        let mut lines = vec!["OwnedPcg".to_owned()];
        let allocated_locals = self
            .0
            .iter_enumerated()
            .filter_map(|(local, local_expansions)| {
                if local_expansions.is_unallocated() {
                    None
                } else {
                    Some((local, local_expansions))
                }
            })
            .collect::<Vec<_>>();

        if allocated_locals.is_empty() {
            lines.push("`-- <empty>".to_owned());
            return DisplayOutput::Text(lines.join("\n").into());
        }

        let allocated_len = allocated_locals.len();
        for (index, (local, local_expansions)) in allocated_locals.into_iter().enumerate() {
            let root_place: Place<'tcx> = local.into();
            push_subtree_lines(
                local_expansions.get_allocated(),
                root_place,
                ctxt,
                "",
                index + 1 == allocated_len,
                &mut lines,
            );
        }

        DisplayOutput::Text(lines.join("\n").into())
    }
}

impl<'tcx> OwnedPcg<'tcx> {
    pub(crate) fn owned_subtree_mut<'a>(
        &mut self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<&mut OwnedPcgNode<'tcx>>
    where
        'tcx: 'a,
    {
        assert!(place.is_owned(ctxt));
        let owned_local = &mut self.0[place.local];
        if let OwnedPcgLocal::Allocated(expansions) = owned_local {
            expansions.subtree_mut(&place.with_inherent_region(ctxt).projection)
        } else {
            None
        }
    }
    pub(crate) fn owned_subtree<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> FindSubtreeResult<'_, 'tcx>
    where
        'tcx: 'a,
    {
        assert!(place.is_owned(ctxt));
        let owned_local = &self.0[place.local];
        if let OwnedPcgLocal::Allocated(expansions) = owned_local {
            expansions.find_subtree(&place.with_inherent_region(ctxt).projection)
        } else {
            FindSubtreeResult::none()
        }
    }
    pub(crate) fn capability<'a>(
        &self,
        place: Place<'tcx>,
        borrows: &BorrowsGraph<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx> + DebugCtxt,
    ) -> CapabilityKind
    where
        'tcx: 'a,
    {
        self.get_capability_and_reason(place, borrows, ctxt).0
    }

    pub(crate) fn get_capability_and_reason<'a>(
        &self,
        place: Place<'tcx>,
        borrows: &BorrowsGraph<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx> + DebugCtxt,
    ) -> (CapabilityKind, AssignedCapabilityReason<'tcx>)
    where
        'tcx: 'a,
    {
        if place.is_owned(ctxt) {
            let find_subtree_result = self.owned_subtree(place, ctxt);
            let Some(owned_subtree) = find_subtree_result.subtree() else {
                return (CapabilityKind::None(()), AssignedCapabilityReason::Other);
            };
            let is_fully_initialized = owned_subtree.check_initialization(place, ctxt).unwrap_or_else(|err| {
                panic!("Failed to check if owned subtree is fully initialized for place {place:?}: {err:?}");
            });
            if !is_fully_initialized.is_fully_initialized() {
                return match owned_subtree {
                    OwnedPcgNode::Leaf(leaf) => (
                        leaf.inherent_capability.into(),
                        AssignedCapabilityReason::UninitializedLeaf(place),
                    ),
                    OwnedPcgNode::Internal(_) => {
                        (CapabilityKind::None(()), AssignedCapabilityReason::Other)
                    }
                };
            }
            for lifetime_projection in place.lifetime_projections(ctxt) {
                if !borrows.contains(lifetime_projection, ctxt) {
                    return (
                        CapabilityKind::ShallowExclusive,
                        AssignedCapabilityReason::Other,
                    );
                }
            }
            let mut has_immut_borrow = false;
            for place in owned_subtree.all_places(place, ctxt) {
                match borrows.is_transitively_blocked(place, ctxt) {
                    Some(Mutability::Mut) => {
                        return (
                            CapabilityKind::None(()),
                            AssignedCapabilityReason::Borrowed(Mutability::Mut),
                        );
                    }
                    Some(Mutability::Not) => {
                        has_immut_borrow = true;
                    }
                    None => {}
                }
            }
            if has_immut_borrow {
                return (
                    CapabilityKind::Read,
                    AssignedCapabilityReason::Borrowed(Mutability::Not),
                );
            }
            if let Some(parent) = find_subtree_result.parent_node()
                && let Some(init) = parent
                    .check_initialization(place.parent_place().unwrap(), ctxt)
                    .unwrap()
                    .as_all_initialized()
            {
                return (
                    CapabilityKind::Read,
                    AssignedCapabilityReason::ParentFullyInitialized(init.clone()),
                );
            } else {
                return (CapabilityKind::Exclusive, AssignedCapabilityReason::Other);
            }
        } else {
            let borrowed_capability = borrows
                .capability(place, ctxt)
                .map(|c| c.into())
                .unwrap_or(CapabilityKind::None(()));
            return (borrowed_capability, AssignedCapabilityReason::Other);
        }
    }
    pub(crate) fn start_block<Ctxt: HasLocals>(ctxt: Ctxt) -> Self {
        let always_live = ctxt.always_live_locals();
        let return_local = RETURN_PLACE;
        let last_arg = Local::new(ctxt.arg_count());
        let capability_summary = IndexVec::from_fn_n(
            |local: mir::Local| {
                if local == return_local {
                    OwnedPcgLocal::new(OwnedCapability::Write)
                } else if local <= last_arg {
                    OwnedPcgLocal::new(OwnedCapability::Exclusive)
                } else if always_live.contains(local) {
                    OwnedPcgLocal::new(OwnedCapability::Write)
                } else {
                    // Other locals are unallocated
                    OwnedPcgLocal::Unallocated
                }
            },
            ctxt.local_count(),
        );
        OwnedPcg(capability_summary)
    }
}

impl<'tcx> OwnedPcg<'tcx> {
    pub(crate) fn check_validity<'a>(
        &self,
        borrows: &BorrowsGraph<'tcx>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> std::result::Result<(), String> {
        self.0
            .iter()
            .try_for_each(|c| c.check_validity(borrows, ctxt))
    }

    pub(crate) fn num_locals(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn leaf_places<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.0
            .iter_enumerated()
            .filter(|(_, c)| !c.is_unallocated())
            .flat_map(|(local, c)| c.get_allocated().leaf_places(local.into(), ctxt))
            .collect()
    }

    pub(crate) fn contains_place(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        let expansion = &self.0[place.local];
        if expansion.is_unallocated() {
            return false;
        }
        expansion
            .get_allocated()
            .contains_projection_to(&place.projection)
    }

    pub(crate) fn is_allocated(&self, local: Local) -> bool {
        !self.0[local].is_unallocated()
    }

    pub(crate) fn allocated_locals(&self) -> Vec<mir::Local> {
        self.0
            .iter_enumerated()
            .filter_map(|(i, c)| if c.is_unallocated() { None } else { Some(i) })
            .collect()
    }

    pub(crate) fn unallocated_locals(&self) -> Vec<mir::Local> {
        self.0
            .iter_enumerated()
            .filter_map(|(i, c)| if c.is_unallocated() { Some(i) } else { None })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AssignedCapabilityReason<'tcx> {
    Borrowed(Mutability),
    ParentFullyInitialized(HashSet<Place<'tcx>>),
    UninitializedLeaf(Place<'tcx>),
    Other,
}
