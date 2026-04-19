//! Tree data type for the per-local initialisation state.
//!
//! See <https://prusti.github.io/pcg-docs/owned-state.html#tree-structure>.
//! An [`InitialisationTree`] mirrors the expansion structure of an owned
//! place: each internal node is an expansion (see
//! [`PlaceExpansion`]) whose per-child data holds the sub-tree under that
//! edge, and each leaf carries an [`OwnedCapability`].
//!
//! **Invariant** (debug-asserted by [`InitialisationTree::internal`]):
//! an internal node must have at least one of its descendant leaves be
//! `U` or `S`. Otherwise the tree would be collapsible to a single `D`
//! leaf.

use std::collections::BTreeMap;
use std::fmt::{Debug, Formatter};

use crate::borrow_pcg::borrow_pcg_expansion::PlaceExpansion;
use crate::owned_pcg::RepackGuide;

use super::OwnedCapability;

/// An initialisation state for a single owned local (or for any subtree
/// rooted at an owned place).
#[derive(Clone, PartialEq, Eq)]
pub(crate) enum InitialisationTree<'tcx> {
    /// A leaf carrying an [`OwnedCapability`]. No further expansion has
    /// been tracked for the subtree rooted here.
    Leaf(OwnedCapability),
    /// An internal (unpacked) node: the expansion of the place at this
    /// node, with each child's sub-tree stored as the per-child data of
    /// the expansion. By invariant, at least one descendant leaf is
    /// non-`Deep`.
    Internal(PlaceExpansion<'tcx, Box<InitialisationTree<'tcx>>>),
}

/// The result of joining two [`InitialisationTree`]s. `changed` reports
/// whether the left-hand side was updated.
#[derive(Debug)]
pub(crate) struct JoinOutcome<'tcx> {
    pub(crate) tree: InitialisationTree<'tcx>,
    pub(crate) changed: bool,
}

impl<'tcx> InitialisationTree<'tcx> {
    /// A fully-initialised single-leaf tree.
    pub(crate) fn deep() -> Self {
        Self::Leaf(OwnedCapability::Deep)
    }

    /// A shallowly-initialised single-leaf tree.
    #[allow(dead_code)]
    pub(crate) fn shallow() -> Self {
        Self::Leaf(OwnedCapability::Shallow)
    }

    /// An uninitialised single-leaf tree.
    pub(crate) fn uninit() -> Self {
        Self::Leaf(OwnedCapability::Uninit)
    }

    /// Construct an internal node.
    ///
    /// Callers are responsible for maintaining the tree invariant that
    /// not every descendant leaf is `Deep` — an all-`Deep` subtree must
    /// be represented as [`Self::deep`] instead. In debug builds this is
    /// checked via `debug_assert!`.
    pub(crate) fn internal(expansion: PlaceExpansion<'tcx, Box<InitialisationTree<'tcx>>>) -> Self {
        debug_assert!(
            !children_of(&expansion).iter().all(|t| t.is_fully_deep()),
            "InitialisationTree::internal called with an all-Deep subtree; \
             collapse to InitialisationTree::deep() instead",
        );
        Self::Internal(expansion)
    }

    /// Returns `true` iff every leaf in this subtree is `Deep`.
    pub(crate) fn is_fully_deep(&self) -> bool {
        match self {
            Self::Leaf(cap) => cap.is_deep(),
            Self::Internal(expansion) => children_of(expansion).iter().all(|t| t.is_fully_deep()),
        }
    }

    /// Returns `true` iff every leaf in this subtree is `Uninit`.
    #[allow(dead_code)]
    pub(crate) fn is_fully_uninit(&self) -> bool {
        match self {
            Self::Leaf(cap) => cap.is_uninit(),
            Self::Internal(expansion) => children_of(expansion).iter().all(|t| t.is_fully_uninit()),
        }
    }
}

/// Collect the children sub-trees stored as per-child data in a
/// [`PlaceExpansion`].
fn children_of<'tcx, 'a>(
    expansion: &'a PlaceExpansion<'tcx, Box<InitialisationTree<'tcx>>>,
) -> Vec<&'a InitialisationTree<'tcx>> {
    match expansion {
        PlaceExpansion::Fields(fields) => fields.values().map(|(_, t)| t.as_ref()).collect(),
        PlaceExpansion::Deref(t)
        | PlaceExpansion::Guided(
            RepackGuide::Downcast(_, _, t)
            | RepackGuide::ConstantIndex(_, t)
            | RepackGuide::Index(_, t)
            | RepackGuide::Subslice { data: t, .. },
        ) => vec![t.as_ref()],
        PlaceExpansion::Guided(RepackGuide::Default(never)) => match *never {},
    }
}

impl<'tcx> InitialisationTree<'tcx> {
    /// Pointwise join per
    /// <https://prusti.github.io/pcg-docs/owned-state.html#join-algorithm>:
    ///
    /// ```text
    /// join(leaf(s1), leaf(s2))   = leaf(min(s1, s2))
    /// join(leaf(S), internal(n)) = leaf(S)
    /// join(leaf(U), internal(n)) = leaf(U)
    /// join(leaf(D), internal(n)) = internal(n)
    /// join(internal(m), internal(n)) = internal pointwise on children
    /// ```
    ///
    /// If two internal nodes have structurally incompatible expansions,
    /// the join falls back to `leaf(Uninit)`: the place could be in
    /// either of two different partially-initialised shapes, so the only
    /// sound join is to treat it as uninitialised.
    pub(crate) fn join(&self, other: &Self) -> JoinOutcome<'tcx> {
        let joined = join_inner(self, other);
        let changed = &joined != self;
        JoinOutcome {
            tree: joined,
            changed,
        }
    }
}

fn join_inner<'tcx>(
    lhs: &InitialisationTree<'tcx>,
    rhs: &InitialisationTree<'tcx>,
) -> InitialisationTree<'tcx> {
    use InitialisationTree::{Internal, Leaf};
    match (lhs, rhs) {
        (Leaf(a), Leaf(b)) => Leaf((*a).min(*b)),
        (Leaf(OwnedCapability::Uninit), Internal(_))
        | (Internal(_), Leaf(OwnedCapability::Uninit)) => Leaf(OwnedCapability::Uninit),
        (Leaf(OwnedCapability::Shallow), Internal(_))
        | (Internal(_), Leaf(OwnedCapability::Shallow)) => Leaf(OwnedCapability::Shallow),
        (Leaf(OwnedCapability::Deep), other @ Internal(_))
        | (other @ Internal(_), Leaf(OwnedCapability::Deep)) => other.clone(),
        (Internal(lhs_exp), Internal(rhs_exp)) => match join_expansions(lhs_exp, rhs_exp) {
            Some(joined_exp) => {
                if children_of(&joined_exp).iter().all(|t| t.is_fully_deep()) {
                    Leaf(OwnedCapability::Deep)
                } else {
                    Internal(joined_exp)
                }
            }
            None => Leaf(OwnedCapability::Uninit),
        },
    }
}

type BoxedSubtree<'tcx> = Box<InitialisationTree<'tcx>>;

/// Pointwise-join two [`PlaceExpansion`]s that carry sub-trees as their
/// per-child data. Returns `None` if the two expansions are structurally
/// incompatible.
fn join_expansions<'tcx>(
    lhs: &PlaceExpansion<'tcx, BoxedSubtree<'tcx>>,
    rhs: &PlaceExpansion<'tcx, BoxedSubtree<'tcx>>,
) -> Option<PlaceExpansion<'tcx, BoxedSubtree<'tcx>>> {
    use PlaceExpansion::{Deref, Fields, Guided};
    match (lhs, rhs) {
        (Fields(a), Fields(b)) => {
            if a.len() != b.len() {
                return None;
            }
            let mut out = BTreeMap::new();
            for ((lk, (lty, lt)), (rk, (rty, rt))) in a.iter().zip(b.iter()) {
                if lk != rk || lty != rty {
                    return None;
                }
                out.insert(*lk, (*lty, Box::new(join_inner(lt, rt))));
            }
            Some(Fields(out))
        }
        (Deref(lt), Deref(rt)) => Some(Deref(Box::new(join_inner(lt, rt)))),
        (Guided(a), Guided(b)) => join_guides(a, b).map(Guided),
        _ => None,
    }
}

fn join_guides<'tcx>(
    lhs: &RepackGuide<crate::rustc_interface::middle::mir::Local, BoxedSubtree<'tcx>, !>,
    rhs: &RepackGuide<crate::rustc_interface::middle::mir::Local, BoxedSubtree<'tcx>, !>,
) -> Option<RepackGuide<crate::rustc_interface::middle::mir::Local, BoxedSubtree<'tcx>, !>> {
    match (lhs, rhs) {
        (RepackGuide::Default(never), _) | (_, RepackGuide::Default(never)) => match *never {},
        (RepackGuide::Downcast(ls, lv, lt), RepackGuide::Downcast(rs, rv, rt))
            if ls == rs && lv == rv =>
        {
            Some(RepackGuide::Downcast(
                *ls,
                *lv,
                Box::new(join_inner(lt, rt)),
            ))
        }
        (RepackGuide::ConstantIndex(lc, lt), RepackGuide::ConstantIndex(rc, rt)) if lc == rc => {
            Some(RepackGuide::ConstantIndex(
                *lc,
                Box::new(join_inner(lt, rt)),
            ))
        }
        (RepackGuide::Index(ll, lt), RepackGuide::Index(rl, rt)) if ll == rl => {
            Some(RepackGuide::Index(*ll, Box::new(join_inner(lt, rt))))
        }
        (
            RepackGuide::Subslice {
                from: lf,
                to: lt_,
                from_end: le,
                data: ld,
            },
            RepackGuide::Subslice {
                from: rf,
                to: rt_,
                from_end: re,
                data: rd,
            },
        ) if lf == rf && lt_ == rt_ && le == re => Some(RepackGuide::Subslice {
            from: *lf,
            to: *lt_,
            from_end: *le,
            data: Box::new(join_inner(ld, rd)),
        }),
        _ => None,
    }
}

impl Debug for InitialisationTree<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Leaf(cap) => write!(f, "{cap:?}"),
            Self::Internal(expansion) => write!(f, "{expansion:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Tree = InitialisationTree<'static>;

    fn leaf(c: OwnedCapability) -> Tree {
        Tree::Leaf(c)
    }

    /// A `Deref` internal node with the given sub-tree. Deref expansions
    /// don't require a tcx context, so they're the cheapest way to
    /// exercise the internal/leaf interactions.
    fn deref_internal(sub: Tree) -> Tree {
        Tree::internal(PlaceExpansion::Deref(Box::new(sub)))
    }

    #[test]
    #[should_panic(expected = "all-Deep subtree")]
    #[cfg(debug_assertions)]
    fn internal_rejects_all_deep_descendants() {
        let _ = Tree::internal(PlaceExpansion::Deref(Box::new(leaf(OwnedCapability::Deep))));
    }

    #[test]
    fn join_two_leaves_takes_minimum() {
        use OwnedCapability::*;
        assert_eq!(leaf(Deep).join(&leaf(Uninit)).tree, leaf(Uninit));
        assert_eq!(leaf(Deep).join(&leaf(Shallow)).tree, leaf(Shallow));
        assert_eq!(leaf(Shallow).join(&leaf(Uninit)).tree, leaf(Uninit));
        assert_eq!(leaf(Deep).join(&leaf(Deep)).tree, leaf(Deep));
    }

    #[test]
    fn join_uninit_with_internal_gives_uninit() {
        use OwnedCapability::*;
        let internal = deref_internal(leaf(Uninit));
        assert_eq!(leaf(Uninit).join(&internal).tree, leaf(Uninit));
        assert_eq!(internal.join(&leaf(Uninit)).tree, leaf(Uninit));
    }

    #[test]
    fn join_shallow_with_internal_gives_shallow() {
        use OwnedCapability::*;
        let internal = deref_internal(leaf(Uninit));
        assert_eq!(leaf(Shallow).join(&internal).tree, leaf(Shallow));
    }

    #[test]
    fn join_deep_with_internal_preserves_internal() {
        use OwnedCapability::*;
        let internal = deref_internal(leaf(Uninit));
        assert_eq!(leaf(Deep).join(&internal).tree, internal);
    }

    #[test]
    fn join_internal_derefs_pointwise() {
        use OwnedCapability::*;
        let lhs = deref_internal(leaf(Uninit));
        let rhs = deref_internal(leaf(Shallow));
        // Deref(U) join Deref(S) = Deref(min(U, S)) = Deref(U). The
        // result is not all-Deep, so it stays internal.
        assert_eq!(lhs.join(&rhs).tree, deref_internal(leaf(Uninit)));
    }

    #[test]
    fn join_collapses_to_deep_leaf_when_every_child_deep() {
        use OwnedCapability::*;
        // The constructor rejects all-Deep children, so build the raw
        // variant to exercise the collapse path in `join`.
        let lhs_raw = InitialisationTree::Internal(PlaceExpansion::Deref(Box::new(leaf(Deep))));
        let rhs_raw = InitialisationTree::Internal(PlaceExpansion::Deref(Box::new(leaf(Deep))));
        assert_eq!(lhs_raw.join(&rhs_raw).tree, leaf(Deep));
    }

    #[test]
    fn join_outcome_reports_changed_flag() {
        use OwnedCapability::*;
        let lhs = leaf(Deep);
        let rhs = leaf(Uninit);
        let outcome = lhs.join(&rhs);
        assert!(outcome.changed);
        assert_eq!(outcome.tree, leaf(Uninit));

        let lhs2 = leaf(Uninit);
        let outcome2 = lhs2.join(&rhs);
        assert!(!outcome2.changed);
        assert_eq!(outcome2.tree, leaf(Uninit));
    }
}
