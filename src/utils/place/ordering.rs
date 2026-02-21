use crate::rustc_interface::middle::mir::{PlaceElem, ProjectionElem};
use crate::rustc_interface::data_structures::fx::FxHasher;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

use crate::utils::Place;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PlaceOrdering {
    // For example `x.f` to `x.f.g`.
    Prefix,
    // For example `x.f` and `x.f`.
    Equal,
    // For example `x.f.g` to `x.f`.
    Suffix,
    // Both places share a common prefix, but are not related by prefix or suffix.
    // For example `x.f` and `x.h`
    Both,
}

impl PlaceOrdering {
    #[must_use]
    pub fn is_eq(self) -> bool {
        matches!(self, PlaceOrdering::Equal)
    }
    #[must_use]
    pub fn is_prefix(self) -> bool {
        matches!(self, PlaceOrdering::Prefix)
    }
    #[must_use]
    pub fn is_suffix(self) -> bool {
        matches!(self, PlaceOrdering::Suffix)
    }
    #[must_use]
    pub fn is_both(self) -> bool {
        matches!(self, PlaceOrdering::Both)
    }
}

impl From<Ordering> for PlaceOrdering {
    fn from(ordering: Ordering) -> Self {
        match ordering {
            Ordering::Less => PlaceOrdering::Prefix,
            Ordering::Equal => PlaceOrdering::Equal,
            Ordering::Greater => PlaceOrdering::Suffix,
        }
    }
}
impl From<PlaceOrdering> for Option<Ordering> {
    fn from(ordering: PlaceOrdering) -> Self {
        match ordering {
            PlaceOrdering::Prefix => Some(Ordering::Less),
            PlaceOrdering::Equal => Some(Ordering::Equal),
            PlaceOrdering::Suffix => Some(Ordering::Greater),
            PlaceOrdering::Both => None,
        }
    }
}

impl<'tcx> Place<'tcx> {
    /// Check if the place `left` is a prefix of `right` or vice versa. For example:
    ///
    /// +   `partial_cmp(x.f, y.f) == None`
    /// +   `partial_cmp(x.f, x.g) == None`
    /// +   `partial_cmp(x.f, x.f) == Some(Equal)`
    /// +   `partial_cmp(x.f.g, x.f) == Some(Suffix)`
    /// +   `partial_cmp(x.f, x.f.g) == Some(Prefix)`
    /// +   `partial_cmp(x as None, x as Some.0) == Some(Both)`
    ///
    /// The ultimate question this answers is: are the two places mutually
    /// exclusive (i.e. can we have both or not)?
    /// For example, all of the following are mutually exclusive:
    ///  - `x` and `x.f`
    ///  - `(x as Ok).0` and `(x as Err).0`
    ///  - `x[_1]` and `x[_2]`
    ///  - `x[2 of 11]` and `x[5 of 14]`
    ///
    /// But the following are not:
    ///  - `x` and `y`
    ///  - `x.f` and `x.g.h`
    ///  - `x[3 of 6]` and `x[4 of 6]`
    pub(crate) fn partial_cmp(self, right: Self) -> Option<PlaceOrdering> {
        if self.local != right.local {
            return None;
        }
        let diff = self.compare_projections(right).find(|(eq, _, _)| !eq);
        if let Some((_, left, right)) = diff {
            use ProjectionElem::{ConstantIndex, Downcast, Field, Index, OpaqueCast, Subslice};
            fn is_index(elem: PlaceElem<'_>) -> bool {
                matches!(elem, Index(_) | ConstantIndex { .. } | Subslice { .. })
            }
            match (left, right) {
                (Field(..), Field(..)) => None,
                (
                    ConstantIndex {
                        min_length: l,
                        from_end: lfe,
                        ..
                    },
                    ConstantIndex {
                        min_length: r,
                        from_end: rfe,
                        ..
                    },
                ) if r == l && lfe == rfe => None,
                (Downcast(_, _), Downcast(_, _)) | (OpaqueCast(_), OpaqueCast(_)) => {
                    Some(PlaceOrdering::Both)
                }
                (left, right) if is_index(left) && is_index(right) => Some(PlaceOrdering::Both),
                diff => unreachable!("Unexpected diff: {diff:?}"),
            }
        } else {
            Some(self.projection.len().cmp(&right.projection.len()).into())
        }
    }

    /// Check if the place `self` is a prefix of `place`. For example:
    ///
    /// +   `is_prefix(x.f, x.f) == true`
    /// +   `is_prefix(x.f, x.f.g) == true`
    /// +   `is_prefix(x.f.g, x.f) == false`
    pub(crate) fn is_prefix_of(self, place: Self) -> bool {
        Self::partial_cmp(self, place)
            .is_some_and(|o| o == PlaceOrdering::Equal || o == PlaceOrdering::Prefix)
    }

    pub(crate) fn is_strict_prefix_of(self, place: Self) -> bool {
        self != place && self.is_prefix_of(place)
    }

    /// Check if the place `self` is an exact prefix of `place`. For example:
    ///
    /// +   `is_prefix(x.f, x.f) == false`
    /// +   `is_prefix(x.f, x.f.g) == true`
    /// +   `is_prefix(x.f, x.f.g.h) == false`
    #[must_use]
    pub fn is_prefix_exact(self, place: Self) -> bool {
        self.0.projection.len() + 1 == place.0.projection.len()
            && Self::partial_cmp(self, place).is_some_and(|o| o == PlaceOrdering::Prefix)
    }

    /// Returns `true` if either of the places can reach the other
    /// with a series of expand/collapse operations. Note that
    /// both operations are allowed and so e.g.
    /// `related_to`(`_1[_4]`, `_1[_3]`) == true
    #[must_use]
    pub fn related_to(self, right: Self) -> bool {
        self.partial_cmp(right).is_some()
    }

    pub(crate) fn compare_projections(
        self,
        other: Self,
    ) -> impl Iterator<Item = (bool, PlaceElem<'tcx>, PlaceElem<'tcx>)> {
        let left = self.projection.iter().copied();
        let right = other.projection.iter().copied();
        left.zip(right).map(|(e1, e2)| (elem_eq((e1, e2)), e1, e2))
    }
}

fn elem_eq<'tcx>(to_cmp: (PlaceElem<'tcx>, PlaceElem<'tcx>)) -> bool {
    use ProjectionElem::{Downcast, Field};
    match to_cmp {
        (Field(left, _), Field(right, _)) => left == right,
        (Downcast(_, left), Downcast(_, right)) => left == right,
        (left, right) => left == right,
    }
}

impl PartialEq for Place<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.local == other.local
            && self.projection.len() == other.projection.len()
            && self.compare_projections(*other).all(|(eq, _, _)| eq)
    }
}
impl Eq for Place<'_> {}

impl PartialOrd for Place<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Place<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        if self == other {
            Ordering::Equal
        } else {
            let mut h1 = FxHasher::default();
            let mut h2 = FxHasher::default();
            self.hash(&mut h1);
            other.hash(&mut h2);
            match h1.finish().cmp(&h2.finish()) {
                Ordering::Equal => {
                    panic!("Places have same hash, but they aren't equal!")
                }
                other => other,
            }
        }
    }

}

pub trait PrefixRelation {
    fn is_prefix_of(self, other: Self) -> bool;
    fn is_strict_prefix_of(self, other: Self) -> bool;
}

impl PrefixRelation for Place<'_> {
    fn is_prefix_of(self, other: Self) -> bool {
        self.is_prefix_of(other)
    }
    fn is_strict_prefix_of(self, other: Self) -> bool {
        self.is_strict_prefix_of(other)
    }
}
