use crate::pcg::PCGNode;
use crate::rustc_interface::data_structures::fx::FxHashSet;
use crate::utils::PlaceRepacker;

use super::borrow_pcg_edge::{BlockedNode, LocalNode};

/// A trait for data that represents a hyperedge in the Borrow PCG.
pub trait EdgeData<'tcx> {
    /// For an edge A -> B, this returns the set of nodes A. In general, the capabilities
    /// of nodes B are obtained from these nodes.
    fn blocked_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>>;

    /// For an edge A -> B, this returns the set of nodes B. In general, these nodes
    /// obtain their capabilities from the nodes A.
    fn blocked_by_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>>;

    fn blocks_node(&self, node: BlockedNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.blocked_nodes(repacker).contains(&node)
    }

    fn is_blocked_by(&self, node: LocalNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.blocked_by_nodes(repacker).contains(&node)
    }
}

#[macro_export]
macro_rules! edgedata_enum {
    (
        $enum_name:ident < $tcx:lifetime >,
        $( $variant_name:ident($inner_type:ty) ),+ $(,)?
    ) => {
        impl<$tcx> $crate::borrow_pcg::edge_data::EdgeData<$tcx> for $enum_name<$tcx> {
            fn blocked_nodes(&self, repacker: PlaceRepacker<'_, $tcx>) -> FxHashSet<PCGNode<'tcx>> {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocked_nodes(repacker),
                    )+
                }
            }

            fn blocked_by_nodes(&self, repacker: PlaceRepacker<'_, $tcx>) -> FxHashSet<$crate::borrow_pcg::borrow_pcg_edge::LocalNode<'tcx>> {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocked_by_nodes(repacker),
                    )+
                }
            }

            fn blocks_node(&self, node: BlockedNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool { match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocks_node(node, repacker),
                    )+
                }
            }

            fn is_blocked_by(&self, node: LocalNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool { match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.is_blocked_by(node, repacker),
                    )+
                }
            }

        }

        $(
            impl<$tcx> From<$inner_type> for $enum_name<$tcx> {
                fn from(inner: $inner_type) -> Self {
                    $enum_name::$variant_name(inner)
                }
            }
        )+

        impl<$tcx> $crate::borrow_pcg::has_pcs_elem::MakePlaceOld<$tcx> for $enum_name<$tcx> {
            fn make_place_old(
                &mut self,
                place: $crate::utils::Place<'tcx>,
                latest: &$crate::borrow_pcg::latest::Latest<'tcx>,
                repacker: PlaceRepacker<'_, 'tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.make_place_old(place, latest, repacker),
                    )+
                }
            }
        }

        impl<$tcx> $crate::borrow_pcg::has_pcs_elem::LabelRegionProjection<$tcx> for $enum_name<$tcx> {
            fn label_region_projection(
                &mut self,
                projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
                location: $crate::utils::SnapshotLocation,
                repacker: PlaceRepacker<'_, 'tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.label_region_projection(projection, location, repacker),
                    )+
                }
            }
        }

        impl<$tcx> HasValidityCheck<$tcx> for $enum_name<$tcx> {
            fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.check_validity(repacker),
                    )+
                }
            }
        }

        impl<$tcx> DisplayWithRepacker<$tcx> for $enum_name<$tcx> {
            fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.to_short_string(repacker),
                    )+
                }
            }
        }

        impl<'tcx, T> HasPcgElems<T> for $enum_name<$tcx>
            where
                $(
                    $inner_type: HasPcgElems<T>,
                )+
            {
                fn pcg_elems(&mut self) -> Vec<&mut T> {
                    match self {
                        $(
                            $enum_name::$variant_name(inner) => inner.pcg_elems(),
                        )+
                    }
                }
            }
    }
}
