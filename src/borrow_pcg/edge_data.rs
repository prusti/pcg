use crate::{
    borrow_pcg::has_pcs_elem::{LabelNodeContext, PlaceLabeller},
    pcg::PcgNode,
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, Place,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
    },
};

use super::borrow_pcg_edge::{BlockedNode, LocalNode};

/// A trait for data that represents a hyperedge in the Borrow PCG.
pub trait EdgeData<'tcx> {
    /// For an edge A -> B, this returns the set of nodes A. In general, the capabilities
    /// of nodes B are obtained from these nodes.
    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf;

    /// For an edge A -> B, this returns the set of nodes B. In general, these nodes
    /// obtain their capabilities from the nodes A.
    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir;

    fn blocks_node(&self, node: BlockedNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.blocked_nodes(ctxt).any(|n| n == node)
    }

    fn is_blocked_by(&self, node: LocalNode<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.blocked_by_nodes(ctxt).any(|n| n == node)
    }

    fn nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(
            self.blocked_nodes(ctxt)
                .chain(self.blocked_by_nodes(ctxt).map(|n| n.into())),
        )
    }

    fn references_place(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.nodes(ctxt).any(|n| match n {
            PcgNode::Place(p) => p.as_current_place() == Some(place),
            PcgNode::LifetimeProjection(rp) => rp.base.as_current_place() == Some(place),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LabelPlacePredicate<'tcx> {
    /// Label only this exact place, not including any of its pre-or postfix places.
    Exact(Place<'tcx>),
    /// Label all places that (transitively) project from a postfix of `place`,
    /// including `place` itself. If `label_place_in_expansion` is `false`,
    /// then we would not label places e.g `place.foo` when `place.foo` is the
    /// child of a [`BorrowPcgExpansion`] or [`DerefEdge`].
    Postfix {
        place: Place<'tcx>,
        label_place_in_expansion: bool,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EdgePredicate {
    All,
    BorrowEdges,
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for LabelPlacePredicate<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            match self {
                LabelPlacePredicate::Postfix { place, .. } => {
                    place.display_string(ctxt) // As a hack for now so debug output doesn't change
                }
                LabelPlacePredicate::Exact(place) => {
                    format!("exact {}", place.display_string(ctxt))
                }
            }
            .into(),
        )
    }
}

impl<'tcx> LabelPlacePredicate<'tcx> {
    pub(crate) fn applies_to(
        &self,
        candidate: Place<'tcx>,
        label_context: LabelNodeContext,
        _ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self {
            LabelPlacePredicate::Postfix {
                place: predicate_place,
                label_place_in_expansion,
            } => {
                if candidate == *predicate_place
                    && label_context.is_place_node()
                    && label_context.is_target_of_expansion()
                {
                    *label_place_in_expansion
                } else {
                    predicate_place.is_prefix_of(candidate)
                }
            }
            LabelPlacePredicate::Exact(place) => *place == candidate,
        }
    }
}

pub trait LabelEdgePlaces<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;
}

macro_rules! edgedata_enum {
    (
        $enum_name:ident < $tcx:lifetime >,
        $( $variant_name:ident($inner_type:ty) ),+ $(,)?
    ) => {
        impl<$tcx> $crate::borrow_pcg::edge_data::EdgeData<$tcx> for $enum_name<$tcx> {
            fn blocked_nodes<'slf, BC: Copy>(
                &'slf self,
                ctxt: CompilerCtxt<'_, $tcx, BC>,
            ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
            where
                'tcx: 'slf,
            {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocked_nodes(ctxt),
                    )+
                }
            }

            fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
                &'slf self,
                ctxt: CompilerCtxt<'mir, $tcx, BC>,
            ) -> Box<dyn std::iter::Iterator<Item = $crate::borrow_pcg::borrow_pcg_edge::LocalNode<'tcx>> + 'slf>
            where
                'tcx: 'mir,
            {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocked_by_nodes(ctxt),
                    )+
                }
            }

            fn blocks_node<'slf>(
                &self,
                node: BlockedNode<'tcx>,
                ctxt: CompilerCtxt<'_, $tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.blocks_node(node, ctxt),
                    )+
                }
            }

            fn is_blocked_by<'slf>(
                &self,
                node: LocalNode<'tcx>,
                ctxt: CompilerCtxt<'_, $tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.is_blocked_by(node, ctxt),
                    )+
                }
            }
        }

        impl<$tcx> $crate::borrow_pcg::edge_data::LabelEdgePlaces<$tcx> for $enum_name<$tcx> {
            fn label_blocked_places(
                &mut self,
                predicate: &$crate::borrow_pcg::edge_data::LabelPlacePredicate<'tcx>,
                labeller: &impl $crate::borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx>,
                ctxt: CompilerCtxt<'_, 'tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.label_blocked_places(predicate, labeller, ctxt),
                    )+
                }
            }

            fn label_blocked_by_places(
                &mut self,
                predicate: &$crate::borrow_pcg::edge_data::LabelPlacePredicate<'tcx>,
                labeller: &impl $crate::borrow_pcg::has_pcs_elem::PlaceLabeller<'tcx>,
                ctxt: CompilerCtxt<'_, 'tcx>,
            ) -> bool {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.label_blocked_by_places(predicate, labeller, ctxt),
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

        impl<'a, $tcx> $crate::borrow_pcg::has_pcs_elem::LabelLifetimeProjection<'a, $tcx> for $enum_name<$tcx> {
            fn label_lifetime_projection(
                &mut self,
                predicate: &$crate::borrow_pcg::has_pcs_elem::LabelLifetimeProjectionPredicate<'tcx>,
                location: Option<$crate::borrow_pcg::region_projection::LifetimeProjectionLabel>,
                ctxt: CompilerCtxt<'a, 'tcx>,
            ) -> $crate::borrow_pcg::has_pcs_elem::LabelLifetimeProjectionResult {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.label_lifetime_projection(predicate, location, ctxt),
                    )+
                }
            }
        }

        impl<$tcx> HasValidityCheck<'_, $tcx> for $enum_name<$tcx> {
            fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.check_validity(ctxt),
                    )+
                }
            }
        }

        impl<'a, $tcx: 'a, Ctxt: $crate::HasBorrowCheckerCtxt<'a, $tcx>> $crate::utils::display::DisplayWithCtxt<Ctxt> for $enum_name<$tcx> {
            fn display_output(&self, ctxt: Ctxt, mode: $crate::utils::display::OutputMode) -> $crate::utils::display::DisplayOutput {
                match self {
                    $(
                        $enum_name::$variant_name(inner) => inner.display_output(ctxt, mode),
                    )+
                }
            }
        }
    }
}
pub(crate) use edgedata_enum;
