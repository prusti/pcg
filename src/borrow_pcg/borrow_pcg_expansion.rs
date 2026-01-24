//! Definition of expansion edges in the Borrow PCG.
use std::{collections::BTreeMap, hash::Hash};

use derive_more::{From, TryFrom};
use itertools::Itertools;

use super::{
    borrow_pcg_edge::{BlockedNode, BlockingNode, LocalNode},
    edge_data::EdgeData,
    has_pcs_elem::LabelLifetimeProjection,
    region_projection::LifetimeProjectionLabel,
};
use crate::{
    borrow_pcg::{
        borrow_pcg_expansion::internal::BorrowPcgExpansionData,
        edge::kind::BorrowPcgEdgeType,
        edge_data::{
            LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate, NodeReplacement,
            conditionally_label_places, edgedata_enum,
        },
        has_pcs_elem::{
            LabelLifetimeProjectionResult, LabelNodeContext, LabelPlace, PlaceLabeller,
            SourceOrTarget,
        },
        region_projection::{LifetimeProjection, LocalLifetimeProjection},
    },
    error::{PcgError, PcgUnsupportedError},
    r#loop::PlaceUsageType,
    owned_pcg::RepackGuide,
    pcg::{
        CapabilityKind, LocalNodeLike, MaybeHasLocation, PcgNode, PcgNodeLike, SymbolicCapability,
        obtain::ObtainType,
        place_capabilities::{BlockType, PlaceCapabilitiesReader},
    },
    pcg_validity_assert,
    rustc_interface::{
        FieldIdx,
        middle::{mir::PlaceElem, ty},
    },
    utils::{
        CompilerCtxt, DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasPlace, PcgNodeComponent,
        PcgPlace, Place, PlaceLike, PlaceProjectable, PrefixRelation,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        place::{corrected::CorrectedPlace, maybe_old::MaybeLabelledPlace},
        validity::HasValidityCheck,
    },
};

/// The projections resulting from an expansion of a place.
///
/// This representation is preferred to a `Vec<PlaceElem>` because it ensures
/// it enables a more reasonable notion of equality between expansions. Directly
/// storing the place elements in a `Vec` could lead to different representations
/// for the same expansion, e.g. `{*x.f.a, *x.f.b}` and `{*x.f.b, *x.f.a}`.
#[derive(PartialEq, Eq, Clone, Debug, Hash, From)]
pub enum PlaceExpansion<'tcx> {
    /// Fields from e.g. a struct or tuple, e.g. `{*x.f} -> {*x.f.a, *x.f.b}`
    /// Note that for region projections, not every field of the base type may
    /// be included. For example consider the following:
    /// ```ignore
    /// struct S<'a, 'b> { x: &'a mut i32, y: &'b mut i32 }
    ///
    /// let s: S<'a, 'b> = S { x: &mut 1, y: &mut 2 };
    /// ```
    /// The projection of `s↓'a` contains only `{s.x↓'a}` because nothing under
    /// `'a` is accessible via `s.y`.
    Fields(BTreeMap<FieldIdx, ty::Ty<'tcx>>),
    /// See [`PlaceElem::Deref`]
    Deref,
    Guided(RepackGuide),
}

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for PlaceExpansion<'tcx> {
    fn check_validity(&self, _ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl<'tcx> PlaceExpansion<'tcx> {
    pub(crate) fn is_enum_expansion(&self) -> bool {
        matches!(self, PlaceExpansion::Guided(RepackGuide::Downcast(_, _)))
    }
    pub(crate) fn block_type<'a>(
        &self,
        base_place: Place<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> BlockType
    where
        'tcx: 'a,
    {
        if matches!(
            obtain_type,
            ObtainType::Capability(CapabilityKind::Read)
                | ObtainType::TwoPhaseExpand
                | ObtainType::LoopInvariant {
                    usage_type: PlaceUsageType::Read,
                    ..
                }
        ) {
            BlockType::Read
        } else if matches!(self, PlaceExpansion::Deref) {
            if base_place.is_shared_ref(ctxt) {
                BlockType::DerefSharedRef
            } else if base_place.is_mut_ref(ctxt) {
                if base_place.projects_shared_ref(ctxt) {
                    BlockType::DerefMutRefUnderSharedRef
                } else {
                    BlockType::DerefMutRefForExclusive
                }
            } else {
                BlockType::Other
            }
        } else {
            BlockType::Other
        }
    }
    pub(crate) fn guide(&self) -> Option<RepackGuide> {
        match self {
            PlaceExpansion::Guided(guide) => Some(*guide),
            _ => None,
        }
    }

    pub(crate) fn from_places<'a>(
        places: Vec<Place<'tcx>>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self
    where
        'tcx: 'a,
    {
        let mut fields = BTreeMap::new();

        for place in places {
            let corrected_place = CorrectedPlace::new(place, ctxt);
            let last_projection = corrected_place.last_projection();
            if let Some(elem) = last_projection {
                match *elem {
                    PlaceElem::Field(field_idx, ty) => {
                        fields.insert(field_idx, ty);
                    }
                    PlaceElem::Deref => return PlaceExpansion::Deref,
                    other => {
                        let repack_guide: RepackGuide = other
                            .try_into()
                            .unwrap_or_else(|_| todo!("unsupported place elem: {:?}", other));
                        return PlaceExpansion::Guided(repack_guide);
                    }
                }
            }
        }

        if !fields.is_empty() {
            PlaceExpansion::Fields(fields)
        } else {
            unreachable!()
        }
    }

    pub(crate) fn elems(&self) -> Vec<PlaceElem<'tcx>> {
        match self {
            PlaceExpansion::Fields(fields) => fields
                .iter()
                .sorted_by_key(|(idx, _)| *idx)
                .map(|(idx, ty)| PlaceElem::Field(*idx, *ty))
                .collect(),
            PlaceExpansion::Deref => vec![PlaceElem::Deref],
            PlaceExpansion::Guided(RepackGuide::ConstantIndex(c)) => {
                let mut elems = vec![(*c).into()];
                elems.extend(c.other_elems());
                elems
            }
            PlaceExpansion::Guided(guided) => vec![(*guided).into()],
        }
    }
}

pub(crate) mod internal {
    use crate::owned_pcg::RepackGuide;

    /// An *expansion* of a place (e.g *x -> {*x.f, *x.g}) or region projection
    /// (e.g. {x↓'a} -> {x.f↓'a, x.g↓'a}) where the expanded part is in the Borrow
    /// PCG.
    #[derive(PartialEq, Eq, Clone, Debug, Hash)]
    pub struct BorrowPcgExpansionData<Node> {
        pub(crate) base: Node,
        pub(crate) expansion: Vec<Node>,
        pub(crate) guide: Option<RepackGuide>,
    }
}

pub type BorrowPcgPlaceExpansion<'tcx, P = Place<'tcx>> =
    BorrowPcgExpansionData<MaybeLabelledPlace<'tcx, P>>;

impl<'tcx, Ctxt, P> LabelEdgeLifetimeProjections<'tcx, Ctxt, P>
    for BorrowPcgPlaceExpansion<'tcx, P>
{
    fn label_lifetime_projections(
        &mut self,
        _predicate: &LabelNodePredicate<'tcx, P>,
        _label: Option<LifetimeProjectionLabel>,
        _ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        LabelLifetimeProjectionResult::Unchanged
    }
}

pub(crate) type LifetimeProjectionExpansion<'tcx, P = Place<'tcx>> =
    BorrowPcgExpansionData<LocalLifetimeProjection<'tcx, P>>;

#[derive(Clone, Debug, Eq, PartialEq, Hash, TryFrom)]
pub enum BorrowPcgExpansion<'tcx, P = Place<'tcx>> {
    Place(BorrowPcgPlaceExpansion<'tcx, P>),
    LifetimeProjection(LifetimeProjectionExpansion<'tcx, P>),
}

edgedata_enum!(
    crate::borrow_pcg::borrow_pcg_expansion::BorrowPcgExpansion,
    BorrowPcgExpansion<'tcx, P>,
    Place(crate::borrow_pcg::borrow_pcg_expansion::BorrowPcgPlaceExpansion<'tcx, P>),
    LifetimeProjection(crate::borrow_pcg::borrow_pcg_expansion::LifetimeProjectionExpansion<'tcx, P>),
);

impl<'tcx, P: PcgNodeComponent> BorrowPcgExpansion<'tcx, P> {
    pub fn base(&self) -> LocalNode<'tcx, P> {
        match self {
            BorrowPcgExpansion::Place(expansion) => expansion.base.into(),
            BorrowPcgExpansion::LifetimeProjection(expansion) => {
                PcgNode::LifetimeProjection(expansion.base)
            }
        }
    }

    pub fn expansion(&self) -> Vec<LocalNode<'tcx, P>> {
        match self {
            BorrowPcgExpansion::Place(expansion) => {
                expansion.expansion.iter().map(|p| (*p).into()).collect()
            }
            BorrowPcgExpansion::LifetimeProjection(expansion) => expansion
                .expansion
                .iter()
                .map(|p| PcgNode::LifetimeProjection(*p))
                .collect(),
        }
    }
}

impl<'tcx> BorrowPcgExpansion<'tcx> {
    pub(crate) fn new_lifetime_projection_expansion<'a>(
        base: LifetimeProjection<'tcx, Place<'tcx>>,
        expansion: PlaceExpansion<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<Self, PcgError>
    where
        'tcx: 'a,
    {
        Ok(BorrowPcgExpansion::LifetimeProjection(
            BorrowPcgExpansionData::new(
                base.with_base(MaybeLabelledPlace::Current(base.base)),
                expansion,
                ctxt,
            )?,
        ))
    }
    pub(crate) fn new_place_expansion<'a>(
        base: Place<'tcx>,
        expansion: PlaceExpansion<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<Self, PcgError>
    where
        'tcx: 'a,
    {
        Ok(BorrowPcgExpansion::Place(BorrowPcgPlaceExpansion::new(
            base.into(),
            expansion,
            ctxt,
        )?))
    }
}

impl<
    'tcx,
    Ctxt: DebugCtxt + Copy,
    P: PcgPlace<'tcx, Ctxt>,
    Node: LocalNodeLike<'tcx, Ctxt, P> + LabelPlace<'tcx, Ctxt, P>,
> LabelEdgePlaces<'tcx, Ctxt, P> for BorrowPcgExpansionData<Node>
where
    Self: HasValidityCheck<Ctxt>,
{
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        conditionally_label_places(
            vec![&mut self.base],
            predicate,
            labeller,
            LabelNodeContext::new(
                SourceOrTarget::Source,
                BorrowPcgEdgeType::BorrowPcgExpansion,
            ),
            ctxt,
        )
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> HashSet<NodeReplacement<'tcx, P>> {
        let result = conditionally_label_places(
            self.expansion.iter_mut(),
            predicate,
            labeller,
            LabelNodeContext::new(
                SourceOrTarget::Target,
                BorrowPcgEdgeType::BorrowPcgExpansion,
            ),
            ctxt,
        );
        self.assert_validity(ctxt);
        result
    }
}

impl<'tcx, Ctxt: Copy, P: PcgPlace<'tcx, Ctxt>> LabelEdgeLifetimeProjections<'tcx, Ctxt, P>
    for LifetimeProjectionExpansion<'tcx, P>
where
    LocalLifetimeProjection<'tcx, P>: LabelLifetimeProjection<'tcx>,
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        let source_context = LabelNodeContext::new(
            SourceOrTarget::Source,
            BorrowPcgEdgeType::BorrowPcgExpansion,
        );
        let target_context = LabelNodeContext::new(
            SourceOrTarget::Target,
            BorrowPcgEdgeType::BorrowPcgExpansion,
        );
        let mut changed = LabelLifetimeProjectionResult::Unchanged;
        if predicate.applies_to(self.base.to_pcg_node(ctxt), source_context) {
            changed |= self.base.label_lifetime_projection(label);
        }
        for p in &mut self.expansion {
            if predicate.applies_to(p.to_pcg_node(ctxt), target_context) {
                changed |= p.label_lifetime_projection(label);
            }
        }
        changed
    }
}

impl<Ctxt: Copy, P: DisplayWithCtxt<Ctxt>> DisplayWithCtxt<Ctxt> for BorrowPcgExpansionData<P> {
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        let guide_part = if let Some(guide) = self.guide
            && matches!(mode, OutputMode::Test)
        {
            DisplayOutput::Text(format!(" (guide={guide:?})").into())
        } else {
            DisplayOutput::EMPTY
        };
        DisplayOutput::Seq(vec![
            DisplayOutput::Text(
                format!(
                    "{{{}}} -> {{{}}}",
                    self.base.display_string(ctxt),
                    self.expansion
                        .iter()
                        .map(|p| p.display_string(ctxt))
                        .join(", ")
                )
                .into(),
            ),
            guide_part,
        ])
    }
}

impl<'a, 'tcx: 'a, Ctxt: DebugCtxt + Copy + HasCompilerCtxt<'a, 'tcx>>
    HasValidityCheck<Ctxt> for BorrowPcgExpansionData<MaybeLabelledPlace<'tcx>>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        if self.expansion.contains(&self.base) {
            return Err(format!("expansion contains base: {self:?}"));
        }
        for p in &self.expansion {
            if let Some(PcgNode::Place(node)) = p.try_to_local_node(ctxt)
                && node.place().is_owned(ctxt)
            {
                return Err(format!(
                    "Expansion of {:?} contains owned place {}",
                    self,
                    node.place().display_string(ctxt)
                ));
            }
        }
        Ok(())
    }
}

impl<'a, 'tcx: 'a, Ctxt: DebugCtxt + Copy + HasCompilerCtxt<'a, 'tcx>>
    HasValidityCheck<Ctxt> for BorrowPcgExpansionData<LocalLifetimeProjection<'tcx>>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        if self.expansion.contains(&self.base) {
            return Err(format!("expansion contains base: {self:?}"));
        }
        for p in &self.expansion {
            let local_node: Option<LocalNode<'tcx>> = p.try_to_local_node(ctxt);
            if let Some(PcgNode::Place(node)) = local_node
                && node.place().is_owned(ctxt)
            {
                return Err(format!(
                    "Expansion of {:?} contains owned place {}",
                    self,
                    node.place().display_string(ctxt)
                ));
            }
        }
        Ok(())
    }
}

impl<
    'tcx,
    Ctxt: Copy,
    P: Eq + Copy + std::fmt::Debug + std::hash::Hash + 'tcx,
    Node: PartialEq + Copy + Into<LocalNode<'tcx, P>> + PcgNodeLike<'tcx, Ctxt, P>,
> EdgeData<'tcx, Ctxt, P> for BorrowPcgExpansionData<Node>
{
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx, P>, ctxt: Ctxt) -> bool {
        self.base.to_pcg_node(ctxt) == node
    }

    fn blocked_nodes<'slf>(
        &self,
        ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = BlockedNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(self.base.to_pcg_node(ctxt)))
    }

    fn blocked_by_nodes<'slf>(
        &'slf self,
        _ctxt: Ctxt,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx, P>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(self.expansion.iter().map(|p| (*p).into()))
    }
}

impl<'tcx> BorrowPcgExpansion<'tcx> {
    pub fn guide(&self) -> Option<RepackGuide> {
        match self {
            BorrowPcgExpansion::Place(place_expansion) => place_expansion.guide,
            BorrowPcgExpansion::LifetimeProjection(lifetime_projection_expansion) => {
                lifetime_projection_expansion.guide
            }
        }
    }

    /// Returns true iff the expansion is packable, i.e. without losing any
    /// information. This is the case when the expansion node labels (for
    /// places, and for region projections) are the same as the base node
    /// labels.
    pub(crate) fn is_packable(
        &self,
        capabilities: &impl PlaceCapabilitiesReader<'tcx, SymbolicCapability>,
        ctxt: impl HasCompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let BorrowPcgExpansion::Place(place_expansion) = self else {
            return false;
        };
        let mut fst_cap = None;
        place_expansion.expansion.iter().all(|p| {
            if let MaybeLabelledPlace::Current(place) = p {
                if let Some(cap) = fst_cap {
                    if cap != capabilities.get(*place, ctxt) {
                        return false;
                    }
                } else {
                    fst_cap = Some(capabilities.get(*place, ctxt));
                }
            }
            place_expansion.base.place().is_prefix_exact(p.place())
                && p.location() == place_expansion.base.location()
        })
    }
}

impl<'tcx, Node: PcgNodeComponent> BorrowPcgExpansionData<Node> {
    pub fn base(&self) -> Node {
        self.base
    }

    pub fn expansion(&self) -> &[Node] {
        &self.expansion
    }

    pub(crate) fn new<Ctxt: DebugCtxt + Copy, P: PlaceLike<'tcx, Ctxt> + DisplayWithCtxt<Ctxt>>(
        base: Node,
        expansion: PlaceExpansion<'tcx>,
        ctxt: Ctxt,
    ) -> Result<Self, PcgError>
    where
        Node: Ord + HasPlace<'tcx, P> + PlaceProjectable<'tcx, Ctxt>,
        Self: HasValidityCheck<Ctxt>,
    {
        if base.place().is_raw_ptr(ctxt) {
            return Err(PcgUnsupportedError::DerefUnsafePtr.into());
        }
        pcg_validity_assert!(
            !(base.is_place() && base.place().is_ref(ctxt) && expansion == PlaceExpansion::Deref),
            [ctxt],
            "Deref expansion of {} should be a Deref edge, not an expansion",
            base.place().display_string(ctxt)
        );
        let result = Self {
            base,
            guide: expansion.guide(),
            expansion: expansion
                .elems()
                .into_iter()
                .map(|elem| base.project_deeper(elem, ctxt))
                .collect::<Result<Vec<_>, _>>()?,
        };
        result.assert_validity(ctxt);
        Ok(result)
    }
}
