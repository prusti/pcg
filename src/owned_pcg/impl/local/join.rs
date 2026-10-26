use crate::{
    DebugLines,
    action::{BorrowPcgAction, OwnedPcgAction, PcgAction},
    borrow_pcg::{action::LabelPlaceReason, state::BorrowsStateLike},
    error::PcgError,
    owned_pcg::{
        ExpandedPlace, LocalExpansions, RepackExpand, RepackOp,
        join::{
            data::JoinOwnedData,
            obtain::{JoinCtxt, JoinObtainer},
        },
    },
    pcg::{
        CapabilityKind,
        obtain::PlaceCollapser,
        place_capabilities::{PlaceCapabilitiesInterface, PlaceCapabilitiesReader},
    },
    pcg_validity_assert,
    utils::{
        self, HasBorrowCheckerCtxt, Place, data_structures::HashSet,
        display::DisplayWithCompilerCtxt,
    },
};

enum JoinDifferentExpansionsResult<'tcx> {
    ExpandedForRead(Box<PcgAction<'tcx>>),
    ExpandedForNoCapability,
    Collapsed(Vec<PcgAction<'tcx>>),
}

impl<'tcx> JoinDifferentExpansionsResult<'tcx> {
    fn actions(self) -> Vec<PcgAction<'tcx>> {
        match self {
            JoinDifferentExpansionsResult::ExpandedForRead(action) => vec![*action],
            JoinDifferentExpansionsResult::ExpandedForNoCapability => vec![],
            JoinDifferentExpansionsResult::Collapsed(actions) => actions,
        }
    }
}

enum JoinExpandedPlaceResult<'tcx> {
    JoinedWithSameExpansion(Vec<PcgAction<'tcx>>),
    CreatedExpansion(Vec<PcgAction<'tcx>>),
    JoinedWithOtherExpansions(JoinDifferentExpansionsResult<'tcx>),
    CollapsedOtherExpansion(Vec<PcgAction<'tcx>>),
}

impl<'tcx> JoinExpandedPlaceResult<'tcx> {
    fn actions(self) -> Vec<PcgAction<'tcx>> {
        match self {
            JoinExpandedPlaceResult::JoinedWithSameExpansion(actions)
            | JoinExpandedPlaceResult::CreatedExpansion(actions)
            | JoinExpandedPlaceResult::CollapsedOtherExpansion(actions) => actions,
            JoinExpandedPlaceResult::JoinedWithOtherExpansions(result) => result.actions(),
        }
    }

    fn performed_collapse(&self) -> bool {
        matches!(
            self,
            JoinExpandedPlaceResult::JoinedWithOtherExpansions(
                JoinDifferentExpansionsResult::Collapsed(_)
            ) | JoinExpandedPlaceResult::CollapsedOtherExpansion(_)
        )
    }
}

impl<'pcg, 'a: 'pcg, 'tcx> JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>> {
    fn join_different_expansions_from_place<'other>(
        &mut self,
        other: &mut JoinOwnedData<'a, 'pcg, 'tcx, &'other mut LocalExpansions<'tcx>>,
        other_expansion: &ExpandedPlace<'tcx>,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) -> Result<JoinDifferentExpansionsResult<'tcx>, PcgError>
    where
        'pcg: 'other,
        'tcx: 'a,
    {
        let base_place = other_expansion.place;
        let self_cap = self.capabilities.get(base_place, ctxt);
        let other_cap = other.capabilities.get(base_place, ctxt);
        if self_cap == Some(CapabilityKind::Read) && other_cap == Some(CapabilityKind::Read) {
            let action = self.expand(
                RepackExpand::new(base_place, other_expansion.guide(), CapabilityKind::Read),
                ctxt,
            );
            Ok(JoinDifferentExpansionsResult::ExpandedForRead(Box::new(
                action,
            )))
        } else if other
            .owned
            .contains_descendent_leaf_node_without_capability(base_place, other.capabilities, ctxt)
        {
            // If this case holds, the leaf node is exclusively borrowed.
            // We want to insert this expansion (and all further expansions), without any capabilities
            tracing::debug!(
                "Other expansions contain a descendent leaf node without capability for place {}",
                base_place.display_string(ctxt)
            );
            self.owned
                .insert_expansion(other_expansion.place, other_expansion.expansion.clone());
            Ok(JoinDifferentExpansionsResult::ExpandedForNoCapability)
        } else {
            let mut self_obtainer = JoinObtainer {
                ctxt,
                data: self,
                actions: vec![],
            };

            // The capability of the place should be Write because presumably something
            // was moved out in either of the expansions.
            self_obtainer.collapse_owned_places_and_lifetime_projections_to(
                base_place,
                CapabilityKind::Write,
                format!(
                    "Join: collapse owned places {}",
                    other_expansion.place.display_string(ctxt)
                ),
                ctxt,
            )?;

            pcg_validity_assert!(
                self_obtainer.data.capabilities.get(base_place, ctxt)
                    == Some(CapabilityKind::Write),
                "Expected capability for {} to be Write",
                base_place.display_string(ctxt)
            );

            let mut other_obtainer = JoinObtainer {
                ctxt,
                data: other,
                actions: vec![],
            };

            other_obtainer.collapse_owned_places_and_lifetime_projections_to(
                base_place,
                CapabilityKind::Write,
                format!(
                    "Join: collapse owned places {}",
                    other_expansion.place.display_string(ctxt)
                ),
                ctxt,
            )?;

            Ok(JoinDifferentExpansionsResult::Collapsed(
                self_obtainer.actions,
            ))
        }
    }

    fn expand_from_place_with_caps(
        &mut self,
        other: &JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        expansion: &ExpandedPlace<'tcx>,
        self_cap: CapabilityKind,
        other_cap: CapabilityKind,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) -> Vec<PcgAction<'tcx>> {
        let place = expansion.place;
        let guide = expansion.guide();
        pcg_validity_assert!(!self.owned.contains_expansion_from(place));
        if let Some(expand_cap) = self_cap.minimum(other_cap) {
            tracing::debug!(
                "Expanding from place {} with cap {:?}",
                place.display_string(ctxt),
                expand_cap
            );
            let mut actions = vec![self.expand(RepackExpand::new(place, guide, expand_cap), ctxt)];
            actions.extend(self.join_all_places_in_expansion(other, expansion, ctxt));
            actions
        } else if self_cap == CapabilityKind::Read {
            pcg_validity_assert!(other_cap == CapabilityKind::Write);
            tracing::debug!(
                "No join expansion from place {}",
                place.display_string(ctxt)
            );
            let actions = self.join_leaf_read_and_write_capabilities(other, place, ctxt);
            pcg_validity_assert!(!actions.is_empty());
            actions
        } else if self_cap == CapabilityKind::Write && other_cap == CapabilityKind::Read {
            self.join_write_leaf_with_read_expansion(other, place, ctxt);
            vec![]
        } else {
            vec![]
        }
    }

    /// Joins `place`, a leaf with [`CapabilityKind::Write`] in `self`, with
    /// the read-only expansion of `place` in `other`.
    ///
    /// Neither capability is available on both paths, so the joined place
    /// retains the expansion of `other` (whose places may be blocked by
    /// borrows from that path) without any capability.
    fn join_write_leaf_with_read_expansion(
        &mut self,
        other: &JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        place: Place<'tcx>,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) {
        tracing::debug!(
            "Joining write leaf {} with read expansion to no capability",
            place.display_string(ctxt)
        );
        for expansion in other.owned.expansions() {
            if place.is_prefix_of(expansion.place) {
                self.owned
                    .insert_expansion(expansion.place, expansion.expansion.clone());
            }
        }
        self.capabilities.remove_all_postfixes(place, ctxt);
    }

    fn join_all_places_in_expansion(
        &mut self,
        other: &JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        expansion: &ExpandedPlace<'tcx>,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) -> Vec<PcgAction<'tcx>> {
        let mut actions = vec![];
        for expansion_place in expansion.expansion_places(ctxt).unwrap() {
            actions.extend(self.join_owned_places(other, expansion_place, ctxt));
        }
        actions
    }

    /// See <https://prusti.github.io/pcg-docs/join.html#local-expansions-join--joine>
    fn join_other_expanded_place(
        &mut self,
        other: &mut JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        other_expansion: &ExpandedPlace<'tcx>,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) -> Result<JoinExpandedPlaceResult<'tcx>, PcgError> {
        tracing::debug!("Joining expansion: {other_expansion:?}");
        let place = other_expansion.place;
        let self_expansions = self
            .owned
            .expansions_from(place)
            .cloned()
            .collect::<HashSet<_>>();
        if self_expansions.contains(other_expansion) {
            let mut actions = vec![];
            // The other side's expansion is a read expansion of a frozen place.
            if other.capabilities.get(place, ctxt) == Some(CapabilityKind::Read)
                && self.capabilities.get(place, ctxt).is_none()
            {
                actions.push(self.apply(
                    BorrowPcgAction::freeze(place, "join with a read expansion"),
                    ctxt,
                ));
            }
            // If some of our expansions have leafs, we want to merge with the other ones
            // for example, to propagate read caps from the other borrowed places to our own
            actions.extend(self.join_all_places_in_expansion(other, other_expansion, ctxt));
            Ok(JoinExpandedPlaceResult::JoinedWithSameExpansion(actions))
        } else if self_expansions.is_empty()
            && let Some(self_cap) = self.capabilities.get(place, ctxt)
        {
            let other_cap = other.capabilities.get(place, ctxt);
            tracing::debug!("Self cap: {self_cap:?}, Other cap: {other_cap:?}");
            if let Some(other_cap) = other_cap {
                Ok(JoinExpandedPlaceResult::CreatedExpansion(
                    self.expand_from_place_with_caps(
                        other,
                        other_expansion,
                        self_cap,
                        other_cap,
                        ctxt,
                    ),
                ))
            } else if other_expansion.is_enum_expansion() {
                // The other expansion is a downcast to a variant that is
                // presumably borrowed or partially-moved (see 206_issue_77.rs).
                // It won't survive the join, so collapse it, emitting the
                // operations: leaves with capability greater than write are weakened
                // first, so that the emitted collape guarantees
                // that all packed-up places hold exactly its capability.
                let weakened = other
                    .capabilities
                    .owned_capabilities(place.local, ctxt)
                    .filter(|(p, k)| place.is_prefix_of(*p) && **k > CapabilityKind::Write)
                    .map(|(p, _)| p)
                    .collect::<Vec<_>>();
                let mut ops = weakened
                    .into_iter()
                    .map(|p| other.weaken_to_write(p, "join with a collapsed variant", ctxt))
                    .collect::<Vec<_>>();
                ops.extend(
                    other
                        .owned
                        .collapse(place, Some(CapabilityKind::Write), other.capabilities, ctxt)
                        .into_iter()
                        .map(Into::into),
                );
                Ok(JoinExpandedPlaceResult::CollapsedOtherExpansion(ops))
            } else {
                // We might as well just expand our place
                Ok(JoinExpandedPlaceResult::CreatedExpansion(vec![
                    self.expand(
                        RepackExpand::new(place, other_expansion.guide(), self_cap),
                        ctxt,
                    ),
                ]))
            }
        } else {
            Ok(JoinExpandedPlaceResult::JoinedWithOtherExpansions(
                self.join_different_expansions_from_place(other, other_expansion, ctxt)?,
            ))
        }
    }

    fn visit_each_other_expansion_iteration(
        &mut self,
        other: &mut JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) -> Result<Vec<PcgAction<'tcx>>, PcgError> {
        let expansions_shortest_first = other
            .owned
            .expansions_shortest_first()
            .cloned()
            .collect::<Vec<_>>();
        let mut actions: Vec<PcgAction<'tcx>> = vec![];
        let mut collapsed_places: HashSet<Place<'tcx>> = HashSet::default();
        for other_expansion in expansions_shortest_first {
            if collapsed_places
                .iter()
                .any(|p| p.is_prefix_of(other_expansion.place))
            {
                continue;
            }
            let result = self.join_other_expanded_place(other, &other_expansion, ctxt)?;
            let performed_collapse = result.performed_collapse();
            if performed_collapse {
                collapsed_places.insert(other_expansion.place);
            }
            actions.extend(result.actions());
        }
        Ok(actions)
    }

    fn visit_each_other_expansion(
        &mut self,
        mut other: JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) -> Result<Vec<PcgAction<'tcx>>, PcgError> {
        let mut actions = vec![];
        let mut iteration = 0;
        loop {
            iteration += 1;
            tracing::debug!("Iteration {iteration}");
            let iteration_actions = self.visit_each_other_expansion_iteration(&mut other, ctxt)?;
            if iteration_actions.is_empty() {
                break;
            }
            actions.extend(iteration_actions);
        }
        Ok(actions)
    }

    fn render_debug_graph<'slf>(
        &'slf self,
        comment: &str,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) where
        'tcx: 'slf,
        'tcx: 'a,
    {
        self.borrows.graph.render_debug_graph(
            self.snapshot_location.location().block,
            Some(utils::DebugImgcat::JoinOwned),
            self.capabilities,
            comment,
            ctxt.bc_ctxt(),
        );
    }

    fn join_leaf_read_and_write_capabilities(
        &mut self,
        other: &JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        place: Place<'tcx>,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) -> Vec<PcgAction<'tcx>> {
        pcg_validity_assert!(self.owned.is_leaf_place(place, ctxt));
        pcg_validity_assert!(other.owned.is_leaf_place(place, ctxt));
        pcg_validity_assert!(self.capabilities.get(place, ctxt) == Some(CapabilityKind::Read));
        pcg_validity_assert!(other.capabilities.get(place, ctxt) == Some(CapabilityKind::Write));
        let mut actions = vec![self.apply(
            BorrowPcgAction::label_place_and_update_related_capabilities(
                place,
                self.snapshot_location,
                LabelPlaceReason::JoinOwnedReadAndWriteCapabilities,
            ),
            ctxt,
        )];
        // This side's freeze has ended and the value it still holds is
        // dropped by the join (the other side moved it out): the place is
        // unfrozen and then weakened, so consumers see an ordinary value drop.
        actions.push(self.apply(
            BorrowPcgAction::unfreeze(place, "join with a moved-out place"),
            ctxt,
        ));
        actions.push(self.weaken_to_write(place, "join with a moved-out place", ctxt));
        actions
    }

    /// Performs `expand` and returns it with its capability changes.
    fn expand(&mut self, expand: RepackExpand<'tcx>, ctxt: JoinCtxt<'a, 'tcx>) -> PcgAction<'tcx> {
        let changes = self
            .owned
            .perform_expand_action(expand, self.capabilities, ctxt);
        OwnedPcgAction::new(RepackOp::Expand(expand), None)
            .with_capabilities(changes)
            .into()
    }

    /// Applies `action` and returns it with its capability changes.
    fn apply(
        &mut self,
        mut action: BorrowPcgAction<'tcx>,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) -> PcgAction<'tcx> {
        self.borrows
            .apply_action(&mut action, self.capabilities, ctxt);
        action.into()
    }

    fn weaken_to_write(
        &mut self,
        place: Place<'tcx>,
        context: &str,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) -> PcgAction<'tcx> {
        let from = self.capabilities.get(place, ctxt).unwrap();
        self.apply(
            BorrowPcgAction::weaken(place, from, CapabilityKind::Write, context.to_owned()),
            ctxt,
        )
    }

    pub(crate) fn join_owned_places(
        &mut self,
        other: &JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        place: Place<'tcx>,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) -> Vec<PcgAction<'tcx>> {
        if !self.owned.is_leaf_place(place, ctxt) || !other.owned.is_leaf_place(place, ctxt) {
            return vec![];
        }
        let Some(self_cap) = self.capabilities.get(place, ctxt) else {
            return vec![];
        };
        let Some(other_cap) = other.capabilities.get(place, ctxt) else {
            return vec![];
        };
        match (self_cap, other_cap) {
            (CapabilityKind::Exclusive, CapabilityKind::Read) => vec![self.apply(
                BorrowPcgAction::freeze(place, "join with a frozen place"),
                ctxt,
            )],
            (CapabilityKind::Read, CapabilityKind::Write) => {
                self.join_leaf_read_and_write_capabilities(other, place, ctxt)
            }
            (CapabilityKind::Exclusive, CapabilityKind::Write) => {
                for (p, c) in other
                    .capabilities
                    .capabilities_for_strict_postfixes_of(place)
                {
                    self.capabilities.insert(p, c, ctxt);
                }
                vec![]
            }
            (CapabilityKind::ShallowExclusive, CapabilityKind::Write) => {
                // A reference lent through on this side but moved out on the
                // other: the joined state can only be Write. Preserve the
                // predecessor's value with a label before emitting the
                // weaken; outstanding borrows still refer to that value.
                vec![
                    self.apply(
                        BorrowPcgAction::label_place_and_update_related_capabilities(
                            place,
                            self.snapshot_location,
                            LabelPlaceReason::JoinOwnedReadAndWriteCapabilities,
                        ),
                        ctxt,
                    ),
                    self.weaken_to_write(place, "join with a moved-out reference", ctxt),
                ]
            }
            (
                CapabilityKind::Read
                | CapabilityKind::Write
                | CapabilityKind::Exclusive
                | CapabilityKind::ShallowExclusive,
                _,
            ) => vec![],
        }
    }

    pub(crate) fn join(
        mut self,
        mut other: JoinOwnedData<'a, 'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        ctxt: JoinCtxt<'a, 'tcx>,
    ) -> Result<Vec<PcgAction<'tcx>>, PcgError> {
        let mut actions: Vec<PcgAction<'tcx>> = Vec::new();
        if self.owned.has_expansions() || other.owned.has_expansions() {
            actions.extend(
                other
                    .reborrow()
                    .visit_each_other_expansion(self.reborrow(), ctxt)?,
            );
            self.render_debug_graph("Self After join_expansions (other)", ctxt);
            other.render_debug_graph("Other After join_expansions (other)", ctxt);
            actions.extend(
                self.reborrow()
                    .visit_each_other_expansion(other.reborrow(), ctxt)?,
            );
            self.render_debug_graph("Self After join_expansions (self)", ctxt);
            other.render_debug_graph("Other After join_expansions (self)", ctxt);
        } else {
            let place = Place::from(self.owned.get_local());
            actions.extend(self.reborrow().join_owned_places(&other, place, ctxt));
            actions.extend(other.join_owned_places(&self, place, ctxt));
        }
        tracing::debug!(
            "Join {} actions:\n\t{}",
            Place::from(self.owned.get_local()).display_string(ctxt),
            actions
                .iter()
                .map(|action| action.debug_line(ctxt))
                .collect::<Vec<_>>()
                .join("\n\t")
        );
        tracing::debug!(
            "Capabilities:\n\t{}",
            self.capabilities.debug_lines(ctxt).join("\n\t")
        );
        Ok(actions)
    }
}

impl<'tcx> LocalExpansions<'tcx> {
    fn contains_descendent_leaf_node_without_capability<'a>(
        &self,
        place: Place<'tcx>,
        place_capabilities: &impl PlaceCapabilitiesInterface<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.leaf_places(ctxt).into_iter().any(|p| {
            let p_place: Place<'tcx> = p.into();
            if place.is_prefix_of(p_place) && place_capabilities.get(p_place, ctxt).is_none() {
                tracing::debug!(
                    "Place {} is a leaf node without capability",
                    p.display_string(ctxt)
                );
                true
            } else {
                false
            }
        })
    }
}
