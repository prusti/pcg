// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::marker::PhantomData;

use crate::{
    DebugDataTypes, PcgDataTypes, RepackDataTypes, Weaken,
    pcg::edge::EdgeMutability,
    rustc_interface::middle::mir::{self, PlaceElem},
    utils::PlaceLike,
};

use crate::{
    pcg::PositiveCapability,
    rustc_interface::{VariantIdx, span::Symbol},
    utils::{
        CompilerCtxt, ConstantIndex, DebugRepr, HasCompilerCtxt, Place,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
    },
};
use serde_derive::Serialize;

pub(crate) type RequiredGuide = RepackGuide<mir::Local, (), !>;

impl From<RequiredGuide> for RepackGuide {
    fn from(val: RequiredGuide) -> Self {
        match val {
            RepackGuide::Default(_) => RepackGuide::Default(()),
            RepackGuide::Downcast(downcast, _) => RepackGuide::Downcast(downcast, ()),
            RepackGuide::ConstantIndex(constant_index, _) => {
                RepackGuide::ConstantIndex(constant_index, ())
            }
            RepackGuide::Index(local, _) => RepackGuide::Index(local, ()),
            RepackGuide::Subslice {
                from,
                to,
                from_end,
                data,
            } => RepackGuide::Subslice {
                from,
                to,
                from_end,
                data: (),
            },
        }
    }
}

impl Default for RepackGuide {
    fn default() -> Self {
        RepackGuide::Default(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum RepackGuide<Local = mir::Local, D = (), Default = ()> {
    Default(Default),
    Downcast(Downcast, D),
    ConstantIndex(ConstantIndex, D),
    Index(Local, D),
    Subslice {
        from: u64,
        to: u64,
        from_end: bool,
        data: D,
    },
}

#[cfg(feature = "type-export")]
impl ts_rs::TS for RepackGuide {
    type WithoutGenerics = RepackGuide;

    type OptionInnerType = RepackGuide;

    fn name(cfg: &ts_rs::Config) -> String {
        todo!()
    }

    fn inline(cfg: &ts_rs::Config) -> String {
        todo!()
    }
}

impl serde::Serialize for RepackGuide {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(format!("{self:?}").as_str())
    }
}

impl<'tcx, D, Default: Copy> RepackGuide<mir::Local, D, Default> {
    pub(crate) fn try_map_data<'slf, R>(
        &'slf self,
        f: impl Fn(&'slf D) -> Option<R>,
    ) -> Option<RepackGuide<mir::Local, R, Default>> {
        match self {
            RepackGuide::Index(local, data) => Some(RepackGuide::Index(*local, f(data)?)),
            RepackGuide::Downcast(downcast, data) => {
                Some(RepackGuide::Downcast(*downcast, f(data)?))
            }
            RepackGuide::ConstantIndex(constant_index, data) => {
                Some(RepackGuide::ConstantIndex(*constant_index, f(data)?))
            }
            RepackGuide::Subslice {
                from,
                to,
                from_end,
                data,
            } => Some(RepackGuide::Subslice {
                from: *from,
                to: *to,
                from_end: *from_end,
                data: f(data)?,
            }),
            RepackGuide::Default(other) => Some(RepackGuide::Default(*other)),
        }
    }

    pub(crate) fn as_non_default(&self) -> Option<RequiredGuide> {
        match self {
            RepackGuide::Default(_) => None,
            RepackGuide::Index(local, _) => Some(RepackGuide::Index(*local, ())),
            RepackGuide::Downcast(downcast, _) => Some(RepackGuide::Downcast(*downcast, ())),
            RepackGuide::ConstantIndex(constant_index, _) => {
                Some(RepackGuide::ConstantIndex(*constant_index, ()))
            }
            RepackGuide::Subslice {
                from, to, from_end, ..
            } => Some(RepackGuide::Subslice {
                from: *from,
                to: *to,
                from_end: *from_end,
                data: (),
            }),
        }
    }

    pub(crate) fn map_data<'slf, R>(
        &'slf self,
        f: impl Fn(&'slf D) -> R,
    ) -> RepackGuide<mir::Local, R, Default> {
        match self {
            RepackGuide::Index(local, data) => RepackGuide::Index(*local, f(data)),
            RepackGuide::Downcast(downcast, data) => RepackGuide::Downcast(*downcast, f(data)),
            RepackGuide::ConstantIndex(constant_index, data) => {
                RepackGuide::ConstantIndex(*constant_index, f(data))
            }
            RepackGuide::Subslice {
                from,
                to,
                from_end,
                data,
            } => RepackGuide::Subslice {
                from: *from,
                to: *to,
                from_end: *from_end,
                data: f(data),
            },
            RepackGuide::Default(other) => RepackGuide::Default(*other),
        }
    }

    pub(crate) fn elem_data_mut(&mut self) -> (PlaceElem<'tcx>, &mut D) {
        match self {
            RepackGuide::Index(local, data) => (PlaceElem::Index(*local), data),
            RepackGuide::Downcast(downcast, data) => (
                PlaceElem::Downcast(downcast.symbol, downcast.variant_idx),
                data,
            ),
            RepackGuide::ConstantIndex(constant_index, data) => (
                PlaceElem::ConstantIndex {
                    offset: constant_index.offset,
                    min_length: constant_index.min_length,
                    from_end: constant_index.from_end,
                },
                data,
            ),
            RepackGuide::Subslice {
                from,
                to,
                from_end,
                data,
            } => (
                PlaceElem::Subslice {
                    from: *from,
                    to: *to,
                    from_end: *from_end,
                },
                data,
            ),
            RepackGuide::Default(_) => todo!(),
        }
    }
    pub(crate) fn without_data(&self) -> RepackGuide<mir::Local, (), Default> {
        self.map_data(|_| ())
    }
    pub(crate) fn elem_data(&self) -> (PlaceElem<'tcx>, &D) {
        match self {
            RepackGuide::Index(local, data) => (PlaceElem::Index(*local), data),
            RepackGuide::Downcast(downcast, data) => (
                PlaceElem::Downcast(downcast.symbol, downcast.variant_idx),
                data,
            ),
            RepackGuide::ConstantIndex(constant_index, data) => (
                PlaceElem::ConstantIndex {
                    offset: constant_index.offset,
                    min_length: constant_index.min_length,
                    from_end: constant_index.from_end,
                },
                data,
            ),
            RepackGuide::Subslice {
                from,
                to,
                from_end,
                data,
            } => (
                PlaceElem::Subslice {
                    from: *from,
                    to: *to,
                    from_end: *from_end,
                },
                data,
            ),
            RepackGuide::Default(_) => todo!(),
        }
    }
}

impl<Default: Clone + Eq + std::fmt::Debug> RepackGuide<mir::Local, (), Default> {
    fn downcast(symbol: Option<Symbol>, variant_idx: VariantIdx) -> Self {
        Self::Downcast(
            Downcast {
                symbol,
                variant_idx,
            },
            (),
        )
    }
    fn constant_index(offset: u64, min_length: u64, from_end: bool) -> Self {
        Self::ConstantIndex(
            ConstantIndex {
                offset,
                min_length,
                from_end,
            },
            (),
        )
    }

    fn subslice(from: u64, to: u64, from_end: bool) -> Self {
        Self::Subslice {
            from,
            to,
            from_end,
            data: (),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) struct Downcast {
    pub(crate) symbol: Option<Symbol>,
    pub(crate) variant_idx: VariantIdx,
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for RepackGuide {
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            match self {
                RepackGuide::Index(local, _) => {
                    format!("index with local {}", (*local).display_string(ctxt))
                }
                _ => format!("{self:?}"),
            }
            .into(),
        )
    }
}

impl From<RequiredGuide> for PlaceElem<'_> {
    fn from(val: RequiredGuide) -> Self {
        match val {
            RepackGuide::Index(local, _) => PlaceElem::Index(local),
            RepackGuide::Downcast(downcast, _) => {
                PlaceElem::Downcast(downcast.symbol, downcast.variant_idx)
            }
            RepackGuide::ConstantIndex(constant_index, _) => PlaceElem::ConstantIndex {
                offset: constant_index.offset,
                min_length: constant_index.min_length,
                from_end: constant_index.from_end,
            },
            RepackGuide::Subslice {
                from, to, from_end, ..
            } => PlaceElem::Subslice { from, to, from_end },
        }
    }
}

impl From<PlaceElem<'_>> for RepackGuide {
    fn from(elem: PlaceElem<'_>) -> Self {
        match elem {
            PlaceElem::Index(local) => RepackGuide::Index(local, ()),
            PlaceElem::Downcast(symbol, variant_idx) => RepackGuide::downcast(symbol, variant_idx),
            PlaceElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => RepackGuide::constant_index(offset, min_length, from_end),
            PlaceElem::Subslice { from, to, from_end } => RepackGuide::subslice(from, to, from_end),
            _ => RepackGuide::Default(()),
        }
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "type-export", ts(concrete(Place=String,Guide=String)))]
pub struct RepackExpand<
    'tcx,
    Place = crate::utils::Place<'tcx>,
    Guide = RepackGuide,
    Capability = EdgeMutability,
> {
    pub(crate) from: Place,
    pub(crate) guide: Guide,
    pub(crate) mutability: Capability,
    #[serde(skip)]
    _marker: PhantomData<&'tcx ()>,
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DebugRepr<Ctxt> for RepackExpand<'tcx> {
    type Repr = RepackExpand<'static, String, String>;
    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr {
        RepackExpand {
            from: self.from.display_string(ctxt),
            guide: self.guide.display_string(ctxt),
            mutability: self.mutability,
            _marker: PhantomData,
        }
    }
}

impl<'tcx> RepackExpand<'tcx> {
    pub(crate) fn new(
        from: Place<'tcx>,
        guide: RepackGuide,
        edge_mutability: EdgeMutability,
    ) -> Self {
        Self {
            from,
            guide,
            mutability: edge_mutability,
            _marker: PhantomData,
        }
    }

    #[must_use]
    pub fn mutability(&self) -> EdgeMutability {
        self.mutability
    }

    #[must_use]
    pub fn from(&self) -> Place<'tcx> {
        self.from
    }

    #[must_use]
    pub fn guide(&self) -> RepackGuide {
        self.guide
    }

    pub(crate) fn local(&self) -> mir::Local {
        self.from.local
    }

    pub fn target_places<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> Vec<Place<'tcx>>
    where
        'tcx: 'a,
    {
        let expansion = self.from.expansion(self.guide, ctxt);
        self.from.expansion_places(&expansion, ctxt).unwrap()
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "type-export", ts(concrete(Guide=String)))]
pub struct RepackCollapse<'tcx, P = crate::utils::Place<'tcx>, Guide = RepackGuide> {
    pub(crate) to: P,
    pub(crate) capability: PositiveCapability,
    pub(crate) guide: Guide,
    #[serde(skip)]
    _marker: PhantomData<&'tcx ()>,
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DebugRepr<Ctxt> for RepackCollapse<'tcx> {
    type Repr = RepackCollapse<'static, String, String>;
    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr {
        RepackCollapse {
            to: self.to.display_string(ctxt),
            capability: self.capability,
            guide: self.guide.display_string(ctxt),
            _marker: PhantomData,
        }
    }
}

impl<'tcx> RepackCollapse<'tcx> {
    pub(crate) fn new(to: Place<'tcx>, capability: PositiveCapability, guide: RepackGuide) -> Self {
        Self {
            to,
            capability,
            guide,
            _marker: PhantomData,
        }
    }

    #[must_use]
    pub fn guide(self) -> RepackGuide {
        self.guide
    }

    #[must_use]
    pub fn box_deref_place(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Option<Place<'tcx>> {
        if self.to.ty(ctxt).ty.is_box() {
            self.to.project_elem(PlaceElem::Deref, ctxt).ok()
        } else {
            None
        }
    }

    #[must_use]
    pub fn to(&self) -> Place<'tcx> {
        self.to
    }

    #[must_use]
    pub fn capability(&self) -> PositiveCapability {
        self.capability
    }

    pub(crate) fn local(&self) -> mir::Local {
        self.to.local
    }
}

#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
pub struct PcgRepackOpDataTypes<'tcx, P = Place<'tcx>, ExpandCapability = EdgeMutability>(
    PhantomData<&'tcx (P, ExpandCapability)>,
);

impl<'tcx, P, E> Eq for PcgRepackOpDataTypes<'tcx, P, E> {}

impl<'tcx, P, E> PartialEq for PcgRepackOpDataTypes<'tcx, P, E> {
    fn eq(&self, other: &Self) -> bool {
        true
    }
}

impl<'tcx, P, E> Clone for PcgRepackOpDataTypes<'tcx, P, E> {
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<P, E> std::fmt::Debug for PcgRepackOpDataTypes<'_, P, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PcgRepackOpDataTypes")
    }
}

impl<'tcx, P: std::fmt::Debug, E> PcgDataTypes<'tcx> for PcgRepackOpDataTypes<'tcx, P, E> {
    type Place = P;
}

impl<'tcx, P: std::fmt::Debug, E> RepackDataTypes<'tcx> for PcgRepackOpDataTypes<'tcx, P, E> {}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
#[serde(tag = "type", content = "data")]
#[cfg_attr(feature = "type-export", ts(concrete(D=PcgRepackOpDataTypes<'tcx>)))]
pub enum RepackOp<'tcx, D: RepackDataTypes<'tcx> = PcgRepackOpDataTypes<'tcx>> {
    /// Rust will sometimes join two `BasicBlocks` where a local is live in one and dead in the other.
    /// Our analysis will join these two into a state where the local is dead, and this Op marks the
    /// edge from where it was live.
    ///
    /// This is not an issue in the MIR since it generally has a
    /// [`mir::StatementKind::StorageDead`](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.StatementKind.html#variant.StorageDead)
    /// right after the merge point, which is fine in Rust semantics, since
    /// [`mir::StatementKind::StorageDead`](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.StatementKind.html#variant.StorageDead)
    /// is a no-op if the local is already (conditionally) dead.
    ///
    /// This Op only appears for edges between basic blocks. It is often emitted for edges to panic
    /// handling blocks, but can also appear in regular code for example in the MIR of
    /// [this function](https://github.com/dtolnay/syn/blob/3da56a712abf7933b91954dbfb5708b452f88504/src/attr.rs#L623-L628).
    StorageDead(D::Local),
    /// This Op only appears within a `BasicBlock` and is attached to a
    /// [`mir::StatementKind::StorageDead`](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.StatementKind.html#variant.StorageDead)
    /// statement. We emit it for any such statement where the local may already be dead. We
    /// guarantee to have inserted a [`RepackOp::StorageDead`] before this Op so that one can
    /// safely ignore the statement this is attached to.
    IgnoreStorageDead(D::Local),
    /// Instructs that the current capability to the place (first [`CapabilityKind`]) should
    /// be weakened to the second given capability. We guarantee that `_.1 > _.2`.
    ///
    /// This Op is used prior to a [`RepackOp::Collapse`] to ensure that all packed up places have
    /// the same capability. It can also appear at basic block join points, where one branch has
    /// a weaker capability than the other.
    Weaken(Weaken<'tcx, D::Place, PositiveCapability, PositiveCapability>),
    /// Instructs that one should unpack `place` with the capability.
    /// We guarantee that the current state holds exactly the given capability for the given place.
    /// `guide` denotes e.g. the enum variant to unpack to. One can use
    /// [`Place::expand_one_level(_.0, _.1, ..)`](Place::expand_one_level) to get the set of all
    /// places (except as noted in the documentation for that fn) which will be obtained by unpacking.
    Expand(RepackExpand<'tcx, D::Place, D::RepackGuide, D::ExpandCapability>),
    /// Instructs that one should pack up `place` with the given capability.
    /// `guide` denotes e.g. the enum variant to pack from. One can use
    /// [`Place::expand_one_level(_.0, _.1, ..)`](Place::expand_one_level) to get the set of all
    /// places which should be packed up. We guarantee that the current state holds exactly the
    /// given capability for all places in this set.
    Collapse(RepackCollapse<'tcx, D::Place, D::RepackGuide>),
    /// TODO
    DerefShallowInit(D::Place, D::Place),
    /// This place should have its capability changed from `Lent` (for mutably
    /// borrowed places) or `Read` (for shared borrow places), to the given
    /// capability, because it is no longer lent out.
    RegainLoanedCapability(RegainedCapability<D::Place>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
pub struct RegainedCapability<Place> {
    pub(crate) place: Place,
    #[cfg_attr(
        feature = "type-export",
        ts(
            as = "crate::pcg::capabilities::capability_kind::debug_reprs::PositiveCapabilityDebugRepr"
        )
    )]
    pub(crate) capability: PositiveCapability,
}

impl<Place> RegainedCapability<Place> {
    pub fn new(place: Place, capability: PositiveCapability) -> Self {
        Self { place, capability }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DebugRepr<Ctxt>
    for RegainedCapability<Place<'tcx>>
{
    type Repr = RegainedCapability<String>;
    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr {
        RegainedCapability {
            place: self.place.display_string(ctxt),
            capability: self.capability,
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DebugRepr<Ctxt> for RepackOp<'tcx> {
    type Repr = RepackOp<'static, DebugDataTypes>;
    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr {
        match self {
            RepackOp::StorageDead(local) => RepackOp::StorageDead(local.display_string(ctxt)),
            RepackOp::IgnoreStorageDead(local) => {
                RepackOp::IgnoreStorageDead(local.display_string(ctxt))
            }
            RepackOp::RegainLoanedCapability(regained_capability) => {
                RepackOp::RegainLoanedCapability(regained_capability.debug_repr(ctxt))
            }
            RepackOp::Weaken(weaken) => RepackOp::Weaken(weaken.debug_repr(ctxt)),
            RepackOp::Expand(expand) => RepackOp::Expand(expand.debug_repr(ctxt)),
            RepackOp::Collapse(collapse) => RepackOp::Collapse(collapse.debug_repr(ctxt)),
            RepackOp::DerefShallowInit(place, place2) => {
                RepackOp::DerefShallowInit(place.display_string(ctxt), place2.display_string(ctxt))
            }
        }
    }
}

impl<'tcx, Ctxt: Copy, D: RepackDataTypes<'tcx>> DisplayWithCtxt<Ctxt> for RepackOp<'tcx, D>
where
    D::Place: DisplayWithCtxt<Ctxt>,
    D::ExpandCapability: DisplayWithCtxt<Ctxt>,
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            match self {
                RepackOp::RegainLoanedCapability(regained_capability) => {
                    format!(
                        "Restore capability {:?} to {}",
                        regained_capability.capability,
                        regained_capability.place.display_string(ctxt),
                    )
                }
                RepackOp::Expand(expand) => format!(
                    "unpack {} with capability {}",
                    expand.from.display_string(ctxt),
                    expand.mutability.display_output(ctxt, mode).into_text()
                ),
                _ => format!("{self:?}"),
            }
            .into(),
        )
    }
}

impl<'tcx, D: RepackDataTypes<'tcx>> RepackOp<'tcx, D> {
    pub(crate) fn expand<'a>(
        from: D::Place,
        guide: D::RepackGuide,
        for_cap: D::ExpandCapability,
        _ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self {
        // Note that we might generate expand annotations with `Write` capability for
        // the `bridge` operation to generate annotations between basic blocks.
        Self::Expand(RepackExpand {
            from,
            guide,
            mutability: for_cap,
            _marker: PhantomData,
        })
    }
}

impl<'tcx> RepackOp<'tcx> {
    pub(crate) fn weaken(
        place: Place<'tcx>,
        from: PositiveCapability,
        to: PositiveCapability,
    ) -> Self {
        Self::Weaken(Weaken::new(place, from, to))
    }

    #[must_use]
    pub fn affected_place(&self) -> Place<'tcx> {
        match *self {
            RepackOp::StorageDead(local) | RepackOp::IgnoreStorageDead(local) => local.into(),
            RepackOp::Weaken(Weaken { place, .. })
            | RepackOp::Collapse(RepackCollapse { to: place, .. })
            | RepackOp::Expand(RepackExpand { from: place, .. })
            | RepackOp::RegainLoanedCapability(RegainedCapability { place, .. })
            | RepackOp::DerefShallowInit(place, _) => place,
        }
    }
}
