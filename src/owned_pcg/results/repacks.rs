// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::marker::PhantomData;

use crate::Weaken;
use crate::rustc_interface::middle::mir::{self, PlaceElem};

use crate::utils::DebugRepr;
use crate::{
    pcg::CapabilityKind,
    rustc_interface::{VariantIdx, span::Symbol},
    utils::{CompilerCtxt, ConstantIndex, HasCompilerCtxt, Place, display::DisplayWithCtxt},
};
use serde_derive::Serialize;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum RepackGuide<Local = mir::Local> {
    Downcast(Option<Symbol>, VariantIdx),
    ConstantIndex(ConstantIndex),
    Index(Local),
    Subslice { from: u64, to: u64, from_end: bool },
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for RepackGuide {
    fn display_string(&self, ctxt: Ctxt) -> String {
        match self {
            RepackGuide::Index(local) => {
                format!("index with local {}", (*local).display_string(ctxt))
            }
            _ => format!("{self:?}"),
        }
    }
}

impl From<RepackGuide> for PlaceElem<'_> {
    fn from(val: RepackGuide) -> Self {
        match val {
            RepackGuide::Index(local) => PlaceElem::Index(local),
            RepackGuide::Downcast(symbol, variant_idx) => PlaceElem::Downcast(symbol, variant_idx),
            RepackGuide::ConstantIndex(constant_index) => PlaceElem::ConstantIndex {
                offset: constant_index.offset,
                min_length: constant_index.min_length,
                from_end: constant_index.from_end,
            },
            RepackGuide::Subslice { from, to, from_end } => {
                PlaceElem::Subslice { from, to, from_end }
            }
        }
    }
}

impl TryFrom<PlaceElem<'_>> for RepackGuide {
    type Error = ();
    fn try_from(elem: PlaceElem<'_>) -> Result<Self, Self::Error> {
        match elem {
            PlaceElem::Index(local) => Ok(RepackGuide::Index(local)),
            PlaceElem::Downcast(symbol, variant_idx) => {
                Ok(RepackGuide::Downcast(symbol, variant_idx))
            }
            PlaceElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => Ok(RepackGuide::ConstantIndex(ConstantIndex {
                offset,
                min_length,
                from_end,
            })),
            PlaceElem::Subslice { from, to, from_end } => {
                Ok(RepackGuide::Subslice { from, to, from_end })
            }
            _ => Err(()),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
pub struct RepackExpand<'tcx, Place = crate::utils::Place<'tcx>, Guide = RepackGuide> {
    pub(crate) from: Place,
    pub(crate) guide: Option<Guide>,
    pub(crate) capability: CapabilityKind,
    #[serde(skip)]
    _marker: PhantomData<&'tcx ()>,
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DebugRepr<Ctxt> for RepackExpand<'tcx> {
    type Repr = RepackExpand<'static, String, String>;
    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr {
        RepackExpand {
            from: self.from.display_string(ctxt),
            guide: self.guide.map(|g| g.display_string(ctxt)),
            capability: self.capability,
            _marker: PhantomData,
        }
    }
}

impl<'tcx> RepackExpand<'tcx> {
    pub(crate) fn new(
        from: Place<'tcx>,
        guide: Option<RepackGuide>,
        capability: CapabilityKind,
    ) -> Self {
        Self {
            from,
            guide,
            capability,
            _marker: PhantomData,
        }
    }

    pub fn capability(&self) -> CapabilityKind {
        self.capability
    }

    pub fn from(&self) -> Place<'tcx> {
        self.from
    }

    pub fn guide(&self) -> Option<RepackGuide> {
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
#[cfg_attr(feature = "type-export", derive(specta::Type))]
pub struct RepackCollapse<'tcx, Place = crate::utils::Place<'tcx>, Guide = RepackGuide> {
    pub(crate) to: Place,
    pub(crate) capability: CapabilityKind,
    pub(crate) guide: Option<Guide>,
    #[serde(skip)]
    _marker: PhantomData<&'tcx ()>,
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DebugRepr<Ctxt> for RepackCollapse<'tcx> {
    type Repr = RepackCollapse<'static, String, String>;
    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr {
        RepackCollapse {
            to: self.to.display_string(ctxt),
            capability: self.capability,
            guide: self.guide.map(|g| g.display_string(ctxt)),
            _marker: PhantomData,
        }
    }
}

impl<'tcx> RepackCollapse<'tcx> {
    pub(crate) fn new(
        to: Place<'tcx>,
        capability: CapabilityKind,
        guide: Option<RepackGuide>,
    ) -> Self {
        Self {
            to,
            capability,
            guide,
            _marker: PhantomData,
        }
    }

    pub fn guide(self) -> Option<RepackGuide> {
        self.guide
    }

    pub fn box_deref_place(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Option<Place<'tcx>> {
        if self.to.ty(ctxt).ty.is_box() {
            self.to.project_deeper(PlaceElem::Deref, ctxt).ok()
        } else {
            None
        }
    }

    pub fn to(&self) -> Place<'tcx> {
        self.to
    }

    pub fn capability(&self) -> CapabilityKind {
        self.capability
    }

    pub(crate) fn local(&self) -> mir::Local {
        self.to.local
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
#[serde(tag = "type", content = "data")]
pub enum RepackOp<'tcx, Local = mir::Local, Place = crate::utils::Place<'tcx>, Guide = RepackGuide>
{
    /// Rust will sometimes join two BasicBlocks where a local is live in one and dead in the other.
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
    StorageDead(Local),
    /// This Op only appears within a BasicBlock and is attached to a
    /// [`mir::StatementKind::StorageDead`](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.StatementKind.html#variant.StorageDead)
    /// statement. We emit it for any such statement where the local may already be dead. We
    /// guarantee to have inserted a [`RepackOp::StorageDead`] before this Op so that one can
    /// safely ignore the statement this is attached to.
    IgnoreStorageDead(Local),
    /// Instructs that the current capability to the place (first [`CapabilityKind`]) should
    /// be weakened to the second given capability. We guarantee that `_.1 > _.2`.
    ///
    /// This Op is used prior to a [`RepackOp::Collapse`] to ensure that all packed up places have
    /// the same capability. It can also appear at basic block join points, where one branch has
    /// a weaker capability than the other.
    Weaken(Weaken<'tcx, Place, CapabilityKind>),
    /// Instructs that one should unpack `place` with the capability.
    /// We guarantee that the current state holds exactly the given capability for the given place.
    /// `guide` denotes e.g. the enum variant to unpack to. One can use
    /// [`Place::expand_one_level(_.0, _.1, ..)`](Place::expand_one_level) to get the set of all
    /// places (except as noted in the documentation for that fn) which will be obtained by unpacking.
    Expand(RepackExpand<'tcx, Place, Guide>),
    /// Instructs that one should pack up `place` with the given capability.
    /// `guide` denotes e.g. the enum variant to pack from. One can use
    /// [`Place::expand_one_level(_.0, _.1, ..)`](Place::expand_one_level) to get the set of all
    /// places which should be packed up. We guarantee that the current state holds exactly the
    /// given capability for all places in this set.
    Collapse(RepackCollapse<'tcx, Place, Guide>),
    /// TODO
    DerefShallowInit(Place, Place),
    /// This place should have its capability changed from `Lent` (for mutably
    /// borrowed places) or `Read` (for shared borrow places), to the given
    /// capability, because it is no longer lent out.
    RegainLoanedCapability(Place, CapabilityKind),
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DebugRepr<Ctxt> for RepackOp<'tcx> {
    type Repr = RepackOp<'static, String, String, String>;
    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr {
        match self {
            RepackOp::StorageDead(local) => RepackOp::StorageDead(local.display_string(ctxt)),
            RepackOp::IgnoreStorageDead(local) => {
                RepackOp::IgnoreStorageDead(local.display_string(ctxt))
            }
            RepackOp::RegainLoanedCapability(place, capability) => {
                RepackOp::RegainLoanedCapability(place.display_string(ctxt), *capability)
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

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for RepackOp<'tcx> {
    fn display_string(&self, ctxt: Ctxt) -> String {
        match self {
            RepackOp::RegainLoanedCapability(place, capability_kind) => {
                format!(
                    "Restore capability {:?} to {}",
                    capability_kind,
                    place.display_string(ctxt),
                )
            }
            RepackOp::Expand(expand) => format!(
                "unpack {} with capability {:?}",
                expand.from.display_string(ctxt),
                expand.capability
            ),
            _ => format!("{self:?}"),
        }
    }
}

impl<'tcx> RepackOp<'tcx> {
    pub(crate) fn weaken(place: Place<'tcx>, from: CapabilityKind, to: CapabilityKind) -> Self {
        Self::Weaken(Weaken::new(place, from, to))
    }
    pub(crate) fn expand<'a>(
        from: Place<'tcx>,
        guide: Option<RepackGuide>,
        for_cap: CapabilityKind,
        _ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self {
        // Note that we might generate expand annotations with `Write` capability for
        // the `bridge` operation to generate annotations between basic blocks.
        Self::Expand(RepackExpand {
            from,
            guide,
            capability: for_cap,
            _marker: PhantomData,
        })
    }

    pub fn affected_place(&self) -> Place<'tcx> {
        match *self {
            RepackOp::StorageDead(local) | RepackOp::IgnoreStorageDead(local) => local.into(),
            RepackOp::Weaken(Weaken { place, .. })
            | RepackOp::Collapse(RepackCollapse { to: place, .. })
            | RepackOp::Expand(RepackExpand { from: place, .. })
            | RepackOp::RegainLoanedCapability(place, _)
            | RepackOp::DerefShallowInit(place, _) => place,
        }
    }
}
