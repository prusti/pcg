// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::marker::PhantomData;

use crate::rustc_interface::middle::mir::{self, PlaceElem};

use crate::{
    pcg::CapabilityKind,
    rustc_interface::{VariantIdx, span::Symbol},
    utils::{
        CompilerCtxt, ConstantIndex, DebugRepr, HasCompilerCtxt, Place, SnapshotLocation,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
    },
};
use serde_derive::Serialize;

/// The index local of an [`RepackGuide::Index`] guide. When the local is
/// overwritten or dies while the expansion it guides is still present, `label`
/// is the snapshot location that still holds the index value. The label is not
/// part of the guide's identity: a labelled and an unlabelled guide of the
/// same local describe the same expansion.
#[derive(Clone, Copy)]
pub struct IndexLocal {
    local: mir::Local,
    label: Option<SnapshotLocation>,
}

impl IndexLocal {
    #[must_use]
    pub fn local(self) -> mir::Local {
        self.local
    }

    /// The snapshot location holding the index value, if the local no longer
    /// holds it.
    #[must_use]
    pub fn label(self) -> Option<SnapshotLocation> {
        self.label
    }
}

impl<D, Default> RepackGuide<IndexLocal, D, Default> {
    /// Labels an `Index` guide of `index` with `label`, unless already
    /// labelled: the first overwrite or death of the local after the expansion
    /// is the last point holding the index value. Returns whether the guide
    /// changed.
    pub(crate) fn label_index(&mut self, index: mir::Local, label: SnapshotLocation) -> bool {
        match self {
            RepackGuide::Index(local, _) if local.local == index && local.label.is_none() => {
                local.label = Some(label);
                true
            }
            _ => false,
        }
    }

    /// Whether this is an `Index` guide of `index` that [`Self::label_index`]
    /// would label.
    pub(crate) fn is_unlabelled_index_of(&self, index: mir::Local) -> bool {
        matches!(self, RepackGuide::Index(local, _) if local.local == index && local.label.is_none())
    }
}

impl From<mir::Local> for IndexLocal {
    fn from(local: mir::Local) -> Self {
        Self { local, label: None }
    }
}

impl PartialEq for IndexLocal {
    fn eq(&self, other: &Self) -> bool {
        self.local == other.local
    }
}

impl Eq for IndexLocal {}

impl std::hash::Hash for IndexLocal {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.local.hash(state);
    }
}

impl std::fmt::Debug for IndexLocal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.label {
            None => write!(f, "{:?}", self.local),
            Some(label) => write!(f, "{:?} at {label:?}", self.local),
        }
    }
}

/// A guide for an expansion that isn't a simple struct-field unpack.
///
/// The `Default` type parameter is used in context where no guide is required
/// (e.g. for a box deref, where only one expansion is possible).
/// If a guide is required (c.f. [`RequiredGuide`]), `Default`
/// is instantiated to `!` so the variant is statically unreachable.
#[derive(Clone, Copy, Eq, PartialEq, Hash)]
pub enum RepackGuide<Local = IndexLocal, D = (), Default = D> {
    /// No non-trivial guide (e.g. an ordinary field/tuple expansion).
    Default(Default),
    Downcast(Option<Symbol>, VariantIdx, D),
    ConstantIndex(ConstantIndex, D),
    Index(Local, D),
    Subslice {
        from: u64,
        to: u64,
        from_end: bool,
        data: D,
    },
}

/// A `RepackGuide` guaranteed to not be [`RepackGuide::Default`].
/// Used for enum downcasts, array accesses etc.
pub(crate) type RequiredGuide<D = ()> = RepackGuide<IndexLocal, D, !>;

/// Custom `Debug` that does not print the per-child data payload, so
/// that test-visible annotation strings stay stable (`Index(_5)` rather
/// than `Index(_5, ())`) across the generic-parameter introduction.
/// The `Default` variant's payload is still shown because it is
/// distinctive and not merely scaffolding.
impl<Local: std::fmt::Debug, D, Default: std::fmt::Debug> std::fmt::Debug
    for RepackGuide<Local, D, Default>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RepackGuide::Default(d) => f.debug_tuple("Default").field(d).finish(),
            RepackGuide::Downcast(sym, idx, _) => {
                f.debug_tuple("Downcast").field(sym).field(idx).finish()
            }
            RepackGuide::ConstantIndex(ci, _) => f.debug_tuple("ConstantIndex").field(ci).finish(),
            RepackGuide::Index(local, _) => f.debug_tuple("Index").field(local).finish(),
            RepackGuide::Subslice {
                from,
                to,
                from_end,
                data: _,
            } => f
                .debug_struct("Subslice")
                .field("from", from)
                .field("to", to)
                .field("from_end", from_end)
                .finish(),
        }
    }
}

impl<Local, D, Default> RepackGuide<Local, D, Default> {
    #[allow(dead_code)]
    pub(crate) fn map_data<R>(self, f: impl FnOnce(D) -> R) -> RepackGuide<Local, R, Default> {
        match self {
            RepackGuide::Default(d) => RepackGuide::Default(d),
            RepackGuide::Downcast(s, v, data) => RepackGuide::Downcast(s, v, f(data)),
            RepackGuide::ConstantIndex(c, data) => RepackGuide::ConstantIndex(c, f(data)),
            RepackGuide::Index(local, data) => RepackGuide::Index(local, f(data)),
            RepackGuide::Subslice {
                from,
                to,
                from_end,
                data,
            } => RepackGuide::Subslice {
                from,
                to,
                from_end,
                data: f(data),
            },
        }
    }

    pub(crate) fn into_non_default(self) -> Option<RequiredGuide<D>>
    where
        Local: Into<IndexLocal>,
    {
        match self {
            RepackGuide::Default(_) => None,
            RepackGuide::Downcast(s, v, d) => Some(RepackGuide::Downcast(s, v, d)),
            RepackGuide::ConstantIndex(c, d) => Some(RepackGuide::ConstantIndex(c, d)),
            RepackGuide::Index(local, d) => Some(RepackGuide::Index(local.into(), d)),
            RepackGuide::Subslice {
                from,
                to,
                from_end,
                data,
            } => Some(RepackGuide::Subslice {
                from,
                to,
                from_end,
                data,
            }),
        }
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for RepackGuide {
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            match self {
                RepackGuide::Index(local, ()) => {
                    format!("index with local {}", local.local().display_string(ctxt))
                }
                _ => format!("{self:?}"),
            }
            .into(),
        )
    }
}

impl From<RequiredGuide> for RepackGuide {
    fn from(val: RequiredGuide) -> Self {
        match val {
            RepackGuide::Default(never) => match never {},
            RepackGuide::Downcast(s, v, ()) => RepackGuide::Downcast(s, v, ()),
            RepackGuide::ConstantIndex(c, ()) => RepackGuide::ConstantIndex(c, ()),
            RepackGuide::Index(local, ()) => RepackGuide::Index(local, ()),
            RepackGuide::Subslice {
                from,
                to,
                from_end,
                data: (),
            } => RepackGuide::Subslice {
                from,
                to,
                from_end,
                data: (),
            },
        }
    }
}

impl From<RequiredGuide> for PlaceElem<'_> {
    fn from(val: RequiredGuide) -> Self {
        match val {
            RepackGuide::Default(never) => match never {},
            RepackGuide::Index(local, ()) => PlaceElem::Index(local.local()),
            RepackGuide::Downcast(symbol, variant_idx, ()) => {
                PlaceElem::Downcast(symbol, variant_idx)
            }
            RepackGuide::ConstantIndex(constant_index, ()) => PlaceElem::ConstantIndex {
                offset: constant_index.offset,
                min_length: constant_index.min_length,
                from_end: constant_index.from_end,
            },
            RepackGuide::Subslice {
                from,
                to,
                from_end,
                data: (),
            } => PlaceElem::Subslice { from, to, from_end },
        }
    }
}

impl From<RepackGuide> for PlaceElem<'_> {
    fn from(val: RepackGuide) -> Self {
        // Safe because ambient `RepackGuide` *shouldn't* carry `Default`
        // at points where we reify it to a `PlaceElem`.
        val.into_non_default()
            .expect("unexpected RepackGuide::Default in PlaceElem conversion")
            .into()
    }
}

impl TryFrom<PlaceElem<'_>> for RepackGuide {
    type Error = ();
    fn try_from(elem: PlaceElem<'_>) -> Result<Self, Self::Error> {
        match elem {
            PlaceElem::Index(local) => Ok(RepackGuide::Index(local.into(), ())),
            PlaceElem::Downcast(symbol, variant_idx) => {
                Ok(RepackGuide::Downcast(symbol, variant_idx, ()))
            }
            PlaceElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => Ok(RepackGuide::ConstantIndex(
                ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                },
                (),
            )),
            PlaceElem::Subslice { from, to, from_end } => Ok(RepackGuide::Subslice {
                from,
                to,
                from_end,
                data: (),
            }),
            _ => Err(()),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "type-export", ts(export, concrete(Place = String, Guide = String)))]
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
    #[must_use]
    pub fn capability(&self) -> CapabilityKind {
        self.capability
    }

    #[must_use]
    pub fn from(&self) -> Place<'tcx> {
        self.from
    }

    #[must_use]
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
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "type-export", ts(export, concrete(Place = String, Guide = String)))]
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

    #[must_use]
    pub fn guide(self) -> Option<RepackGuide> {
        self.guide
    }

    #[must_use]
    pub fn box_deref_place(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Option<Place<'tcx>> {
        if self.to.ty(ctxt).ty.is_box() {
            self.to.project_deeper(PlaceElem::Deref, ctxt).ok()
        } else {
            None
        }
    }

    #[must_use]
    pub fn to(&self) -> Place<'tcx> {
        self.to
    }

    #[must_use]
    pub fn capability(&self) -> CapabilityKind {
        self.capability
    }

    pub(crate) fn local(&self) -> mir::Local {
        self.to.local
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
#[cfg_attr(
    feature = "type-export",
    ts(export, concrete(Local = String, Place = String, Guide = String))
)]
#[serde(tag = "type", content = "data")]
pub enum RepackOp<'tcx, Local = mir::Local, Place = crate::utils::Place<'tcx>, Guide = RepackGuide>
{
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
    StorageDead(Local),
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
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> DebugRepr<Ctxt> for RepackOp<'tcx> {
    type Repr = RepackOp<'static, String, String, String>;
    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr {
        match self {
            RepackOp::StorageDead(local) => RepackOp::StorageDead(local.display_string(ctxt)),
            RepackOp::Expand(expand) => RepackOp::Expand(expand.debug_repr(ctxt)),
            RepackOp::Collapse(collapse) => RepackOp::Collapse(collapse.debug_repr(ctxt)),
            RepackOp::DerefShallowInit(place, place2) => {
                RepackOp::DerefShallowInit(place.display_string(ctxt), place2.display_string(ctxt))
            }
        }
    }
}

impl<Ctxt, P: std::fmt::Debug + DisplayWithCtxt<Ctxt>> DisplayWithCtxt<Ctxt>
    for RepackOp<'_, mir::Local, P>
{
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            match self {
                RepackOp::Expand(expand) => format!(
                    "unpack {} with capability {:?}",
                    expand.from.display_string(ctxt),
                    expand.capability
                ),
                _ => format!("{self:?}"),
            }
            .into(),
        )
    }
}

impl<'tcx> RepackOp<'tcx> {
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

    #[must_use]
    pub fn affected_place(&self) -> Place<'tcx> {
        match *self {
            RepackOp::StorageDead(local) => local.into(),
            RepackOp::Collapse(RepackCollapse { to: place, .. })
            | RepackOp::Expand(RepackExpand { from: place, .. })
            | RepackOp::DerefShallowInit(place, _) => place,
        }
    }
}
