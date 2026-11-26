//! Replay: a client that applies the capability changes the PCG records, in
//! order, from the capabilities before a phase (or before an edge between
//! blocks), gets the capabilities after it. The changes are those of the
//! recorded actions and of the statement's own effects (an assignment gives
//! its place E): the capabilities change in no other way. Records and the
//! graph are not replayed: no action lists their changes; the per-action
//! frame condition limits them to the places and edge an action names.

use super::{fail, show};
use crate::{
    action::CapabilityChanges,
    pcg::{
        CapabilityKind,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesReader},
    },
    utils::{CompilerCtxt, Place, display::DisplayWithCompilerCtxt},
};

/// Checks that applying `steps` to the capabilities of `before` gives those
/// of `after`; `what` names the phase or edge in a failure.
pub(crate) fn check<'s, 'a, 'tcx: 'a + 's>(
    what: &str,
    before: &PlaceCapabilities<'tcx>,
    steps: impl IntoIterator<Item = &'s CapabilityChanges<Place<'tcx>>>,
    after: &PlaceCapabilities<'tcx>,
    ctxt: CompilerCtxt<'a, 'tcx>,
) {
    let mut replayed = before.map.clone();
    for step in steps {
        for (place, capability) in step.iter() {
            match capability {
                Some(capability) => replayed.insert(place, capability),
                None => replayed.remove(&place),
            };
        }
    }
    if replayed == after.map {
        return;
    }
    let mut differences = replayed
        .keys()
        .chain(after.map.keys())
        .copied()
        .collect::<std::collections::HashSet<_>>()
        .into_iter()
        .filter(|place| !place.contains_unsafe_deref(ctxt))
        .filter_map(|place| {
            let replayed: Option<CapabilityKind> = replayed.get(&place).copied();
            let actual = after.get(place, ctxt);
            (replayed != actual).then(|| {
                format!(
                    "{}: replayed {}, actual {}",
                    place.display_string(ctxt),
                    show(replayed),
                    show(actual)
                )
            })
        })
        .collect::<Vec<_>>();
    if differences.is_empty() {
        return;
    }
    differences.sort();
    fail(
        ctxt,
        "replay",
        &format!(
            "{what}: the recorded changes do not reproduce the state: {}",
            differences.join(", ")
        ),
    );
}
