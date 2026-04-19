//! Owned State scaffolding for the computed-capability PCG design.
//!
//! The full design is described in the PCG documentation:
//! <https://prusti.github.io/pcg-docs/owned-state.html> and
//! <https://prusti.github.io/pcg-docs/computing-place-capabilities.html>.
//! In the target design, place capabilities are _computed_ from:
//!
//! 1. the **initialisation state** (this module), which records for each
//!    leaf owned place whether it is deeply initialised, shallowly
//!    initialised, or uninitialised, and
//! 2. the borrow PCG.
//!
//! This module introduces the data types only. The existing
//! [`crate::pcg::place_capabilities::PlaceCapabilities`] remains the
//! authoritative source of capabilities for now; these types are the
//! building blocks for the migration described at
//! <https://prusti.github.io/pcg-docs/computing-place-capabilities.html>.
//!
//! Items are `#[allow(dead_code)]` because they are scaffolding for a
//! migration in progress. They are exercised by unit tests in the
//! submodules so behaviour is pinned down as each rule is added.

#![allow(dead_code, unused_imports)]

mod init_capability;
mod init_tree;

pub(crate) use init_capability::OwnedCapability;
pub(crate) use init_tree::{InitialisationTree, JoinOutcome};
