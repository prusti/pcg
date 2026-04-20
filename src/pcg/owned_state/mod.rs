//! Owned-PCG state.
//!
//! The full design is described in the PCG documentation:
//! <https://prusti.github.io/pcg-docs/owned-state.html> and
//! <https://prusti.github.io/pcg-docs/computing-place-capabilities.html>.
//! Place capabilities are computed from:
//!
//! 1. the **initialisation state** on each allocated local's
//!    [`InitialisationTree`], which records for each leaf owned place
//!    whether it is deeply initialised, shallowly initialised, or
//!    uninitialised, and
//! 2. the borrow PCG.

#![allow(dead_code, unused_imports)]

mod init_capability;
mod init_tree;
mod state;

pub use init_capability::OwnedCapability;
pub use init_tree::InitialisationTree;
pub(crate) use init_tree::JoinOutcome;
pub use state::{LocalInitState, OwnedPcg};
