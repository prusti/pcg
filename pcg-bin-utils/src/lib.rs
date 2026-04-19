//! Shared helpers for locating and building the `pcg_bin` executable.
//!
//! Both `pcg-server` and `pcg-tests` need to run `pcg_bin`. This crate
//! centralises the path-resolution logic so they agree on where the
//! binary lives, and so `CARGO_TARGET_DIR` is honoured consistently.

use std::{
    env,
    path::{Path, PathBuf},
    process::Command,
};

/// Which build profile of `pcg_bin` to use.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Target {
    Debug,
    Release,
}

impl Target {
    /// Name of the cargo profile subdirectory (`debug` or `release`).
    #[must_use]
    pub fn profile_dir(self) -> &'static str {
        match self {
            Target::Debug => "debug",
            Target::Release => "release",
        }
    }

    /// Flag to pass to `cargo build` for this target, if any.
    #[must_use]
    pub fn cargo_flag(self) -> Option<&'static str> {
        match self {
            Target::Debug => None,
            Target::Release => Some("--release"),
        }
    }
}

/// File name of the `pcg_bin` executable for the current platform.
#[must_use]
pub fn pcg_bin_name() -> &'static str {
    if cfg!(target_os = "windows") {
        "pcg_bin.exe"
    } else {
        "pcg_bin"
    }
}

/// Returns the cargo target directory to use when resolving build
/// outputs, honouring the `CARGO_TARGET_DIR` environment variable.
#[must_use]
pub fn target_dir() -> PathBuf {
    match env::var_os("CARGO_TARGET_DIR") {
        Some(s) => PathBuf::from(s),
        None => PathBuf::from("target"),
    }
}

/// Path to the built `pcg_bin` executable, assuming `pcg-bin` is
/// its own workspace rooted at `pcg_bin_workspace_dir`.
#[must_use]
pub fn find_pcg_bin(pcg_bin_workspace_dir: &Path, target: Target) -> PathBuf {
    pcg_bin_workspace_dir
        .join(target_dir())
        .join(target.profile_dir())
        .join(pcg_bin_name())
}

/// Build `pcg_bin` in its workspace at `pcg_bin_workspace_dir` using
/// the given profile, and return the path of the resulting binary.
///
/// Panics if the `cargo build` invocation fails to launch or exits
/// with a non-zero status, mirroring the existing test-suite
/// expectations.
pub fn build_pcg_bin_in_dir(pcg_bin_workspace_dir: &Path, target: Target) -> PathBuf {
    let mut cmd = Command::new("cargo");
    cmd.arg("build");
    if let Some(flag) = target.cargo_flag() {
        cmd.arg(flag);
    }
    cmd.current_dir(pcg_bin_workspace_dir);

    let status = cmd
        .status()
        .unwrap_or_else(|e| panic!("Failed to launch `cargo build` for pcg_bin: {e}"));

    assert!(
        status.success(),
        "`cargo build` for pcg_bin failed (cwd: {})",
        pcg_bin_workspace_dir.display(),
    );

    find_pcg_bin(pcg_bin_workspace_dir, target)
}

/// Locate `pcg_bin` for `pcg-server`.
///
/// Resolution order:
/// 1. `PCG_BIN_PATH` if set.
/// 2. Development layout — `pcg-bin` is its own workspace living
///    alongside `pcg-server`, so the binary is under
///    `../pcg-bin/<target_dir>/release/pcg_bin`.
/// 3. Docker layout — `pcg-bin` has been built in a shared parent
///    workspace, so the binary is under `../<target_dir>/release/pcg_bin`.
///
/// Both (2) and (3) honour `CARGO_TARGET_DIR`.
#[must_use]
pub fn find_pcg_bin_for_server() -> PathBuf {
    if let Ok(explicit) = env::var("PCG_BIN_PATH") {
        return PathBuf::from(explicit);
    }

    let dev = find_pcg_bin(Path::new("../pcg-bin"), Target::Release);
    if dev.exists() {
        return dev;
    }

    find_pcg_bin(Path::new(".."), Target::Release)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn target_profile_dir_strings() {
        assert_eq!(Target::Debug.profile_dir(), "debug");
        assert_eq!(Target::Release.profile_dir(), "release");
    }

    #[test]
    fn target_cargo_flag() {
        assert_eq!(Target::Debug.cargo_flag(), None);
        assert_eq!(Target::Release.cargo_flag(), Some("--release"));
    }

    #[test]
    fn find_pcg_bin_default_layout() {
        // Ensure we don't accidentally read from the ambient env.
        // SAFETY: the test is single-threaded for env mutation. We
        // restore the prior value when done.
        let prior = env::var_os("CARGO_TARGET_DIR");
        // SAFETY: single-threaded test; no other thread reads this var.
        unsafe {
            env::remove_var("CARGO_TARGET_DIR");
        }

        let path = find_pcg_bin(Path::new("/some/ws"), Target::Debug);
        assert_eq!(
            path,
            PathBuf::from(format!("/some/ws/target/debug/{}", pcg_bin_name())),
        );

        // SAFETY: single-threaded test; no other thread reads this var.
        unsafe {
            if let Some(v) = prior {
                env::set_var("CARGO_TARGET_DIR", v);
            }
        }
    }

    #[test]
    fn find_pcg_bin_with_absolute_cargo_target_dir() {
        let prior = env::var_os("CARGO_TARGET_DIR");
        // SAFETY: single-threaded test.
        unsafe {
            env::set_var("CARGO_TARGET_DIR", "/abs/build");
        }

        let path = find_pcg_bin(Path::new("/some/ws"), Target::Release);
        // An absolute CARGO_TARGET_DIR overrides the workspace prefix.
        assert_eq!(
            path,
            PathBuf::from(format!("/abs/build/release/{}", pcg_bin_name())),
        );

        // SAFETY: single-threaded test.
        unsafe {
            match prior {
                Some(v) => env::set_var("CARGO_TARGET_DIR", v),
                None => env::remove_var("CARGO_TARGET_DIR"),
            }
        }
    }

    #[test]
    fn find_pcg_bin_with_relative_cargo_target_dir() {
        let prior = env::var_os("CARGO_TARGET_DIR");
        // SAFETY: single-threaded test.
        unsafe {
            env::set_var("CARGO_TARGET_DIR", "custom_target");
        }

        let path = find_pcg_bin(Path::new("/some/ws"), Target::Debug);
        assert_eq!(
            path,
            PathBuf::from(format!("/some/ws/custom_target/debug/{}", pcg_bin_name())),
        );

        // SAFETY: single-threaded test.
        unsafe {
            match prior {
                Some(v) => env::set_var("CARGO_TARGET_DIR", v),
                None => env::remove_var("CARGO_TARGET_DIR"),
            }
        }
    }
}
