//! Tiers 2 and 3 of the PCG's checks (see `pcg::oracle`), on every test file:
//!
//! - `dataflow_cross_checks` compares each PCG state with rustc's dataflow
//!   facts;
//! - `borrowck_probes` inserts accesses into the MIR and lets rustc's borrow
//!   checker decide them: an E or R the PCG claims that borrowck rejects
//!   (also rerun with Polonius), and an over-restriction candidate of tier 2
//!   that borrowck rejects (a bug of tier 2's oracle).
//!
//! Their findings are compared with the checked-in baselines in
//! `tests/oracle/`, one line `file<TAB>function<TAB>class<TAB>place` each:
//! a finding that is not listed fails the test, and so does a listed one that
//! is no longer found. `ORACLE_BLESS=1` writes the current findings instead.

use std::{
    collections::{BTreeSet, HashMap},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant},
};

use rayon::prelude::*;

mod common;

/// The longest a single run of `pcg_bin` may take.
const RUN_TIMEOUT: Duration = Duration::from_secs(180);

/// The most probes of one function borrow checked in one run.
const BATCH: usize = 100;

/// The most probes of a file borrow checked alone, after their batch was
/// rejected.
const MAX_SINGLE_RUNS: usize = 400;

fn test_files() -> Vec<PathBuf> {
    let workspace_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    common::get_test_files(&workspace_dir.parent().unwrap().join("test-files"))
}

fn stem(file: &Path) -> String {
    file.file_stem().unwrap().to_str().unwrap().to_owned()
}

fn scratch_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("oracle");
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Runs `pcg_bin` on `file` with the file's options, `env` and `args`.
/// Returns whether it succeeded and its standard error, or `None` if it
/// timed out.
fn run(file: &Path, env: &[(&str, String)], args: &[&str], tag: &str) -> Option<(bool, String)> {
    let pcg_bin = pcg_bin_utils::find_pcg_bin(
        &common::find_workspace_base_dir().join("pcg-bin"),
        common::Target::Debug,
    );
    let stderr_path = scratch_dir().join(format!("{}-{tag}.stderr", stem(file)));
    let mut command = Command::new(pcg_bin);
    command
        .args(args)
        .arg(file)
        .current_dir(env!("CARGO_TARGET_TMPDIR"))
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(std::fs::File::create(&stderr_path).unwrap());
    for (key, value) in common::parse_env_vars_from_file(file) {
        command.env(key, value);
    }
    for (key, value) in env {
        command.env(key, value);
    }
    let mut child = command.spawn().unwrap();
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break Some(status);
        }
        if start.elapsed() > RUN_TIMEOUT {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let stderr = String::from_utf8_lossy(&std::fs::read(&stderr_path).unwrap()).into_owned();
    let _ = std::fs::remove_file(&stderr_path);
    status.map(|status| (status.success(), stderr))
}

/// Compares `found` with the baseline `tests/oracle/<name>.tsv`.
fn compare_with_baseline(name: &str, description: &str, found: &BTreeSet<String>) {
    let path = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap())
        .join("tests")
        .join("oracle")
        .join(format!("{name}.tsv"));
    if std::env::var_os("ORACLE_BLESS").is_some() {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        let header = description
            .lines()
            .map(|line| format!("# {line}\n"))
            .collect::<String>();
        let lines = found
            .iter()
            .map(|line| format!("{line}\n"))
            .collect::<String>();
        std::fs::write(&path, header + &lines).unwrap();
        return;
    }
    let baseline = std::fs::read_to_string(&path)
        .unwrap_or_default()
        .lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .map(str::to_owned)
        .collect::<BTreeSet<_>>();
    let new = found.difference(&baseline).collect::<Vec<_>>();
    let gone = baseline.difference(found).collect::<Vec<_>>();
    if new.is_empty() && gone.is_empty() {
        return;
    }
    let show = |lines: &[&String]| {
        lines
            .iter()
            .take(300)
            .map(|line| format!("  {line}"))
            .collect::<Vec<_>>()
            .join("\n")
    };
    panic!(
        "{} differs from what the PCG gives (rerun with ORACLE_BLESS=1 to update it).\n\
         {} new findings:\n{}\n{} listed findings that are gone:\n{}",
        path.display(),
        new.len(),
        show(&new),
        gone.len(),
        show(&gone)
    );
}

#[test]
fn dataflow_cross_checks() {
    common::build_pcg_bin(common::Target::Debug);
    let line = regex::Regex::new(r"^PCG Oracle: \[(.*?)\] ([a-z-]+): (.*?) at ").unwrap();
    let found = test_files()
        .par_iter()
        .flat_map(|file| {
            let (success, stderr) = run(
                file,
                &[
                    ("PCG_ORACLE", "true".to_owned()),
                    ("PCG_VALIDITY_CHECKS", "false".to_owned()),
                    ("PCG_ALLOW_BORROWCK_ERRORS", "true".to_owned()),
                ],
                &[],
                "dataflow",
            )
            .unwrap_or_else(|| panic!("{} timed out", file.display()));
            assert!(success, "{} failed:\n{stderr}", file.display());
            stderr
                .lines()
                .filter_map(|l| line.captures(l))
                .map(|cap| format!("{}\t{}\t{}\t{}", stem(file), &cap[1], &cap[2], &cap[3]))
                .collect::<Vec<_>>()
        })
        .collect::<BTreeSet<_>>();
    compare_with_baseline(
        "dataflow",
        "Disagreements of the PCG's states with rustc's dataflow facts (see `pcg::oracle`):\n\
         file, function, class, place.",
        &found,
    );
}

/// A probe, as `pcg_bin` writes it with `PCG_ORACLE_PROBES`.
struct Probe {
    /// The line `borrowck-body-storage` reads, with an id unique in the file.
    line: String,
    id: String,
    function: String,
    class: String,
    place: String,
}

/// The verdict of rustc's borrow checker on one run.
struct BorrowCheck {
    /// The error codes of each probe.
    errors: HashMap<String, Vec<String>>,
    /// The errors that belong to no probe, and panics.
    other: Vec<String>,
    /// Whether two probes got the same span, so that errors cannot be
    /// attributed.
    ambiguous: bool,
}

fn borrow_check(file: &Path, probes: &[&Probe], polonius: bool, tag: &str) -> Option<BorrowCheck> {
    let probes_path = scratch_dir().join(format!("{}-{tag}.probes", stem(file)));
    std::fs::write(
        &probes_path,
        probes
            .iter()
            .map(|p| format!("{}\n", p.line))
            .collect::<String>(),
    )
    .unwrap();
    let mut args = vec!["--error-format=json"];
    if polonius {
        args.push("-Zpolonius");
    }
    let result = run(
        file,
        &[
            ("BORROWCK_PROBES", probes_path.display().to_string()),
            ("PCG_VALIDITY_CHECKS", "false".to_owned()),
        ],
        &args,
        tag,
    );
    let _ = std::fs::remove_file(&probes_path);
    let (_, stderr) = result?;
    let mut spans = HashMap::new();
    let mut ambiguous = false;
    let mut errors: HashMap<String, Vec<String>> = HashMap::new();
    let mut other = vec![];
    for line in stderr.lines() {
        if let Some(rest) = line.strip_prefix("PROBE-SPAN\t") {
            let (id, byte) = rest.split_once('\t').unwrap();
            ambiguous |= spans
                .insert(byte.parse::<u64>().unwrap(), id.to_owned())
                .is_some();
            continue;
        }
        if line.contains("panicked") {
            other.push(line.to_owned());
            continue;
        }
        let Ok(diagnostic) = serde_json::from_str::<serde_json::Value>(line) else {
            continue;
        };
        if diagnostic["level"] != "error" || diagnostic["code"].is_null() {
            continue;
        }
        let code = diagnostic["code"]["code"].as_str().unwrap_or("").to_owned();
        let probe = diagnostic["spans"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|span| span["is_primary"] == true)
            .find_map(|span| spans.get(&span["byte_start"].as_u64()?));
        match probe {
            Some(id) => errors.entry(id.clone()).or_default().push(code),
            None => other.push(format!("{code} {}", diagnostic["message"])),
        }
    }
    Some(BorrowCheck {
        errors,
        other,
        ambiguous,
    })
}

/// The findings of the probes of `file`.
fn probe_file(file: &Path) -> Vec<String> {
    let name = stem(file);
    let finding =
        |function: &str, class: &str, place: &str| format!("{name}\t{function}\t{class}\t{place}");
    // A file rustc rejects has no verdicts to compare with.
    match borrow_check(file, &[], false, "compiles") {
        Some(check) if check.other.is_empty() => {}
        _ => return vec![finding("", "does-not-compile", "")],
    }
    let probes_path = scratch_dir().join(format!("{name}.all-probes"));
    let _ = std::fs::remove_file(&probes_path);
    let (success, stderr) = run(
        file,
        &[
            ("PCG_ORACLE_PROBES", probes_path.display().to_string()),
            ("PCG_VALIDITY_CHECKS", "false".to_owned()),
            ("PCG_ALLOW_BORROWCK_ERRORS", "true".to_owned()),
        ],
        &[],
        "probes",
    )
    .unwrap_or_else(|| panic!("{} timed out", file.display()));
    assert!(success, "{} failed:\n{stderr}", file.display());
    let probes = std::fs::read_to_string(&probes_path)
        .unwrap_or_default()
        .lines()
        .enumerate()
        .map(|(n, line)| {
            let mut columns = line.split('\t').map(str::to_owned).collect::<Vec<_>>();
            columns[1] = format!("p{n}");
            Probe {
                id: columns[1].clone(),
                function: columns[2].clone(),
                class: columns[8].clone(),
                place: columns[9].clone(),
                line: columns.join("\t"),
            }
        })
        .collect::<Vec<_>>();
    let _ = std::fs::remove_file(&probes_path);

    // Batches with up to `BATCH` probes of each function. A batch whose
    // errors cannot all be attributed to its probes is split in halves.
    let mut by_function: Vec<(&str, Vec<&Probe>)> = vec![];
    for probe in &probes {
        match by_function.iter_mut().find(|(f, _)| *f == probe.function) {
            Some((_, list)) => list.push(probe),
            None => by_function.push((&probe.function, vec![probe])),
        }
    }
    let mut batches = vec![];
    let mut start = 0;
    while by_function.iter().any(|(_, list)| list.len() > start) {
        batches.push(
            by_function
                .iter()
                .flat_map(|(_, list)| list.iter().skip(start).take(BATCH).copied())
                .collect::<Vec<_>>(),
        );
        start += BATCH;
    }
    let mut rejected: Vec<&Probe> = vec![];
    let mut findings = vec![];
    let mut runs = 0;
    while let Some(batch) = batches.pop() {
        runs += 1;
        let check = borrow_check(file, &batch, false, &format!("batch{runs}"));
        let clean = check
            .as_ref()
            .is_some_and(|check| check.other.is_empty() && !check.ambiguous);
        if !clean && batch.len() > 1 {
            let (first, second) = batch.split_at(batch.len() / 2);
            batches.push(first.to_vec());
            batches.push(second.to_vec());
            continue;
        }
        for probe in batch {
            if !clean || check.as_ref().unwrap().errors.contains_key(&probe.id) {
                rejected.push(probe);
            }
        }
    }
    // Each rejected probe is checked alone, so that only its own verdict
    // counts, and a rejection is checked again with Polonius.
    for (n, probe) in rejected.iter().enumerate() {
        if n >= MAX_SINGLE_RUNS {
            findings.push(finding(&probe.function, "probe-unchecked", &probe.place));
            continue;
        }
        let Some(check) = borrow_check(file, &[probe], false, &format!("single{n}")) else {
            findings.push(finding(&probe.function, "probe-timeout", &probe.place));
            continue;
        };
        if !check.errors.contains_key(&probe.id) {
            if !check.other.is_empty() {
                findings.push(finding(&probe.function, "probe-perturbed", &probe.place));
            }
            continue;
        }
        let class = if probe.class == "claim" {
            match borrow_check(file, &[probe], true, &format!("polonius{n}")) {
                Some(check) if check.errors.contains_key(&probe.id) => "claim-rejected",
                Some(_) => "claim-rejected-by-nll-only",
                None => "claim-rejected-polonius-timeout",
            }
        } else {
            "under-rejected"
        };
        findings.push(finding(&probe.function, class, &probe.place));
    }
    findings
}

#[test]
fn borrowck_probes() {
    common::build_pcg_bin(common::Target::Debug);
    let found = test_files()
        .par_iter()
        .flat_map(|file| probe_file(file))
        .collect::<BTreeSet<_>>();
    compare_with_baseline(
        "borrowck",
        "Probes that rustc's borrow checker rejects (see `pcg::oracle`): an E or R the PCG claims\n\
         (`claim-rejected`; `claim-rejected-by-nll-only` if Polonius accepts it), or an access\n\
         rustc allows by tier 2's facts (`under-rejected`, a bug of tier 2), and probes without a\n\
         verdict: file, function, class, place.",
        &found,
    );
}
