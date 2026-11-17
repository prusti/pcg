#![feature(rustc_private)]
#![cfg(unix)]
use chrono::Local;
use derive_more::Deref;
use itertools::Itertools;
use rayon::prelude::*;
use regex::Regex;
use serde_derive::{Deserialize, Serialize};
use std::{
    cmp::Reverse,
    collections::BTreeSet,
    io::{ErrorKind, Write},
    ops::Range,
    os::unix::process::CommandExt,
    panic::{AssertUnwindSafe, catch_unwind},
    path::{Path, PathBuf},
    process::{Child, Command, ExitStatus},
    str::FromStr,
    sync::{LazyLock, Mutex},
    time::{Duration, Instant},
};

mod common;
use common::{
    RunOnCrateOptions, Target, find_workspace_base_dir, get, is_supported_crate, pcg_check_command,
    with_downloaded_crate,
};

const DATE: &str = "2026-07-15";

const NUM_CRATES: usize = 500;

const LOG_DIR: &str = "tmp/top-crates-logs";

const RESULTS_FILE: &str = "tmp/top-crates-results.tsv";

const RESULTS_HEADER: &str = "index\tcrate\tversion\tresult\tseconds\tpeak_mib\tfunction\tmessage";

/// Runs the PCG with validity checks on every function of the most downloaded
/// crates of `DATE`, and fails if a crate fails that is not a known failure.
///
/// The harness settings are environment variables outside the `PCG_`
/// namespace, because `pcg_bin` inherits the environment and rejects `PCG_`
/// variables it does not know:
/// - `TOP_CRATES_START`, `TOP_CRATES_END`: the index range of the crates to
///   check (default: all crates of the list).
/// - `TOP_CRATES_GROUP`, `TOP_CRATES_GROUPS`: split the crates of the range
///   into `TOP_CRATES_GROUPS` groups of about equal check time (see
///   `crate_group`) and check only group `TOP_CRATES_GROUP`, counted from 0
///   (default: one group).
/// - `TEST_CRATES_PARALLELISM`: how many crates are checked at once (default 1).
/// - `TOP_CRATES_TIMEOUT_SECS`: how long a crate may take before its check is
///   killed and the crate counts as failed (default 3600).
/// - `TOP_CRATES_MEMORY_LIMIT_MIB`: how much memory the processes of a
///   crate's check may use together before the check is killed and the crate
///   counts as failed (default 12 GiB). The default is the same everywhere,
///   so that whether a crate fails does not depend on the memory of the
///   machine, and it leaves room for the system on a 16 GB CI runner.
///
/// Each crate's result is appended to `RESULTS_FILE` as soon as the crate is
/// done, and the output of its check is written to `LOG_DIR`.
#[test]
#[ignore]
pub fn top_crates() {
    let all_crates = Crates::top(NUM_CRATES, Some(DATE));
    let start = env_var("TOP_CRATES_START", 0);
    let end = env_var("TOP_CRATES_END", NUM_CRATES);
    assert!(
        start <= end && end <= NUM_CRATES,
        "Invalid crate range {start}..{end}"
    );
    let group = env_var("TOP_CRATES_GROUP", 0);
    let groups = env_var("TOP_CRATES_GROUPS", 1);
    assert!(group < groups, "Invalid crate group {group} of {groups}");
    let parallelism = env_var("TEST_CRATES_PARALLELISM", 1);
    let limits = Limits {
        timeout: Duration::from_secs(env_var("TOP_CRATES_TIMEOUT_SECS", 3600)),
        memory_mib: env_var("TOP_CRATES_MEMORY_LIMIT_MIB", 12 * 1024),
    };
    let known_failures = known_failures(DATE, &all_crates);
    let indices = crate_group(start..end, &check_seconds(DATE, &all_crates), group, groups);

    std::fs::create_dir_all(LOG_DIR).unwrap();
    let mut results_file = std::fs::File::create(RESULTS_FILE).unwrap();
    writeln!(results_file, "{RESULTS_HEADER}").unwrap();
    let results_file = Mutex::new(results_file);
    rayon::ThreadPoolBuilder::new()
        .num_threads(parallelism)
        .build_global()
        .unwrap();
    let results: Vec<CrateResult> = indices
        .par_iter()
        .map(|&index| {
            let krate = &all_crates[index];
            let version = krate.version();
            println!("Starting: {index} ({} {version})", krate.name);
            let began = Instant::now();
            let (outcome, peak_mib) = check_crate(krate, &limits);
            let result = CrateResult {
                index,
                krate: krate.clone(),
                outcome,
                time: began.elapsed(),
                peak_mib,
                known_failure: known_failures.contains(&krate.name),
            };
            println!(
                "Finished: {index} ({} {version}): {} in {}s",
                krate.name,
                result.status(),
                result.time.as_secs()
            );
            writeln!(results_file.lock().unwrap(), "{}", result.row()).unwrap();
            result
        })
        .collect();

    println!("{RESULTS_HEADER}");
    for result in &results {
        println!("{}", result.row());
    }

    for result in &results {
        if result.known_failure && matches!(result.outcome, Outcome::Passed) {
            println!(
                "Known failure {} now passes; remove it from {}",
                result.krate.name,
                known_failures_file(DATE).display()
            );
        }
    }
    let failures: Vec<String> = results
        .iter()
        .filter(|result| !result.known_failure)
        .filter_map(|result| match &result.outcome {
            Outcome::Failed(failure) => Some(format!(
                "{} {} in {}: {} (log: {})",
                result.krate.name,
                result.krate.version(),
                failure.function.as_deref().unwrap_or("unknown function"),
                failure.message,
                crate_log_file(&result.krate).display()
            )),
            Outcome::Passed | Outcome::Unsupported(_) => None,
        })
        .collect();
    assert!(
        failures.is_empty(),
        "{} crates failed, see {RESULTS_FILE}:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

fn env_var<T: FromStr>(name: &str, default: T) -> T {
    std::env::var(name).map_or(default, |value| {
        value
            .parse()
            .unwrap_or_else(|_| panic!("{name} must be a number, got `{value}`"))
    })
}

fn known_failures_file(date: &str) -> PathBuf {
    PathBuf::from("tests/top-crates").join(format!("{date}-known-failures.txt"))
}

/// The crates of the list for `date` that are known to fail. Each line of the
/// file that is neither empty nor a `#` comment is a crate name followed by
/// the reason it fails.
fn known_failures(date: &str, crates: &[Crate]) -> BTreeSet<String> {
    let path = known_failures_file(date);
    let content = match std::fs::read_to_string(&path) {
        Ok(content) => content,
        Err(e) if e.kind() == ErrorKind::NotFound => return BTreeSet::new(),
        Err(e) => panic!("Failed to read {}: {e}", path.display()),
    };
    content
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            let name = line
                .split_once(char::is_whitespace)
                .unwrap_or_else(|| panic!("{}: `{line}` gives no reason", path.display()))
                .0;
            assert!(
                crates.iter().any(|krate| krate.name == name),
                "{}: {name} is not in the crate list",
                path.display()
            );
            name.to_string()
        })
        .collect()
}

/// How long the check of a crate is assumed to take if the timing file does
/// not list the crate: the median time of a crate in CI.
const DEFAULT_CHECK_SECONDS: u64 = 2;

/// The check time in seconds of each of `crates`, the list for `date`, as
/// measured in CI, for balancing the crate groups. The file lists the `crate`
/// and `seconds` columns of the `RESULTS_FILE`s of all groups of a CI run
/// under a header line; e.g. for the files `results/*.tsv`:
/// `awk -F'\t' 'NR == 1 || FNR > 1 { print $2 "\t" $5 }' results/*.tsv`.
fn check_seconds(date: &str, crates: &[Crate]) -> Vec<u64> {
    let path = PathBuf::from("tests/top-crates").join(format!("{date}-seconds.tsv"));
    let mut seconds = vec![DEFAULT_CHECK_SECONDS; crates.len()];
    let content = match std::fs::read_to_string(&path) {
        Ok(content) => content,
        Err(e) if e.kind() == ErrorKind::NotFound => return seconds,
        Err(e) => panic!("Failed to read {}: {e}", path.display()),
    };
    for line in content.lines().skip(1) {
        let (name, time) = line
            .split_once('\t')
            .unwrap_or_else(|| panic!("{}: `{line}` is not `crate\tseconds`", path.display()));
        let index = crates
            .iter()
            .position(|krate| krate.name == name)
            .unwrap_or_else(|| panic!("{}: {name} is not in the crate list", path.display()));
        seconds[index] = time
            .parse()
            .unwrap_or_else(|_| panic!("{}: `{line}` gives no seconds", path.display()));
    }
    seconds
}

/// The indices of group `group` of the crates in `range`, in increasing
/// order. The crates are split into `groups` groups by giving each crate, from
/// the slowest to the fastest by `seconds`, to the group with the least total
/// time so far.
fn crate_group(range: Range<usize>, seconds: &[u64], group: usize, groups: usize) -> Vec<usize> {
    let mut totals = vec![0; groups];
    let mut members = Vec::new();
    for index in range.sorted_by_key(|&index| (Reverse(seconds[index]), index)) {
        let lightest = (0..groups).min_by_key(|&g| (totals[g], g)).unwrap();
        totals[lightest] += seconds[index];
        if lightest == group {
            members.push(index);
        }
    }
    members.sort_unstable();
    members
}

struct CrateResult {
    index: usize,
    krate: Crate,
    outcome: Outcome,
    time: Duration,
    /// The largest memory use of the crate's check, in MiB.
    peak_mib: u64,
    known_failure: bool,
}

impl CrateResult {
    fn status(&self) -> &'static str {
        match (&self.outcome, self.known_failure) {
            (Outcome::Failed(_), true) => "known-fail",
            (Outcome::Passed, true) => "fixed",
            (outcome, _) => outcome.kind(),
        }
    }

    /// The line of this result in `RESULTS_FILE`.
    fn row(&self) -> String {
        let (function, message) = match &self.outcome {
            Outcome::Failed(failure) => (
                failure.function.as_deref().unwrap_or(""),
                failure.message.as_str(),
            ),
            Outcome::Unsupported(reason) => ("", reason.as_str()),
            Outcome::Passed => ("", ""),
        };
        format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{function}\t{}",
            self.index,
            self.krate.name,
            self.krate.version(),
            self.status(),
            self.time.as_secs(),
            self.peak_mib,
            message.replace(['\t', '\n'], " "),
        )
    }
}

enum Outcome {
    Passed,
    Failed(Failure),
    /// `is_supported_crate` excludes the crate, for the given reason.
    Unsupported(String),
}

impl Outcome {
    fn kind(&self) -> &'static str {
        match self {
            Outcome::Passed => "pass",
            Outcome::Failed(_) => "fail",
            Outcome::Unsupported(_) => "unsupported",
        }
    }
}

struct Failure {
    message: String,
    /// The function the PCG was analysing when the check failed.
    function: Option<String>,
}

fn crate_log_file(krate: &Crate) -> PathBuf {
    PathBuf::from(LOG_DIR).join(format!("{}-{}.log", krate.name, krate.version()))
}

/// The resources the check of a crate may use.
struct Limits {
    timeout: Duration,
    memory_mib: u64,
}

/// Checks `krate` within `limits`. Returns the outcome and the largest memory
/// use of the check in MiB.
fn check_crate(krate: &Crate, limits: &Limits) -> (Outcome, u64) {
    let (name, version) = (krate.name.as_str(), krate.version());
    if let Err(reason) = is_supported_crate(name, version) {
        return (Outcome::Unsupported(reason), 0);
    }
    let log = crate_log_file(krate);
    let run = catch_unwind(AssertUnwindSafe(|| {
        with_downloaded_crate(name, version, Some(DATE), |dir| {
            let options = RunOnCrateOptions::RunPCG {
                target: Target::Release,
                validity_checks: true,
                function: None,
                extra_env_vars: vec![],
            };
            let mut command = pcg_check_command(dir, &options);
            // Lints that newer compilers deny in older crates are not PCG
            // failures, so they only warn.
            command
                .env("CARGO_TERM_COLOR", "never")
                .env("NO_COLOR", "1")
                .env("RUSTFLAGS", "--cap-lints=warn");
            // The PCG logs each function it analyses at this level, which
            // lets `failure_from_log` name the function that failed.
            if std::env::var_os("RUST_LOG").is_none() {
                command.env("RUST_LOG", "warn,pcg[debug_ctxt]=info,pcg_bin=info");
            }
            run_with_limits(command, &log, limits)
        })
    }));
    let killed = |message: String| {
        Outcome::Failed(Failure {
            message,
            function: last_analysed_function(&read_log(&log).lines().collect::<Vec<_>>()),
        })
    };
    match run {
        Ok((End::Exited(status), peak_mib)) if status.success() => (Outcome::Passed, peak_mib),
        Ok((End::Exited(status), peak_mib)) => {
            (Outcome::Failed(failure_from_log(&log, status)), peak_mib)
        }
        Ok((End::TimedOut, peak_mib)) => (
            killed(format!("timed out after {}s", limits.timeout.as_secs())),
            peak_mib,
        ),
        Ok((End::OutOfMemory, peak_mib)) => (
            killed(format!(
                "exceeded the memory limit of {} MiB",
                limits.memory_mib
            )),
            peak_mib,
        ),
        Err(payload) => (
            Outcome::Failed(Failure {
                message: format!(
                    "harness panicked: {}",
                    payload
                        .downcast_ref::<String>()
                        .map(String::as_str)
                        .or_else(|| payload.downcast_ref::<&str>().copied())
                        .unwrap_or("unknown panic")
                ),
                function: None,
            }),
            0,
        ),
    }
}

/// How a run of `run_with_limits` ended.
enum End {
    Exited(ExitStatus),
    /// Killed because it ran longer than the timeout.
    TimedOut,
    /// Killed because it used more memory than the memory limit.
    OutOfMemory,
}

/// Runs `command` with its output written to `log`, killing it if it exceeds
/// `limits`. Returns how the run ended and the largest memory use of its
/// processes in MiB, sampled every second.
fn run_with_limits(mut command: Command, log: &Path, limits: &Limits) -> (End, u64) {
    let output = std::fs::File::create(log).unwrap();
    // `cargo` does not pass a kill on to the compilers it runs, so it gets its
    // own process group, which is killed as a whole and whose memory use is
    // the sum over its processes.
    command
        .stdout(output.try_clone().unwrap())
        .stderr(output)
        .process_group(0);
    let mut child = ProcessGroup(command.spawn().expect("Failed to run cargo check"));
    let group = libc::pid_t::try_from(child.0.id()).unwrap();
    let deadline = Instant::now() + limits.timeout;
    let mut peak_mib = 0;
    loop {
        if let Some(status) = child.0.try_wait().unwrap() {
            return (End::Exited(status), peak_mib);
        }
        peak_mib = peak_mib.max(process_group_rss_mib(group));
        if Instant::now() >= deadline {
            return (End::TimedOut, peak_mib);
        }
        if peak_mib > limits.memory_mib {
            return (End::OutOfMemory, peak_mib);
        }
        std::thread::sleep(Duration::from_secs(1));
    }
}

/// A child that leads its own process group. Dropping it kills the group
/// unless the child has exited, so that the group is also killed when the
/// harness panics while the child runs.
struct ProcessGroup(Child);

impl Drop for ProcessGroup {
    fn drop(&mut self) {
        if let Ok(Some(_)) = self.0.try_wait() {
            return;
        }
        let group = libc::pid_t::try_from(self.0.id()).unwrap();
        // SAFETY: `killpg` only sends a signal and has no memory-safety
        // preconditions.
        if unsafe { libc::killpg(group, libc::SIGKILL) } != 0 {
            eprintln!(
                "Failed to kill cargo check: {}",
                std::io::Error::last_os_error()
            );
        }
        let _ = self.0.wait();
    }
}

/// The summed resident memory of the processes in process group `group`, in
/// MiB.
fn process_group_rss_mib(group: libc::pid_t) -> u64 {
    let output = Command::new("ps")
        .args(["-A", "-o", "pgid=,rss="])
        .output()
        .expect("Failed to run ps");
    assert!(output.status.success(), "ps failed: {}", output.status);
    let rss_kib: u64 = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| {
            let (pgid, rss) = line.split_whitespace().collect_tuple()?;
            (pgid.parse() == Ok(group)).then(|| rss.parse::<u64>().unwrap())
        })
        .sum();
    rss_kib / 1024
}

fn read_log(log: &Path) -> String {
    String::from_utf8_lossy(&std::fs::read(log).unwrap()).into_owned()
}

static ANALYSED_FUNCTION: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"Running PCG on function: (.*) with \d+ basic blocks").unwrap());

/// The function the PCG analysed last in the given log lines.
fn last_analysed_function(lines: &[&str]) -> Option<String> {
    lines
        .iter()
        .rev()
        .find_map(|line| ANALYSED_FUNCTION.captures(line))
        .map(|captures| captures[1].to_string())
}

/// The first compiler panic in the log of a check that failed with `status`,
/// else a compiler killed by a signal, else the first error. For a panic or a
/// signal, also the function the PCG was analysing then.
fn failure_from_log(log: &Path, status: ExitStatus) -> Failure {
    const MAX_MESSAGE_LEN: usize = 500;
    let text = read_log(log);
    let lines: Vec<&str> = text.lines().collect();
    let analysed_before = |end: usize| last_analysed_function(&lines[..end]);
    let panic = lines.iter().position(|line| line.contains(" panicked at "));
    let signal = lines.iter().position(|line| {
        line.contains("process didn't exit successfully") && line.contains("(signal: ")
    });
    let (mut message, function) = if let Some(index) = panic {
        let workspace = format!("{}/", find_workspace_base_dir().display());
        let location = lines[index]
            .split_once(" panicked at ")
            .unwrap()
            .1
            .trim_end_matches(':');
        let location = location.strip_prefix(&workspace).unwrap_or(location);
        // The panic message ends before the note on how to get a backtrace,
        // or before the backtrace itself.
        let message = lines[index + 1..]
            .iter()
            .take_while(|line| {
                !line.is_empty() && !line.starts_with("note: ") && **line != "stack backtrace:"
            })
            .map(|line| line.trim())
            .join(" ");
        (format!("{location}: {message}"), analysed_before(index))
    } else if let Some(index) = signal {
        let signal = lines[index].rsplit_once("(signal: ").unwrap().1;
        (
            format!("compiler killed (signal: {signal}"),
            analysed_before(index),
        )
    } else if let Some(line) = lines.iter().find(|line| line.starts_with("error")) {
        (line.to_string(), None)
    } else {
        (
            format!("cargo check failed ({status}) without a panic or error"),
            None,
        )
    };
    if let Some((cut, _)) = message.char_indices().nth(MAX_MESSAGE_LEN) {
        message.truncate(cut);
    }
    Failure { message, function }
}

/// A create on crates.io.
#[derive(Debug, Deserialize, Serialize, Clone)]
struct Crate {
    #[serde(rename = "id")]
    name: String,
    #[serde(rename = "max_stable_version")]
    version: Option<String>,
    #[serde(rename = "newest_version")]
    newest_version: String,
}

impl Crate {
    fn version(&self) -> &str {
        self.version.as_ref().unwrap_or(&self.newest_version)
    }
}

/// The list of crates from crates.io
#[derive(Debug, Deref, Deserialize)]
struct Crates {
    crates: Vec<Crate>,
}

const PAGE_SIZE: usize = 100;

fn download_crates(n: usize) -> Vec<Crate> {
    let mut all_crates = Vec::new();
    let mut page = 1;

    while all_crates.len() < n {
        let url = format!(
            "https://crates.io/api/v1/crates?page={}&per_page={PAGE_SIZE}&sort=downloads",
            page,
        );
        let resp = get(&url).expect("Could not fetch top crates");
        assert!(
            resp.status().is_success(),
            "Response status: {}",
            resp.status()
        );
        let page_crates = match serde_json::from_reader::<_, Crates>(resp) {
            Ok(page_crates) => page_crates,
            Err(e) => panic!("Invalid JSON {e}"),
        };
        assert_eq!(page_crates.crates.len(), PAGE_SIZE);
        all_crates.extend(page_crates.crates);
        page += 1;
    }

    all_crates
}

fn get_cache_path(date: &str) -> PathBuf {
    PathBuf::from("tests/top-crates").join(format!("{date}.json"))
}

fn read_from_cache(cache_path: &Path) -> Option<Vec<Crate>> {
    if let Ok(file) = std::fs::File::open(cache_path) {
        return Some(serde_json::from_reader::<_, Vec<Crate>>(file).unwrap());
    }
    None
}

fn write_to_cache(cache_path: PathBuf, crates: &[Crate]) {
    let file = std::fs::File::create(&cache_path).unwrap_or_else(|err| {
        panic!(
            "Failed to create cache file {}: {}",
            cache_path.display(),
            err
        );
    });
    serde_json::to_writer(file, &crates).unwrap();
}

impl Crates {
    pub fn top(n: usize, date: Option<&str>) -> Crates {
        let today = Local::now().format("%Y-%m-%d").to_string();
        let date = date.unwrap_or(today.as_str());
        let cache_path = get_cache_path(date);
        let crates = read_from_cache(&cache_path).unwrap_or_else(|| {
            assert_eq!(
                date,
                today,
                "Cannot get crates from {} because we JSON file {} doesn't exist",
                date,
                cache_path.display()
            );
            let crates = download_crates(n);
            write_to_cache(cache_path, &crates);
            crates
        });
        assert!(
            crates.len() >= n,
            "Tried to get {} crates but only had {}",
            n,
            crates.len()
        );
        Crates {
            crates: crates[..n].to_vec(),
        }
    }
}
