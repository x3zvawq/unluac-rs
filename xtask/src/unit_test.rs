use std::collections::BTreeMap;
use std::env;
use std::io::{self, IsTerminal};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::{Arc, Mutex, mpsc};
use std::thread;
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail};
use indicatif::{ProgressBar, ProgressDrawTarget, ProgressStyle};
use owo_colors::OwoColorize;

const OUTPUT_ENV: &str = "UNLUAC_TEST_OUTPUT";
const PROGRESS_ENV: &str = "UNLUAC_TEST_PROGRESS";
const COLOR_ENV: &str = "UNLUAC_TEST_COLOR";
const RECOMPILE_ROUNDS_ENV: &str = "UNLUAC_TEST_RECOMPILE_ROUNDS";

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum FailureOutputMode {
    Simple,
    Verbose,
}

impl FailureOutputMode {
    fn parse(value: &str) -> Result<Self> {
        match value {
            "simple" => Ok(Self::Simple),
            "verbose" => Ok(Self::Verbose),
            _ => bail!("unknown output mode: {value}"),
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Simple => "simple",
            Self::Verbose => "verbose",
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum ProgressMode {
    Auto,
    On,
    Off,
}

impl ProgressMode {
    fn parse(value: &str) -> Result<Self> {
        match value {
            "auto" => Ok(Self::Auto),
            "on" => Ok(Self::On),
            "off" => Ok(Self::Off),
            _ => bail!("unknown progress mode: {value}"),
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum ColorMode {
    Auto,
    Always,
    Never,
}

impl ColorMode {
    fn parse(value: &str) -> Result<Self> {
        match value {
            "auto" => Ok(Self::Auto),
            "always" => Ok(Self::Always),
            "never" => Ok(Self::Never),
            _ => bail!("unknown color mode: {value}"),
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum PlainProgressDetail {
    Sparse,
    Verbose,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct Options {
    suite: String,
    dialect: String,
    case_filters: Vec<String>,
    output: FailureOutputMode,
    timeout_seconds: u64,
    progress: ProgressMode,
    color: ColorMode,
    plain_progress_detail: PlainProgressDetail,
    jobs: usize,
    recompile_rounds: u32,
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct UnitCaseDescriptor {
    suite: String,
    dialect: String,
    path: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum UnitCaseOutcome {
    Passed,
    Failed,
    TimedOut,
}

#[derive(Debug)]
struct UnitCaseExecution {
    outcome: UnitCaseOutcome,
    classification: Option<String>,
    rendered_failure: Option<String>,
    proto_count: usize,
    failed_proto_tags: Vec<String>,
}

#[derive(Debug, Eq, PartialEq)]
struct MachineFailure {
    classification: String,
    rendered: String,
    proto_count: usize,
    failed_proto_tags: Vec<String>,
}

#[derive(Debug, Clone)]
struct ScheduledCase {
    case: UnitCaseDescriptor,
}

#[derive(Debug)]
enum WorkerEvent {
    Started {
        case: UnitCaseDescriptor,
    },
    Finished {
        case: UnitCaseDescriptor,
        execution: UnitCaseExecution,
    },
    WorkerError {
        case: UnitCaseDescriptor,
        error: String,
    },
}

#[derive(Clone, Copy, Debug)]
struct Palette {
    enabled: bool,
}

impl Palette {
    fn red(self, text: impl AsRef<str>) -> String {
        let text = text.as_ref();
        if self.enabled {
            text.red().bold().to_string()
        } else {
            text.to_owned()
        }
    }

    fn green(self, text: impl AsRef<str>) -> String {
        let text = text.as_ref();
        if self.enabled {
            text.green().bold().to_string()
        } else {
            text.to_owned()
        }
    }

    fn yellow(self, text: impl AsRef<str>) -> String {
        let text = text.as_ref();
        if self.enabled {
            text.yellow().bold().to_string()
        } else {
            text.to_owned()
        }
    }

    fn cyan(self, text: impl AsRef<str>) -> String {
        let text = text.as_ref();
        if self.enabled {
            text.cyan().to_string()
        } else {
            text.to_owned()
        }
    }

    fn magenta(self, text: impl AsRef<str>) -> String {
        let text = text.as_ref();
        if self.enabled {
            text.magenta().to_string()
        } else {
            text.to_owned()
        }
    }
}

enum ReporterMode {
    Interactive(ProgressBar),
    Plain,
}

#[derive(Clone, Copy, Debug)]
struct ProgressCounts {
    completed: usize,
    total: usize,
}

struct Reporter {
    mode: ReporterMode,
    palette: Palette,
    plain_progress_detail: PlainProgressDetail,
}

impl Reporter {
    fn new(total: usize, options: &Options) -> Result<Self> {
        let palette = Palette {
            enabled: color_is_enabled(options.color),
        };
        let mode = if progress_is_enabled(options.progress) {
            let progress =
                ProgressBar::with_draw_target(Some(total as u64), ProgressDrawTarget::stderr());
            progress.set_style(
                ProgressStyle::with_template("{spinner} {msg}")
                    .context("failed to build unit test progress style")?,
            );
            ReporterMode::Interactive(progress)
        } else {
            ReporterMode::Plain
        };
        Ok(Self {
            mode,
            palette,
            plain_progress_detail: options.plain_progress_detail,
        })
    }

    fn announce_start(&self, total: usize, options: &Options, jobs: usize) {
        let filters = if options.case_filters.is_empty() {
            "none".to_owned()
        } else {
            options.case_filters.join(", ")
        };
        eprintln!(
            "running {total} unit case(s) with output={} timeout={}s progress={} color={} jobs={} recompile-rounds={} case-filter={}",
            options.output.label(),
            options.timeout_seconds,
            match options.progress {
                ProgressMode::Auto => "auto",
                ProgressMode::On => "on",
                ProgressMode::Off => "off",
            },
            match options.color {
                ColorMode::Auto => "auto",
                ColorMode::Always => "always",
                ColorMode::Never => "never",
            },
            jobs,
            options.recompile_rounds,
            filters,
        );
    }

    fn update_progress(
        &self,
        completed: usize,
        total: usize,
        active: usize,
        case: &UnitCaseDescriptor,
        event: ProgressEventKind,
    ) {
        match &self.mode {
            ReporterMode::Interactive(progress) => {
                let message = progress_message(self.palette, completed, total, active, case);
                progress.set_position(completed as u64);
                progress.set_message(message);
            }
            ReporterMode::Plain => match self.plain_progress_detail {
                PlainProgressDetail::Verbose => {
                    let message = progress_message(self.palette, completed, total, active, case);
                    eprintln!("{message}");
                }
                PlainProgressDetail::Sparse => {
                    if should_emit_sparse_plain_progress(event, completed, total) {
                        eprintln!(
                            "{}",
                            sparse_progress_message(self.palette, completed, total, active)
                        );
                    }
                }
            },
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_failure(
        &self,
        counts: ProgressCounts,
        case: &UnitCaseDescriptor,
        outcome: UnitCaseOutcome,
        rendered_failure: Option<&str>,
        failed_proto_tags: &[String],
        timeout_seconds: u64,
        output_mode: FailureOutputMode,
    ) {
        let text = match outcome {
            UnitCaseOutcome::TimedOut => self.render_timeout(counts, case, timeout_seconds),
            UnitCaseOutcome::Failed => self.render_failure(
                counts,
                case,
                rendered_failure.unwrap_or("runner exited with failure but did not report details"),
                failed_proto_tags,
                output_mode,
            ),
            UnitCaseOutcome::Passed => return,
        };

        match &self.mode {
            ReporterMode::Interactive(progress) => progress.println(text),
            ReporterMode::Plain => eprintln!("{text}"),
        }
    }

    fn finish(
        &self,
        total: usize,
        failed: usize,
        timed_out: usize,
        failure_counts: &BTreeMap<String, usize>,
        total_protos: usize,
        failed_protos: usize,
    ) {
        if let ReporterMode::Interactive(progress) = &self.mode {
            progress.finish_and_clear();
        }

        let passed = total - failed;
        let passed_protos = total_protos.saturating_sub(failed_protos);
        eprintln!(
            "unit runner finished: files: total={}, passed={}, failed={}, timed_out={}",
            total,
            self.palette.green(passed.to_string()),
            if failed == 0 {
                self.palette.green(failed.to_string())
            } else {
                self.palette.red(failed.to_string())
            },
            if timed_out == 0 {
                self.palette.green(timed_out.to_string())
            } else {
                self.palette.yellow(timed_out.to_string())
            },
        );
        if total_protos > 0 {
            eprintln!(
                "                     protos: total={}, passed={}, failed={}",
                total_protos,
                self.palette.green(passed_protos.to_string()),
                if failed_protos == 0 {
                    self.palette.green(failed_protos.to_string())
                } else {
                    self.palette.red(failed_protos.to_string())
                },
            );
        }

        if failure_counts.is_empty() {
            return;
        }

        eprintln!("failure summary:");
        for (label, count) in sorted_failure_counts(failure_counts) {
            let is_timeout = label == "timed-out";
            let label = if is_timeout {
                self.palette.yellow(label)
            } else {
                self.palette.red(label)
            };
            let count = if is_timeout {
                self.palette.yellow(count.to_string())
            } else {
                self.palette.red(count.to_string())
            };
            eprintln!("  {count}\t{label}");
        }
    }

    fn render_timeout(
        &self,
        counts: ProgressCounts,
        case: &UnitCaseDescriptor,
        timeout_seconds: u64,
    ) -> String {
        format!(
            "{} [{}/{}]\tdialect: {}\tcase: {}\t{}",
            self.palette.red("FAIL"),
            counts.completed,
            counts.total,
            self.palette.cyan(&case.dialect),
            case.path,
            self.palette
                .yellow(format!("timed out after {}s", timeout_seconds))
        )
    }

    fn render_failure(
        &self,
        counts: ProgressCounts,
        case: &UnitCaseDescriptor,
        raw: &str,
        failed_proto_tags: &[String],
        output_mode: FailureOutputMode,
    ) -> String {
        let normalized = normalize_runner_failure(raw, case, output_mode);
        let tag_suffix = if failed_proto_tags.is_empty() {
            String::new()
        } else {
            format!("\t[{}]", failed_proto_tags.join(", "))
        };
        match output_mode {
            FailureOutputMode::Simple => format!(
                "{} [{}/{}]\tdialect: {}\tcase: {}\t{}{}",
                self.palette.red("FAIL"),
                counts.completed,
                counts.total,
                self.palette.cyan(&case.dialect),
                case.path,
                self.palette.red(&normalized),
                self.palette.yellow(&tag_suffix),
            ),
            FailureOutputMode::Verbose => {
                let mut lines = Vec::new();
                lines.push(format!(
                    "{} [{}/{}]\tdialect: {}\tcase: {}{}",
                    self.palette.red("FAIL"),
                    counts.completed,
                    counts.total,
                    self.palette.cyan(&case.dialect),
                    case.path,
                    self.palette.yellow(&tag_suffix),
                ));
                lines.extend(
                    normalized
                        .lines()
                        .map(|line| format!("  {}", self.color_detail_line(line))),
                );
                lines.join("\n")
            }
        }
    }

    fn color_detail_line(&self, line: &str) -> String {
        if line.starts_with("status:") {
            self.palette.yellow(line)
        } else if line.starts_with("stdout:") {
            self.palette.cyan(line)
        } else if line.starts_with("stderr:") {
            self.palette.red(line)
        } else if line.starts_with("source artifact:") || line.starts_with("chunk artifact:") {
            self.palette.cyan(line)
        } else if line.starts_with("generated source:") {
            self.palette.magenta(line)
        } else if line.contains("failed") || line.contains("mismatch") {
            self.palette.red(line)
        } else {
            line.to_owned()
        }
    }
}

pub(crate) fn run<I>(args: I) -> Result<()>
where
    I: IntoIterator,
    I::Item: Into<String>,
{
    let args = args.into_iter().map(Into::into).collect::<Vec<_>>();
    if is_help_request(&args) {
        print_help();
        return Ok(());
    }

    let options = parse_args(args)?;
    let root = workspace_root()?;

    build_unit_case_runner(&root)?;
    let runner = unit_case_runner_path(&root);
    let cases = list_unit_cases(&root, &runner)?;
    let cases = cases
        .into_iter()
        .filter(|case| options.suite == "all" || case.suite == options.suite)
        .filter(|case| options.dialect == "all" || case.dialect == options.dialect)
        .filter(|case| matches_case_filters(case, &options.case_filters))
        .collect::<Vec<_>>();

    if cases.is_empty() {
        let filter_text = if options.case_filters.is_empty() {
            "none".to_owned()
        } else {
            options.case_filters.join(", ")
        };
        bail!(
            "no unit cases matched filters: suite={}, dialect={}, case-filter={filter_text}",
            options.suite,
            options.dialect
        );
    }

    let timeout = Duration::from_secs(options.timeout_seconds);
    let total = cases.len();
    let jobs = options.jobs.min(total).max(1);
    let reporter = Reporter::new(total, &options)?;
    reporter.announce_start(total, &options, jobs);

    let (event_rx, handles) = spawn_workers(
        root,
        runner,
        cases,
        options.output.label().to_owned(),
        options.recompile_rounds,
        timeout,
        jobs,
    )?;

    let mut active = 0usize;
    let mut completed = 0usize;
    let mut failed = 0usize;
    let mut timed_out = 0usize;
    let mut failure_counts = BTreeMap::new();
    let mut worker_error = None;
    let mut total_protos = 0usize;
    let mut failed_protos = 0usize;

    while completed < total && worker_error.is_none() {
        match event_rx.recv() {
            Ok(WorkerEvent::Started { case }) => {
                active += 1;
                reporter.update_progress(
                    completed,
                    total,
                    active,
                    &case,
                    ProgressEventKind::Started,
                );
            }
            Ok(WorkerEvent::Finished { case, execution }) => {
                active = active.saturating_sub(1);
                completed += 1;
                reporter.update_progress(
                    completed,
                    total,
                    active,
                    &case,
                    ProgressEventKind::Finished,
                );

                match execution.outcome {
                    UnitCaseOutcome::Passed => {
                        total_protos += execution.proto_count;
                    }
                    UnitCaseOutcome::Failed => {
                        failed += 1;
                        total_protos += execution.proto_count;
                        failed_protos += execution.failed_proto_tags.len();
                        if let Some(classification) = execution.classification {
                            *failure_counts.entry(classification).or_insert(0) += 1;
                        }
                        reporter.emit_failure(
                            ProgressCounts { completed, total },
                            &case,
                            execution.outcome,
                            execution.rendered_failure.as_deref(),
                            &execution.failed_proto_tags,
                            options.timeout_seconds,
                            options.output,
                        );
                    }
                    UnitCaseOutcome::TimedOut => {
                        failed += 1;
                        timed_out += 1;
                        *failure_counts.entry("timed-out".to_owned()).or_insert(0) += 1;
                        reporter.emit_failure(
                            ProgressCounts { completed, total },
                            &case,
                            execution.outcome,
                            execution.rendered_failure.as_deref(),
                            &execution.failed_proto_tags,
                            options.timeout_seconds,
                            options.output,
                        );
                    }
                }
            }
            Ok(WorkerEvent::WorkerError { case, error }) => {
                worker_error = Some(format!(
                    "worker failed while running {} {} {}: {error}",
                    case.suite, case.dialect, case.path
                ));
            }
            Err(_) => {
                worker_error =
                    Some("worker event channel closed before all cases finished".to_owned());
            }
        }
    }

    for handle in handles {
        match handle.join() {
            Ok(Ok(())) => {}
            Ok(Err(error)) => {
                if worker_error.is_none() {
                    worker_error = Some(error.to_string());
                }
            }
            Err(_) => {
                if worker_error.is_none() {
                    worker_error = Some("unit test worker panicked".to_owned());
                }
            }
        }
    }

    if let Some(error) = worker_error {
        bail!("{error}");
    }

    reporter.finish(total, failed, timed_out, &failure_counts, total_protos, failed_protos);

    if failed == 0 {
        Ok(())
    } else {
        bail!("unit runner failed with {failed} failing case(s)")
    }
}

pub(crate) fn print_help() {
    println!("usage:");
    println!("  cargo unit-test");
    println!("  cargo unit-test <help|--help|-h>");
    println!("                  [--suite <all|case-health|decompile-pipeline-health>]");
    println!("                  [--dialect <all|lua5.1|lua5.2|lua5.3|lua5.4|lua5.5>]");
    println!("                  [--case-filter <substring>]...");
    println!("                  [--output <simple|verbose>] [--timeout-seconds <n>]");
    println!("                  [--progress <auto|on|off>] [--color <auto|always|never>]");
    println!("                  [--verbose]");
    println!("                  [--jobs <n>]");
    println!("                  [--recompile-rounds <n>]");
}

fn parse_args<I>(args: I) -> Result<Options>
where
    I: IntoIterator,
    I::Item: Into<String>,
{
    let args = args.into_iter().map(Into::into).collect::<Vec<_>>();
    let mut options = Options {
        suite: "all".to_owned(),
        dialect: "all".to_owned(),
        case_filters: Vec::new(),
        output: parse_env_or_default(OUTPUT_ENV, "simple", FailureOutputMode::parse)?,
        timeout_seconds: 10,
        progress: parse_env_or_default(PROGRESS_ENV, "auto", ProgressMode::parse)?,
        color: parse_env_or_default(COLOR_ENV, "auto", ColorMode::parse)?,
        plain_progress_detail: PlainProgressDetail::Sparse,
        jobs: 1,
        recompile_rounds: 1,
    };

    let mut cursor = 0;
    while cursor < args.len() {
        match args[cursor].as_str() {
            "--suite" => {
                cursor += 1;
                options.suite = args
                    .get(cursor)
                    .context("missing value for `--suite`")?
                    .clone();
            }
            "--dialect" => {
                cursor += 1;
                options.dialect = args
                    .get(cursor)
                    .context("missing value for `--dialect`")?
                    .clone();
            }
            "--case-filter" => {
                cursor += 1;
                options.case_filters.push(
                    args.get(cursor)
                        .context("missing value for `--case-filter`")?
                        .clone(),
                );
            }
            "--output" => {
                cursor += 1;
                let value = args.get(cursor).context("missing value for `--output`")?;
                options.output = FailureOutputMode::parse(value)?;
            }
            "--timeout-seconds" => {
                cursor += 1;
                let value = args
                    .get(cursor)
                    .context("missing value for `--timeout-seconds`")?;
                options.timeout_seconds = value
                    .parse::<u64>()
                    .with_context(|| format!("invalid timeout seconds: {value}"))?;
                if options.timeout_seconds == 0 {
                    bail!("timeout seconds must be greater than zero");
                }
            }
            "--progress" => {
                cursor += 1;
                let value = args.get(cursor).context("missing value for `--progress`")?;
                options.progress = ProgressMode::parse(value)?;
            }
            "--color" => {
                cursor += 1;
                let value = args.get(cursor).context("missing value for `--color`")?;
                options.color = ColorMode::parse(value)?;
            }
            "--jobs" => {
                cursor += 1;
                let value = args.get(cursor).context("missing value for `--jobs`")?;
                options.jobs = value
                    .parse::<usize>()
                    .with_context(|| format!("invalid jobs value: {value}"))?;
                if options.jobs == 0 {
                    bail!("jobs must be greater than zero");
                }
            }
            "--recompile-rounds" => {
                cursor += 1;
                let value = args
                    .get(cursor)
                    .context("missing value for `--recompile-rounds`")?;
                options.recompile_rounds = value
                    .parse::<u32>()
                    .with_context(|| format!("invalid recompile rounds: {value}"))?;
            }
            "--verbose" => {
                options.plain_progress_detail = PlainProgressDetail::Verbose;
            }
            other => bail!("unsupported `test-unit` option: {other}"),
        }
        cursor += 1;
    }

    Ok(options)
}

fn is_help_request(args: &[String]) -> bool {
    matches!(args, [flag] if matches!(flag.as_str(), "help" | "--help" | "-h"))
}

fn parse_env_or_default<T>(
    key: &str,
    default: &str,
    parse: impl Fn(&str) -> Result<T>,
) -> Result<T> {
    match env::var(key) {
        Ok(value) => parse(value.trim()).with_context(|| format!("invalid {key} value")),
        Err(env::VarError::NotPresent) => parse(default),
        Err(error) => bail!("failed to read {key}: {error}"),
    }
}

fn progress_is_enabled(mode: ProgressMode) -> bool {
    match mode {
        ProgressMode::On => true,
        ProgressMode::Off => false,
        ProgressMode::Auto => stderr_supports_live_updates(),
    }
}

fn color_is_enabled(mode: ColorMode) -> bool {
    match mode {
        ColorMode::Always => true,
        ColorMode::Never => false,
        ColorMode::Auto => env::var_os("NO_COLOR").is_none() && stderr_supports_live_updates(),
    }
}

fn stderr_supports_live_updates() -> bool {
    io::stderr().is_terminal() && env::var("TERM").map_or(true, |term| term != "dumb")
}

fn matches_case_filters(case: &UnitCaseDescriptor, case_filters: &[String]) -> bool {
    case_filters.is_empty()
        || case_filters
            .iter()
            .any(|case_filter| case.path.contains(case_filter))
}

fn sorted_failure_counts(failure_counts: &BTreeMap<String, usize>) -> Vec<(&str, usize)> {
    let mut entries = failure_counts
        .iter()
        .map(|(label, count)| (label.as_str(), *count))
        .collect::<Vec<_>>();
    entries.sort_by(|left, right| right.1.cmp(&left.1).then_with(|| left.0.cmp(right.0)));
    entries
}

fn workspace_root() -> Result<PathBuf> {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .map(Path::to_path_buf)
        .context("failed to resolve workspace root")
}

fn build_unit_case_runner(root: &Path) -> Result<()> {
    run_command(
        "cargo",
        [
            "build",
            "--quiet",
            "-p",
            "unluac-test-support",
            "--bin",
            "unit_case_runner",
        ],
        root,
    )
}

fn unit_case_runner_path(root: &Path) -> PathBuf {
    root.join("target")
        .join("debug")
        .join(format!("unit_case_runner{}", std::env::consts::EXE_SUFFIX))
}

fn list_unit_cases(root: &Path, runner: &Path) -> Result<Vec<UnitCaseDescriptor>> {
    let output = Command::new(runner)
        .arg("--list")
        .current_dir(root)
        .output()
        .with_context(|| format!("failed to spawn `{}`", runner.display()))?;

    if !output.status.success() {
        bail!(
            "`{}` --list failed with status {}",
            runner.display(),
            output.status
        );
    }

    let stdout = String::from_utf8(output.stdout).context("unit case list is not valid UTF-8")?;
    stdout
        .lines()
        .map(|line| {
            let mut parts = line.splitn(3, '\t');
            let suite = parts
                .next()
                .context("missing suite column in unit case list")?;
            let dialect = parts
                .next()
                .context("missing dialect column in unit case list")?;
            let path = parts
                .next()
                .context("missing path column in unit case list")?;
            Ok(UnitCaseDescriptor {
                suite: suite.to_owned(),
                dialect: dialect.to_owned(),
                path: path.to_owned(),
            })
        })
        .collect()
}

type WorkerHandles = Vec<thread::JoinHandle<Result<()>>>;
type SpawnedWorkers = (mpsc::Receiver<WorkerEvent>, WorkerHandles);

fn spawn_workers(
    root: PathBuf,
    runner: PathBuf,
    cases: Vec<UnitCaseDescriptor>,
    output_mode: String,
    recompile_rounds: u32,
    timeout: Duration,
    jobs: usize,
) -> Result<SpawnedWorkers> {
    let (task_tx, task_rx) = mpsc::channel::<ScheduledCase>();
    let (event_tx, event_rx) = mpsc::channel::<WorkerEvent>();
    let task_rx = Arc::new(Mutex::new(task_rx));
    let mut handles = Vec::with_capacity(jobs);

    for _ in 0..jobs {
        let root = root.clone();
        let runner = runner.clone();
        let output_mode = output_mode.clone();
        let task_rx = Arc::clone(&task_rx);
        let event_tx = event_tx.clone();
        handles.push(thread::spawn(move || {
            loop {
                let scheduled = {
                    let receiver = task_rx
                        .lock()
                        .map_err(|_| anyhow::anyhow!("task receiver mutex poisoned"))?;
                    match receiver.recv() {
                        Ok(scheduled) => scheduled,
                        Err(_) => break,
                    }
                };

                event_tx
                    .send(WorkerEvent::Started {
                        case: scheduled.case.clone(),
                    })
                    .map_err(|_| anyhow::anyhow!("worker event channel closed"))?;

                match run_unit_case_with_timeout(
                    &root,
                    &runner,
                    &scheduled.case,
                    &output_mode,
                    recompile_rounds,
                    timeout,
                ) {
                    Ok(execution) => event_tx
                        .send(WorkerEvent::Finished {
                            case: scheduled.case,
                            execution,
                        })
                        .map_err(|_| anyhow::anyhow!("worker event channel closed"))?,
                    Err(error) => {
                        let error = error.to_string();
                        let _ = event_tx.send(WorkerEvent::WorkerError {
                            case: scheduled.case,
                            error,
                        });
                        break;
                    }
                }
            }

            Ok(())
        }));
    }

    drop(event_tx);

    for case in cases {
        task_tx.send(ScheduledCase { case }).map_err(|_| {
            anyhow::anyhow!("worker task channel closed before scheduling all cases")
        })?;
    }
    drop(task_tx);

    Ok((event_rx, handles))
}

fn run_unit_case_with_timeout(
    root: &Path,
    runner: &Path,
    case: &UnitCaseDescriptor,
    output_mode: &str,
    recompile_rounds: u32,
    timeout: Duration,
) -> Result<UnitCaseExecution> {
    let mut child = Command::new(runner)
        .args([
            "--report",
            "machine",
            "--suite",
            case.suite.as_str(),
            "--dialect",
            case.dialect.as_str(),
            "--case",
            case.path.as_str(),
        ])
        .env(OUTPUT_ENV, output_mode)
        .env(RECOMPILE_ROUNDS_ENV, recompile_rounds.to_string())
        .current_dir(root)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| format!("failed to spawn `{}`", runner.display()))?;

    let start = Instant::now();
    loop {
        if let Some(status) = child
            .try_wait()
            .with_context(|| format!("failed to poll `{}`", runner.display()))?
        {
            let output = child
                .wait_with_output()
                .with_context(|| format!("failed to read `{}` output", runner.display()))?;
            return match status.code() {
                Some(0) => {
                    let proto_count = parse_machine_success(&output);
                    Ok(UnitCaseExecution {
                        outcome: UnitCaseOutcome::Passed,
                        classification: None,
                        rendered_failure: None,
                        proto_count,
                        failed_proto_tags: Vec::new(),
                    })
                }
                Some(1) => {
                    let failure = parse_machine_failure(&output)?;
                    Ok(UnitCaseExecution {
                        outcome: UnitCaseOutcome::Failed,
                        classification: Some(failure.classification),
                        rendered_failure: Some(failure.rendered),
                        proto_count: failure.proto_count,
                        failed_proto_tags: failure.failed_proto_tags,
                    })
                }
                _ => bail!(
                    "unit case runner exited unexpectedly for {} {} {} with status {}",
                    case.suite,
                    case.dialect,
                    case.path,
                    status
                ),
            };
        }

        if start.elapsed() >= timeout {
            child
                .kill()
                .with_context(|| format!("failed to kill timed out `{}`", runner.display()))?;
            let output = child.wait_with_output().with_context(|| {
                format!("failed to read timed out `{}` output", runner.display())
            })?;
            let rendered_failure = preferred_child_output(&output);
            return Ok(UnitCaseExecution {
                outcome: UnitCaseOutcome::TimedOut,
                classification: Some("timed-out".to_owned()),
                rendered_failure: (!rendered_failure.trim().is_empty()).then_some(rendered_failure),
                proto_count: 0,
                failed_proto_tags: Vec::new(),
            });
        }

        thread::sleep(Duration::from_millis(50));
    }
}

/// 解析 machine 模式成功输出中的 `proto-count` 行。
fn parse_machine_success(output: &std::process::Output) -> usize {
    let stdout = String::from_utf8_lossy(&output.stdout);
    for line in stdout.lines() {
        if let Some(v) = line.strip_prefix("proto-count\t") {
            return v.trim().parse().unwrap_or(0);
        }
    }
    0
}

/// 解析 machine 模式失败输出：支持 `kind`、`proto-count`、`failed-protos` 三种头部行，
/// 余下内容作为渲染后的失败详情。
fn parse_machine_failure(output: &std::process::Output) -> Result<MachineFailure> {
    let stdout = String::from_utf8(output.stdout.clone())
        .context("unit case runner machine output is not valid UTF-8")?;
    let trimmed = stdout.trim_end_matches('\n');

    let mut classification = None;
    let mut proto_count = 0usize;
    let mut failed_proto_tags = Vec::new();
    let mut body_start = 0usize;

    for (i, line) in trimmed.lines().enumerate() {
        if let Some(v) = line.strip_prefix("kind\t") {
            classification = Some(v.trim().to_owned());
            body_start = i + 1;
        } else if let Some(v) = line.strip_prefix("proto-count\t") {
            proto_count = v.trim().parse().unwrap_or(0);
            body_start = i + 1;
        } else if let Some(v) = line.strip_prefix("failed-protos\t") {
            failed_proto_tags = v
                .split(',')
                .map(|s| s.trim().to_owned())
                .filter(|s| !s.is_empty())
                .collect();
            body_start = i + 1;
        } else {
            break;
        }
    }

    let classification = classification
        .context("unit case runner machine output is missing kind header")?;
    let rendered: String = trimmed
        .lines()
        .skip(body_start)
        .collect::<Vec<_>>()
        .join("\n");
    let rendered = rendered.trim().to_owned();
    if classification.is_empty() || rendered.is_empty() {
        bail!("unit case runner machine output contained an empty failure payload");
    }

    Ok(MachineFailure {
        classification,
        rendered,
        proto_count,
        failed_proto_tags,
    })
}

fn preferred_child_output(output: &std::process::Output) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_owned();
    if !stderr.is_empty() { stderr } else { stdout }
}

fn progress_message(
    palette: Palette,
    completed: usize,
    total: usize,
    active: usize,
    case: &UnitCaseDescriptor,
) -> String {
    format!(
        "[{completed}/{total}]\tactive: {active}\tdialect: {}\tcase: {}",
        palette.cyan(&case.dialect),
        case.path
    )
}

fn sparse_progress_message(
    palette: Palette,
    completed: usize,
    total: usize,
    active: usize,
) -> String {
    format!(
        "[{completed}/{total}]\tactive: {active}\t{}",
        palette.cyan("progress")
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ProgressEventKind {
    Started,
    Finished,
}

fn should_emit_sparse_plain_progress(
    event: ProgressEventKind,
    completed: usize,
    total: usize,
) -> bool {
    matches!(event, ProgressEventKind::Finished)
        && completed > 0
        && (completed == total || completed.is_multiple_of(100))
}

fn normalize_runner_failure(
    raw: &str,
    case: &UnitCaseDescriptor,
    output_mode: FailureOutputMode,
) -> String {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return "runner exited with failure but did not report details".to_owned();
    }

    match output_mode {
        FailureOutputMode::Simple => trimmed
            .strip_prefix(&format!("{} :: ", case.path))
            .unwrap_or(trimmed)
            .to_owned(),
        FailureOutputMode::Verbose => trimmed
            .strip_prefix(&format!("case: {}\n", case.path))
            .unwrap_or(trimmed)
            .to_owned(),
    }
}

fn run_command<I, S>(program: &str, args: I, cwd: &Path) -> Result<()>
where
    I: IntoIterator<Item = S>,
    S: AsRef<std::ffi::OsStr>,
{
    let status = Command::new(program)
        .args(args)
        .current_dir(cwd)
        .status()
        .with_context(|| format!("failed to spawn `{program}` in {}", cwd.display()))?;

    if status.success() {
        Ok(())
    } else {
        bail!("`{program}` failed with status {status}")
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ColorMode, FailureOutputMode, MachineFailure, Options, PlainProgressDetail, ProgressMode,
        is_help_request, matches_case_filters, normalize_runner_failure, parse_args,
        parse_machine_failure, sorted_failure_counts,
    };
    use std::os::unix::process::ExitStatusExt;

    #[test]
    fn parse_args_should_accept_options() {
        let options = parse_args([
            "--suite",
            "case-health",
            "--dialect",
            "lua5.4",
            "--case-filter",
            "control_flow",
            "--case-filter",
            "04_generic_for",
            "--output",
            "verbose",
            "--timeout-seconds",
            "12",
            "--progress",
            "off",
            "--color",
            "always",
            "--verbose",
            "--jobs",
            "4",
            "--recompile-rounds",
            "2",
        ])
        .expect("test-unit options should parse");

        assert_eq!(
            options,
            Options {
                suite: "case-health".to_owned(),
                dialect: "lua5.4".to_owned(),
                case_filters: vec!["control_flow".to_owned(), "04_generic_for".to_owned()],
                output: FailureOutputMode::Verbose,
                timeout_seconds: 12,
                progress: ProgressMode::Off,
                color: ColorMode::Always,
                plain_progress_detail: PlainProgressDetail::Verbose,
                jobs: 4,
                recompile_rounds: 2,
            }
        );
    }

    #[test]
    fn parse_args_should_reject_zero_timeout() {
        let error =
            parse_args(["--timeout-seconds", "0"]).expect_err("zero timeout should be rejected");

        assert_eq!(
            error.to_string(),
            "timeout seconds must be greater than zero"
        );
    }

    #[test]
    fn parse_args_should_reject_zero_jobs() {
        let error = parse_args(["--jobs", "0"]).expect_err("zero jobs should be rejected");

        assert_eq!(error.to_string(), "jobs must be greater than zero");
    }

    #[test]
    fn help_request_should_recognize_all_supported_spellings() {
        assert!(is_help_request(&["help".to_owned()]));
        assert!(is_help_request(&["--help".to_owned()]));
        assert!(is_help_request(&["-h".to_owned()]));
        assert!(!is_help_request(&[]));
        assert!(!is_help_request(&["--suite".to_owned(), "all".to_owned()]));
    }

    #[test]
    fn sparse_plain_progress_should_only_emit_on_milestones() {
        assert!(!super::should_emit_sparse_plain_progress(
            super::ProgressEventKind::Started,
            100,
            500,
        ));
        assert!(!super::should_emit_sparse_plain_progress(
            super::ProgressEventKind::Finished,
            99,
            500,
        ));
        assert!(super::should_emit_sparse_plain_progress(
            super::ProgressEventKind::Finished,
            100,
            500,
        ));
        assert!(super::should_emit_sparse_plain_progress(
            super::ProgressEventKind::Finished,
            500,
            500,
        ));
    }

    #[test]
    fn normalize_runner_failure_should_strip_simple_case_prefix() {
        let case = super::UnitCaseDescriptor {
            suite: "case-health".to_owned(),
            dialect: "lua5.4".to_owned(),
            path: "tests/example.lua".to_owned(),
        };
        let rendered = normalize_runner_failure(
            "tests/example.lua :: source execution failed: bad",
            &case,
            FailureOutputMode::Simple,
        );

        assert_eq!(rendered, "source execution failed: bad");
    }

    #[test]
    fn parse_machine_failure_should_decode_kind_and_rendered_output() {
        let output = std::process::Output {
            status: std::process::ExitStatus::from_raw(256),
            stdout: b"kind\tgenerated-output-mismatch\ntests/example.lua :: mismatch".to_vec(),
            stderr: Vec::new(),
        };
        let failure = parse_machine_failure(&output).expect("machine output should parse");

        assert_eq!(
            failure,
            MachineFailure {
                classification: "generated-output-mismatch".to_owned(),
                rendered: "tests/example.lua :: mismatch".to_owned(),
                proto_count: 0,
                failed_proto_tags: Vec::new(),
            }
        );
    }

    #[test]
    fn parse_machine_failure_should_decode_proto_stats() {
        let output = std::process::Output {
            status: std::process::ExitStatus::from_raw(256),
            stdout: b"kind\tgenerated-output-mismatch\nproto-count\t5\nfailed-protos\tcommon_01#2,common_01#4\ntests/example.lua :: mismatch".to_vec(),
            stderr: Vec::new(),
        };
        let failure = parse_machine_failure(&output).expect("machine output should parse");

        assert_eq!(
            failure,
            MachineFailure {
                classification: "generated-output-mismatch".to_owned(),
                rendered: "tests/example.lua :: mismatch".to_owned(),
                proto_count: 5,
                failed_proto_tags: vec!["common_01#2".to_owned(), "common_01#4".to_owned()],
            }
        );
    }

    #[test]
    fn matches_case_filters_should_accept_any_substring_match() {
        let case = super::UnitCaseDescriptor {
            suite: "case-health".to_owned(),
            dialect: "lua5.4".to_owned(),
            path: "tests/lua_cases/common/control_flow/04_generic_for.lua".to_owned(),
        };

        assert!(matches_case_filters(&case, &[]));
        assert!(matches_case_filters(&case, &["control_flow".to_owned()]));
        assert!(matches_case_filters(
            &case,
            &["not-here".to_owned(), "04_generic_for".to_owned()]
        ));
        assert!(!matches_case_filters(&case, &["tables".to_owned()]));
    }

    #[test]
    fn sorted_failure_counts_should_order_by_count_then_label() {
        let counts = std::collections::BTreeMap::from([
            ("generated-output-mismatch".to_owned(), 2usize),
            ("timed-out".to_owned(), 5usize),
            ("decompile-failed".to_owned(), 5usize),
        ]);

        assert_eq!(
            sorted_failure_counts(&counts),
            vec![
                ("decompile-failed", 5),
                ("timed-out", 5),
                ("generated-output-mismatch", 2),
            ]
        );
    }
}
