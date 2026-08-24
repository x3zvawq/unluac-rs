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

mod args;
mod reporter;
mod run;
mod workers;

use args::*;
use reporter::*;
pub(crate) use run::run;
use workers::*;

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
    variant: Option<String>,
}

impl UnitCaseDescriptor {
    fn display_path(&self) -> String {
        self.variant.as_ref().map_or_else(
            || self.path.clone(),
            |variant| format!("{} [{variant}]", self.path),
        )
    }
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

#[cfg(test)]
mod tests {
    use super::{
        ColorMode, FailureOutputMode, MachineFailure, Options, PlainProgressDetail, ProgressMode,
        is_help_request, matches_case_filters, normalize_runner_failure, parse_args,
        parse_machine_failure, sorted_failure_counts,
    };
    #[cfg(unix)]
    use std::os::unix::process::ExitStatusExt;
    #[cfg(windows)]
    use std::os::windows::process::ExitStatusExt;

    #[test]
    fn parse_args_should_accept_options() {
        let options = parse_args([
            "--suite",
            "unit",
            "--dialect",
            "lua5.4",
            "--case-filter",
            "common_04",
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
                suite: "unit".to_owned(),
                dialect: "lua5.4".to_owned(),
                case_filters: vec!["common_04".to_owned(), "04_generic_for".to_owned()],
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
            suite: "unit".to_owned(),
            dialect: "lua5.4".to_owned(),
            path: "tests/example.lua".to_owned(),
            variant: None,
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
            suite: "unit".to_owned(),
            dialect: "lua5.4".to_owned(),
            path: "tests/unit-case/common_04_generic_for.lua".to_owned(),
            variant: None,
        };

        assert!(matches_case_filters(&case, &[]));
        assert!(matches_case_filters(&case, &["common_04".to_owned()]));
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
