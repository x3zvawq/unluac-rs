//! 驱动 Lua 源码矩阵的筛选、并发执行与进度汇总；实例身份由同次构建的 runner 签发，
//! 本层只传递身份并展示描述，不重新拼装编译选项或语义验证合同。

use std::collections::BTreeMap;
use std::env;
use std::io::{self, IsTerminal, Read};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output, Stdio};
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicBool, Ordering},
    mpsc,
};
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
const PROGRESS_HEARTBEAT_INTERVAL: Duration = Duration::from_secs(10);

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
    category: String,
    tags: Vec<String>,
    list: bool,
    list_json: bool,
    report_json: Option<PathBuf>,
    dialect: String,
    case_filters: Vec<String>,
    output: FailureOutputMode,
    timeout_seconds: u64,
    progress: ProgressMode,
    color: ColorMode,
    plain_progress_detail: PlainProgressDetail,
    jobs: usize,
    profile: String,
    recompile_rounds: u32,
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct CaseDescriptor {
    id: String,
    category: String,
    dialect: String,
    path: String,
    variant: Option<String>,
    tags: Vec<String>,
    purpose: String,
    configuration: String,
    readability_assertions: usize,
    ast_assertions: usize,
}

impl CaseDescriptor {
    fn catalog_json(&self) -> serde_json::Value {
        serde_json::json!({
            "id": self.id,
            "type": self.category,
            "dialect": self.dialect,
            "path": self.path,
            "variant": self.variant,
            "tags": self.tags,
            "purpose": self.purpose,
            "configuration": self.configuration,
            "readability_assertions": self.readability_assertions,
            "ast_assertions": self.ast_assertions,
        })
    }

    fn display_path(&self) -> String {
        self.variant.as_ref().map_or_else(
            || self.path.clone(),
            |variant| format!("{} [{variant}]", self.path),
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CaseOutcome {
    Passed,
    Failed,
    TimedOut,
}

#[derive(Debug)]
struct CaseExecution {
    elapsed: Duration,
    outcome: CaseOutcome,
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
    case: CaseDescriptor,
}

#[derive(Debug)]
enum WorkerEvent {
    Started {
        case: CaseDescriptor,
    },
    Finished {
        case: CaseDescriptor,
        execution: CaseExecution,
    },
    WorkerError {
        case: CaseDescriptor,
        error: String,
    },
}
