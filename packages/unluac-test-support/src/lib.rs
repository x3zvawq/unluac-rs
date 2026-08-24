//! 这个 crate 承载仓库源码 case 的统一端到端测试流水线。
//!
//! unit 与 regression 共用官方 toolchain 编译、反编译、回编译、执行和可读性/结构合同；
//! 少数 VM 内建协议或普通小样例难以稳定触发的宽度边界，只能由 manifest 显式授权，
//! 再从同一源码通过 pinned 运行时动态导出临时 chunk。这里不提交 bytecode fixture，
//! 也不改变业务 lowering。
#![allow(dead_code)]

use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{
    OnceLock,
    atomic::{AtomicUsize, Ordering},
};

use unluac::ast::AstLowerError;
use unluac::decompile::{
    DecompileDialect, DecompileError, DecompileOptions, DecompileStage, decompile,
};
use unluac::generate::{GenerateMode, GeneratedChunkKind, LuauVectorConstructor, LuauVectorSize};
use unluac::parser::{DialectConstPoolExtra, ParseMode};
use unluac::structure::{
    ControlFlowFeature, LoopVmProtocol, RegionId, RegionPlan, StructureFacts, StructurePlan,
    UnstructuredLayoutItem,
};
use unluac::transformer::{
    AccessBase, AccessKey, CallKind, GetTableKind, LowInstr, LoweredChunk, LoweredProto, Reg,
    SetTableKind, TypeGuardKind, ValueOperand, ValuePack, format_low_instr,
};

#[allow(dead_code)]
mod case_manifest;
pub use case_manifest::{LuaCaseDialect, LuaCaseManifestEntry, LuaCaseVariant};
use case_manifest::{
    LuaCaseExpectation, LuaCaseLoopProtocol, LuaCaseOptions, LuaCaseStructureContract,
    regression_cases, unit_cases,
};

#[derive(Debug, Clone, Eq, PartialEq)]
struct LuaCommandOutput {
    pub(crate) status_code: Option<i32>,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: Vec<u8>,
}

impl LuaCommandOutput {
    fn success(&self) -> bool {
        self.status_code == Some(0)
    }

    fn render(&self) -> String {
        format!(
            "status: {}\nstdout:\n{}\nstderr:\n{}",
            render_status_code(self.status_code),
            render_bytes(&self.stdout),
            render_bytes(&self.stderr)
        )
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum LuaCompilerProtocol {
    LuacStyle,
    LuaJitBytecodeTool,
    LuauBinaryStdout,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct LuaToolchain {
    runtime_name: &'static str,
    compiler_name: &'static str,
    compiler_protocol: LuaCompilerProtocol,
    chunk_extension: &'static str,
    can_run_compiled_chunks: bool,
}

impl LuaToolchain {
    const fn stock_puc_lua() -> Self {
        Self {
            runtime_name: "lua",
            compiler_name: "luac",
            compiler_protocol: LuaCompilerProtocol::LuacStyle,
            chunk_extension: "luac",
            can_run_compiled_chunks: true,
        }
    }

    const fn luau() -> Self {
        Self {
            runtime_name: "luau",
            compiler_name: "luau-compile",
            compiler_protocol: LuaCompilerProtocol::LuauBinaryStdout,
            chunk_extension: "luau",
            can_run_compiled_chunks: false,
        }
    }

    const fn luajit() -> Self {
        Self {
            runtime_name: "luajit",
            compiler_name: "luac",
            compiler_protocol: LuaCompilerProtocol::LuaJitBytecodeTool,
            chunk_extension: "luajit",
            can_run_compiled_chunks: true,
        }
    }
}

fn lua_toolchain(dialect_label: &str) -> Result<LuaToolchain, String> {
    match dialect_label {
        "lua5.1" | "lua5.2" | "lua5.3" | "lua5.4" | "lua5.5" => Ok(LuaToolchain::stock_puc_lua()),
        "luajit" => Ok(LuaToolchain::luajit()),
        "luau" => Ok(LuaToolchain::luau()),
        _ => Err(format!("unknown Lua dialect label: {dialect_label}")),
    }
}

fn repo_relative_display(path: &Path) -> String {
    path.strip_prefix(repo_root())
        .map(|relative| relative.display().to_string())
        .unwrap_or_else(|_| sanitize_repo_paths(&path.display().to_string()))
}

const TEST_OUTPUT_ENV: &str = "UNLUAC_TEST_OUTPUT";
const RECOMPILE_ROUNDS_ENV: &str = "UNLUAC_TEST_RECOMPILE_ROUNDS";

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum TestOutputMode {
    Simple,
    Verbose,
}

impl TestOutputMode {
    fn parse(raw: &str) -> Result<Self, String> {
        match raw {
            "simple" => Ok(Self::Simple),
            "verbose" => Ok(Self::Verbose),
            _ => Err(format!(
                "invalid {TEST_OUTPUT_ENV}={raw:?}, expected one of: simple, verbose"
            )),
        }
    }
}

static TEST_OUTPUT_MODE: OnceLock<TestOutputMode> = OnceLock::new();

fn test_output_mode() -> TestOutputMode {
    *TEST_OUTPUT_MODE.get_or_init(|| match std::env::var(TEST_OUTPUT_ENV) {
        Ok(raw) => TestOutputMode::parse(raw.trim()).unwrap_or_else(|error| panic!("{error}")),
        Err(std::env::VarError::NotPresent) => TestOutputMode::Simple,
        Err(error) => panic!("failed to read {TEST_OUTPUT_ENV}: {error}"),
    })
}

static RECOMPILE_ROUNDS: OnceLock<u32> = OnceLock::new();

fn recompile_rounds() -> u32 {
    *RECOMPILE_ROUNDS.get_or_init(|| match std::env::var(RECOMPILE_ROUNDS_ENV) {
        Ok(raw) => raw
            .trim()
            .parse::<u32>()
            .unwrap_or_else(|error| panic!("invalid {RECOMPILE_ROUNDS_ENV}={raw:?}: {error}")),
        Err(std::env::VarError::NotPresent) => 0,
        Err(error) => panic!("failed to read {RECOMPILE_ROUNDS_ENV}: {error}"),
    })
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum FailureKind {
    RunSourceFailed,
    SourceExecutionFailed,
    CompileSourceFailed,
    SourceCompilationFailed,
    RunCompiledChunkFailed,
    CompiledChunkExecutionFailed,
    SourceChunkOutputMismatch,
    BaselineFailed,
    AutoDialectMismatch,
    DecompileFailed,
    GenerateWithoutSource,
    GeneratedChunkKindMismatch,
    WriteGeneratedSourceFailed,
    CompileGeneratedSourceFailed,
    GeneratedSourceCompilationFailed,
    RunGeneratedChunkFailed,
    GeneratedChunkExecutionFailed,
    GeneratedOutputMismatch,
    RecompileDecompileFailed,
    RecompileGeneratedSourceCompilationFailed,
    RecompileGeneratedChunkExecutionFailed,
    RecompileGeneratedOutputMismatch,
    RecompileConvergenceMismatch,
    ReadabilityAssertionFailed,
    StructureContractAssertionFailed,
    LuaJitBuiltinContractAssertionFailed,
    LuaJitMethodProtocolContractAssertionFailed,
}

impl FailureKind {
    pub const fn label(self) -> &'static str {
        match self {
            Self::RunSourceFailed => "run-source-failed",
            Self::SourceExecutionFailed => "source-execution-failed",
            Self::CompileSourceFailed => "compile-source-failed",
            Self::SourceCompilationFailed => "source-compilation-failed",
            Self::RunCompiledChunkFailed => "run-compiled-chunk-failed",
            Self::CompiledChunkExecutionFailed => "compiled-chunk-execution-failed",
            Self::SourceChunkOutputMismatch => "source-chunk-output-mismatch",
            Self::BaselineFailed => "baseline-failed",
            Self::AutoDialectMismatch => "auto-dialect-mismatch",
            Self::DecompileFailed => "decompile-failed",
            Self::GenerateWithoutSource => "generate-without-source",
            Self::GeneratedChunkKindMismatch => "generated-chunk-kind-mismatch",
            Self::WriteGeneratedSourceFailed => "write-generated-source-failed",
            Self::CompileGeneratedSourceFailed => "compile-generated-source-failed",
            Self::GeneratedSourceCompilationFailed => "generated-source-compilation-failed",
            Self::RunGeneratedChunkFailed => "run-generated-chunk-failed",
            Self::GeneratedChunkExecutionFailed => "generated-chunk-execution-failed",
            Self::GeneratedOutputMismatch => "generated-output-mismatch",
            Self::RecompileDecompileFailed => "recompile-decompile-failed",
            Self::RecompileGeneratedSourceCompilationFailed => {
                "recompile-generated-source-compilation-failed"
            }
            Self::RecompileGeneratedChunkExecutionFailed => {
                "recompile-generated-chunk-execution-failed"
            }
            Self::RecompileGeneratedOutputMismatch => "recompile-generated-output-mismatch",
            Self::RecompileConvergenceMismatch => "recompile-convergence-mismatch",
            Self::ReadabilityAssertionFailed => "readability-assertion-failed",
            Self::StructureContractAssertionFailed => "structure-contract-assertion-failed",
            Self::LuaJitBuiltinContractAssertionFailed => {
                "luajit-builtin-contract-assertion-failed"
            }
            Self::LuaJitMethodProtocolContractAssertionFailed => {
                "luajit-method-protocol-contract-assertion-failed"
            }
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TestSuccess {
    pub proto_count: usize,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TestFailure {
    kind: FailureKind,
    summary: String,
    detail: String,
    proto_count: usize,
    failed_proto_tags: Vec<String>,
}

impl TestFailure {
    fn new(kind: FailureKind, summary: impl Into<String>, detail: impl Into<String>) -> Self {
        Self {
            kind,
            summary: summary.into(),
            detail: detail.into(),
            proto_count: 0,
            failed_proto_tags: Vec::new(),
        }
    }

    fn with_proto_stats(mut self, proto_count: usize, failed_proto_tags: Vec<String>) -> Self {
        self.proto_count = proto_count;
        self.failed_proto_tags = failed_proto_tags;
        self
    }

    pub fn kind(&self) -> FailureKind {
        self.kind
    }

    pub fn summary(&self) -> &str {
        &self.summary
    }

    pub fn detail(&self) -> &str {
        &self.detail
    }

    pub fn proto_count(&self) -> usize {
        self.proto_count
    }

    pub fn failed_proto_tags(&self) -> &[String] {
        &self.failed_proto_tags
    }
}

fn assert_auto_dialect(
    phase: &str,
    actual: DecompileDialect,
    expected: DecompileDialect,
    case_path: &str,
) -> Result<(), TestFailure> {
    if actual == expected {
        return Ok(());
    }

    Err(TestFailure::new(
        FailureKind::AutoDialectMismatch,
        format!("{phase} auto dialect mismatch: expected {expected}, got {actual}"),
        format!("{phase} auto dialect mismatch for {case_path}: expected {expected}, got {actual}"),
    ))
}

pub fn format_case_failure(path: &str, failure: &TestFailure) -> String {
    match test_output_mode() {
        TestOutputMode::Simple => format!("{path} :: {}", failure.summary()),
        TestOutputMode::Verbose => format!("case: {path}\n{}", failure.detail()),
    }
}

fn failure_separator() -> &'static str {
    match test_output_mode() {
        TestOutputMode::Simple => "\n",
        TestOutputMode::Verbose => "\n\n",
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum UnitSuite {
    Unit,
    Regression,
}

impl UnitSuite {
    pub fn label(self) -> &'static str {
        match self {
            Self::Unit => "unit",
            Self::Regression => "regression",
        }
    }

    pub fn parse(value: &str) -> Result<Self, String> {
        match value {
            "unit" => Ok(Self::Unit),
            "regression" => Ok(Self::Regression),
            _ => Err(format!(
                "unknown test suite: {value} (expected `unit` or `regression`)"
            )),
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct UnitCaseSpec {
    pub suite: UnitSuite,
    pub entry: LuaCaseManifestEntry,
}

pub fn unit_case_specs() -> Vec<UnitCaseSpec> {
    unit_cases()
        .map(|entry| UnitCaseSpec {
            suite: UnitSuite::Unit,
            entry,
        })
        .chain(regression_cases().map(|entry| UnitCaseSpec {
            suite: UnitSuite::Regression,
            entry,
        }))
        .collect()
}

pub fn find_unit_case_spec(
    suite: UnitSuite,
    dialect_label: &str,
    path: &str,
    variant_label: Option<&str>,
) -> Option<UnitCaseSpec> {
    unit_case_specs().into_iter().find(|spec| {
        spec.suite == suite
            && <&'static str>::from(spec.entry.dialect) == dialect_label
            && spec.entry.path == path
            && spec.entry.variant.map(LuaCaseVariant::label) == variant_label
    })
}

pub fn run_unit_case(spec: UnitCaseSpec) -> Result<TestSuccess, TestFailure> {
    run_pipeline_case(spec.suite, &spec.entry)
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct CaseBaseline {
    pub(crate) source_output: LuaCommandOutput,
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum ReadabilityAssertion {
    Contains {
        line: usize,
        needle: String,
    },
    NotContains {
        line: usize,
        needle: String,
    },
    Order {
        line: usize,
        before: String,
        after: String,
    },
    MaxLineLength {
        line: usize,
        max: usize,
    },
}

#[path = "support/chunk_patch.rs"]
mod chunk_patch;
#[path = "support/compile.rs"]
mod compile;
#[path = "support/luajit_contracts.rs"]
mod luajit_contracts;
#[path = "support/output_diff.rs"]
mod output_diff;
#[path = "support/pipeline.rs"]
mod pipeline;
#[path = "support/readability.rs"]
mod readability;
#[path = "support/toolchain.rs"]
mod toolchain;

use chunk_patch::*;
use compile::*;
use luajit_contracts::*;
use output_diff::*;
use pipeline::*;
use readability::*;
use toolchain::*;

pub fn compile_lua_case(dialect_label: &str, source_relative: &str) -> Vec<u8> {
    compile_lua_case_inner(
        dialect_label,
        source_relative,
        true,
        LuaCaseOptions::default(),
    )
}

#[allow(dead_code)]
pub fn compile_lua_case_with_debug(dialect_label: &str, source_relative: &str) -> Vec<u8> {
    compile_lua_case_inner(
        dialect_label,
        source_relative,
        false,
        LuaCaseOptions::default(),
    )
}
