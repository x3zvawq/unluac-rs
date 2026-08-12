//! 这个 crate 承载仓库源码 case 的统一端到端测试流水线。
//!
//! unit 与 regression 共用官方 toolchain 编译、反编译、回编译、执行和可读性/结构合同；
//! 少数源码编译器无法产出的 VM 内建协议也只能由 manifest 显式授权，再从同一源码通过
//! pinned 运行时动态导出临时 chunk。这里不提交 bytecode fixture，也不改变业务 lowering。
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
use unluac::structure::{
    ControlFlowFeature, LoopVmProtocol, RegionId, RegionPlan, StructureFacts, StructurePlan,
    UnstructuredLayoutItem,
};
use unluac::transformer::{
    AccessBase, AccessKey, GetTableKind, LowInstr, Reg, SetTableKind, TypeGuardKind, ValueOperand,
    format_low_instr,
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
}

fn read_readability_assertions(
    source_relative: &str,
) -> Result<Vec<ReadabilityAssertion>, TestFailure> {
    let source = repo_root().join(source_relative);
    let text = fs::read_to_string(&source).map_err(|error| {
        TestFailure::new(
            FailureKind::ReadabilityAssertionFailed,
            "read readability assertions failed",
            format!(
                "read readability assertions from {} failed: {error}",
                repo_relative_display(&source)
            ),
        )
    })?;

    let mut assertions = Vec::new();
    for (line_index, line) in text.lines().enumerate() {
        let line_no = line_index + 1;
        let Some(raw) = line
            .trim_start()
            .strip_prefix("--")
            .map(str::trim_start)
            .and_then(|line| line.strip_prefix("unluac:"))
            .map(str::trim)
        else {
            continue;
        };

        let (directive, args) = split_directive(raw).ok_or_else(|| {
            readability_parse_failure(source_relative, line_no, "missing readability directive")
        })?;
        let args = parse_long_bracket_args(args)
            .map_err(|error| readability_parse_failure(source_relative, line_no, error))?;

        match directive {
            "expect-contains" => {
                let [needle] = args.as_slice() else {
                    return Err(readability_parse_failure(
                        source_relative,
                        line_no,
                        "expect-contains requires exactly one [[...]] argument",
                    ));
                };
                assertions.push(ReadabilityAssertion::Contains {
                    line: line_no,
                    needle: needle.clone(),
                });
            }
            "expect-not-contains" => {
                let [needle] = args.as_slice() else {
                    return Err(readability_parse_failure(
                        source_relative,
                        line_no,
                        "expect-not-contains requires exactly one [[...]] argument",
                    ));
                };
                assertions.push(ReadabilityAssertion::NotContains {
                    line: line_no,
                    needle: needle.clone(),
                });
            }
            "expect-order" => {
                let [before, after] = args.as_slice() else {
                    return Err(readability_parse_failure(
                        source_relative,
                        line_no,
                        "expect-order requires exactly two [[...]] arguments",
                    ));
                };
                assertions.push(ReadabilityAssertion::Order {
                    line: line_no,
                    before: before.clone(),
                    after: after.clone(),
                });
            }
            other => {
                return Err(readability_parse_failure(
                    source_relative,
                    line_no,
                    format!("unknown readability directive: {other}"),
                ));
            }
        }
    }

    Ok(assertions)
}

fn split_directive(raw: &str) -> Option<(&str, &str)> {
    let raw = raw.trim();
    if raw.is_empty() {
        return None;
    }
    match raw.find(char::is_whitespace) {
        Some(index) => Some((&raw[..index], raw[index..].trim_start())),
        None => Some((raw, "")),
    }
}

fn parse_long_bracket_args(mut raw: &str) -> Result<Vec<String>, &'static str> {
    let mut args = Vec::new();
    loop {
        raw = raw.trim_start();
        if raw.is_empty() {
            return Ok(args);
        }
        let Some(rest) = raw.strip_prefix("[[") else {
            return Err("arguments must use Lua long-bracket form [[...]]");
        };
        let Some(end) = rest.find("]]") else {
            return Err("missing closing ]] in readability assertion argument");
        };
        args.push(rest[..end].to_owned());
        raw = &rest[end + 2..];
    }
}

fn readability_parse_failure(
    source_relative: &str,
    line: usize,
    reason: impl Into<String>,
) -> TestFailure {
    let reason = reason.into();
    TestFailure::new(
        FailureKind::ReadabilityAssertionFailed,
        format!("readability assertion parse failed at {source_relative}:{line}: {reason}"),
        format!("readability assertion parse failed at {source_relative}:{line}: {reason}"),
    )
}

fn assert_readability(
    stage_label: &str,
    generated_source: &str,
    assertions: &[ReadabilityAssertion],
    check_positive_shape: bool,
) -> Result<(), TestFailure> {
    for assertion in assertions {
        match assertion {
            ReadabilityAssertion::Contains { line, needle } if check_positive_shape => {
                if !generated_source.contains(needle) {
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!("expected generated source to contain {needle:?}"),
                        generated_source,
                    ));
                }
            }
            ReadabilityAssertion::NotContains { line, needle } => {
                if generated_source.contains(needle) {
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!("expected generated source not to contain {needle:?}"),
                        generated_source,
                    ));
                }
            }
            ReadabilityAssertion::Order {
                line,
                before,
                after,
            } if check_positive_shape => {
                let before_pos = generated_source.find(before);
                let after_pos = generated_source.find(after);
                if !matches!((before_pos, after_pos), (Some(left), Some(right)) if left < right) {
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!("expected generated source to contain {before:?} before {after:?}"),
                        generated_source,
                    ));
                }
            }
            ReadabilityAssertion::Contains { .. } | ReadabilityAssertion::Order { .. } => {}
        }
    }

    Ok(())
}

fn assert_source_chunk(
    stage_label: &str,
    kind: GeneratedChunkKind,
    case_path: &str,
) -> Result<(), TestFailure> {
    if kind == GeneratedChunkKind::Source {
        return Ok(());
    }
    let summary = format!("[{stage_label}] generated diagnostic pseudocode in strict source test");
    Err(TestFailure::new(
        FailureKind::GeneratedChunkKindMismatch,
        summary.clone(),
        format!("{summary}: case={case_path}, kind={kind:?}"),
    ))
}

fn assert_structure_contracts(
    entry: &LuaCaseManifestEntry,
    facts: Option<&StructureFacts>,
) -> Result<(), TestFailure> {
    for contract in entry
        .structure_contracts
        .iter()
        .copied()
        .filter(|contract| contract.dialect() == entry.dialect)
    {
        let facts = facts.ok_or_else(|| {
            source_structure_contract_failure(entry, "generate stage returned no StructureFacts")
        })?;
        if !structure_facts_match_contract(facts, contract) {
            let LuaCaseStructureContract::MixedUnstructuredChildLoop { protocol, .. } = contract;
            return Err(source_structure_contract_failure(
                entry,
                format!(
                    "no Unstructured layout contained both a direct block and a region child whose subtree owns a {} LoopVmProtocol",
                    loop_protocol_label(protocol)
                ),
            ));
        }
    }
    Ok(())
}

fn structure_facts_match_contract(
    facts: &StructureFacts,
    contract: LuaCaseStructureContract,
) -> bool {
    let LuaCaseStructureContract::MixedUnstructuredChildLoop { protocol, .. } = contract;
    plan_contains_mixed_unstructured_child_loop(facts.plan(), protocol)
        || facts
            .children
            .iter()
            .any(|child| structure_facts_match_contract(child, contract))
}

fn plan_contains_mixed_unstructured_child_loop(
    plan: &StructurePlan,
    protocol: LuaCaseLoopProtocol,
) -> bool {
    plan.regions().any(|(_, region)| {
        let RegionPlan::Unstructured { layout, .. } = region else {
            return false;
        };
        layout
            .iter()
            .any(|item| matches!(item, UnstructuredLayoutItem::Block(_)))
            && layout.iter().any(|item| match item {
                UnstructuredLayoutItem::Block(_) => false,
                UnstructuredLayoutItem::Region(child) => {
                    region_subtree_contains_loop_protocol(plan, *child, protocol)
                }
            })
    })
}

fn region_subtree_contains_loop_protocol(
    plan: &StructurePlan,
    subtree_root: RegionId,
    protocol: LuaCaseLoopProtocol,
) -> bool {
    plan.loops().any(|(loop_id, _)| {
        loop_protocol_matches(plan.loop_protocol(loop_id), protocol)
            && plan
                .loop_region(loop_id)
                .is_some_and(|region| region_is_in_subtree(plan, subtree_root, region))
    })
}

fn region_is_in_subtree(
    plan: &StructurePlan,
    subtree_root: RegionId,
    mut region: RegionId,
) -> bool {
    for _ in 0..plan.regions().len() {
        if region == subtree_root {
            return true;
        }
        let Some(parent) = plan.region(region).and_then(RegionPlan::parent) else {
            return false;
        };
        region = parent;
    }
    false
}

fn loop_protocol_matches(actual: Option<&LoopVmProtocol>, expected: LuaCaseLoopProtocol) -> bool {
    matches!(
        (actual, expected),
        (
            Some(LoopVmProtocol::NumericFor(_)),
            LuaCaseLoopProtocol::NumericFor
        ) | (
            Some(LoopVmProtocol::GenericFor(_)),
            LuaCaseLoopProtocol::GenericFor
        )
    )
}

fn loop_protocol_label(protocol: LuaCaseLoopProtocol) -> &'static str {
    match protocol {
        LuaCaseLoopProtocol::NumericFor => "NumericFor",
        LuaCaseLoopProtocol::GenericFor => "GenericFor",
    }
}

fn source_structure_contract_failure(
    entry: &LuaCaseManifestEntry,
    reason: impl Into<String>,
) -> TestFailure {
    let dialect = <&'static str>::from(entry.dialect);
    let reason = reason.into();
    TestFailure::new(
        FailureKind::StructureContractAssertionFailed,
        "StructurePlan source contract failed",
        format!(
            "StructurePlan source contract failed: case={}, dialect={dialect}: {reason}",
            entry.path
        ),
    )
}

fn readability_assertion_failure(
    stage_label: &str,
    line: usize,
    reason: String,
    generated_source: &str,
) -> TestFailure {
    let summary =
        format!("[{stage_label}] readability assertion failed at source line {line}: {reason}");
    TestFailure::new(
        FailureKind::ReadabilityAssertionFailed,
        summary.clone(),
        format!("{summary}\ngenerated source:\n{generated_source}"),
    )
}

/// 使用 vendored 的 `lua` 直接执行某个仓库内 Lua case。
pub(crate) fn run_lua_case(
    dialect_label: &str,
    source_relative: &str,
) -> Result<LuaCommandOutput, String> {
    let source = repo_root().join(source_relative);
    run_lua_file(dialect_label, &source)
}

/// 使用 vendored 的 `lua` 执行一个已经落盘的 Lua 源码或 chunk 文件。
pub(crate) fn run_lua_file(
    dialect_label: &str,
    input_path: &Path,
) -> Result<LuaCommandOutput, String> {
    let toolchain = lua_toolchain(dialect_label)?;
    let runtime = lua_tool_path(dialect_label, toolchain.runtime_name)?;
    run_command(&runtime, [input_path.as_os_str()], toolchain.runtime_name)
}

fn run_lua_file_with_args(
    dialect_label: &str,
    input_path: &Path,
    args: &[&str],
) -> Result<LuaCommandOutput, String> {
    let toolchain = lua_toolchain(dialect_label)?;
    let runtime = lua_tool_path(dialect_label, toolchain.runtime_name)?;
    run_command(
        &runtime,
        std::iter::once(input_path.as_os_str()).chain(args.iter().map(OsStr::new)),
        toolchain.runtime_name,
    )
}

/// 使用 vendored 的 `luac` 把一个仓库内 case 编译到 health suite 的稳定产物路径。
pub(crate) fn compile_lua_case_to_suite_artifact(
    entry: &LuaCaseManifestEntry,
    suite_label: &str,
    artifact_label: &str,
    strip_debug: bool,
) -> Result<(PathBuf, LuaCommandOutput), String> {
    let dialect_label = <&'static str>::from(entry.dialect);
    let toolchain = lua_toolchain(dialect_label)?;
    let source = repo_root().join(entry.path);
    let output = suite_artifact_path(
        suite_label,
        dialect_label,
        entry.variant,
        artifact_label,
        entry.path,
        toolchain.chunk_extension,
    );
    let command_output =
        compile_lua_file_to_path(dialect_label, &source, &output, strip_debug, entry.options)?;
    Ok((output, command_output))
}

/// 把反编译得到的源码落到稳定产物路径，便于后续编译、执行和排错。
pub(crate) fn write_generated_case_source(
    entry: &LuaCaseManifestEntry,
    suite_label: &str,
    generated_source: &str,
) -> Result<PathBuf, String> {
    let dialect_label = <&'static str>::from(entry.dialect);
    let output = suite_artifact_path(
        suite_label,
        dialect_label,
        entry.variant,
        "generated-source",
        entry.path,
        "lua",
    );
    write_output_file(&output, generated_source.as_bytes())?;
    Ok(output)
}

/// 执行源码与官方编译产物，得到后续反编译验证可以复用的基线输出。
pub(crate) fn build_case_baseline(
    entry: &case_manifest::LuaCaseManifestEntry,
    suite_label: &str,
) -> Result<CaseBaseline, TestFailure> {
    let dialect_label = <&'static str>::from(entry.dialect);
    let toolchain = lua_toolchain(dialect_label).map_err(|error| {
        TestFailure::new(
            FailureKind::RunSourceFailed,
            "unknown test dialect",
            format!("unknown test dialect {dialect_label}: {error}"),
        )
    })?;
    let source_output = run_lua_case(dialect_label, entry.path).map_err(|error| {
        TestFailure::new(
            FailureKind::RunSourceFailed,
            "run source failed",
            format!("run source failed: {error}"),
        )
    })?;
    if !source_output.success() {
        let reason = primary_command_reason(&source_output)
            .map(|reason| format!(": {reason}"))
            .unwrap_or_default();
        let summary = format!(
            "source execution failed{reason} (status: {})",
            render_status_code(source_output.status_code)
        );
        return Err(TestFailure::new(
            FailureKind::SourceExecutionFailed,
            summary.clone(),
            format!("{summary}\n{}", source_output.render()),
        ));
    }

    let (compiled_path, compile_output) = compile_lua_case_to_suite_artifact(
        entry,
        suite_label,
        "compiled-source",
        !entry.options.retain_debug,
    )
    .map_err(|error| {
        TestFailure::new(
            FailureKind::CompileSourceFailed,
            "compile source failed",
            format!("compile source failed: {error}"),
        )
    })?;
    if !compile_output.success() {
        let reason = primary_command_reason(&compile_output)
            .map(|reason| format!(": {reason}"))
            .unwrap_or_default();
        let summary = format!(
            "source compilation failed{reason} (artifact: {}, status: {})",
            repo_relative_display(&compiled_path),
            render_status_code(compile_output.status_code)
        );
        return Err(TestFailure::new(
            FailureKind::SourceCompilationFailed,
            summary.clone(),
            format!("{summary}\n{}", compile_output.render()),
        ));
    }

    if !toolchain.can_run_compiled_chunks {
        return Ok(CaseBaseline { source_output });
    }

    let chunk_output = run_lua_file(dialect_label, &compiled_path).map_err(|error| {
        TestFailure::new(
            FailureKind::RunCompiledChunkFailed,
            "run compiled chunk failed",
            format!("run compiled chunk failed: {error}"),
        )
    })?;
    if !chunk_output.success() {
        let reason = primary_command_reason(&chunk_output)
            .map(|reason| format!(": {reason}"))
            .unwrap_or_default();
        let summary = format!(
            "compiled chunk execution failed{reason} (artifact: {}, status: {})",
            repo_relative_display(&compiled_path),
            render_status_code(chunk_output.status_code)
        );
        return Err(TestFailure::new(
            FailureKind::CompiledChunkExecutionFailed,
            summary.clone(),
            format!("{summary}\n{}", chunk_output.render()),
        ));
    }

    if let Some(diff) =
        diff_command_outputs("source", &source_output, "compiled-chunk", &chunk_output)
    {
        let summary = format!(
            "source/chunk output mismatch (artifact: {})",
            repo_relative_display(&compiled_path),
        );
        return Err(TestFailure::new(
            FailureKind::SourceChunkOutputMismatch,
            summary.clone(),
            format!("{summary}\n{diff}"),
        ));
    }

    Ok(CaseBaseline { source_output })
}

pub(crate) fn run_pipeline_case(
    suite: UnitSuite,
    entry: &LuaCaseManifestEntry,
) -> Result<TestSuccess, TestFailure> {
    if let LuaCaseExpectation::UnsupportedIsland { jump_pc, target_pc } = entry.expectation {
        return run_unsupported_island_contract(entry, jump_pc, target_pc);
    }
    let dialect_label = <&'static str>::from(entry.dialect);
    let suite_label = suite.label();
    let toolchain = lua_toolchain(dialect_label).map_err(|error| {
        TestFailure::new(
            FailureKind::RunGeneratedChunkFailed,
            "unknown test dialect",
            format!("unknown test dialect {dialect_label}: {error}"),
        )
    })?;
    let assertions = read_readability_assertions(entry.path)?;
    let baseline = build_case_baseline(entry, suite_label).map_err(|failure| {
        TestFailure::new(
            FailureKind::BaselineFailed,
            format!("baseline failed first: {}", failure.summary()),
            format!("baseline failed first\n{}", failure.detail()),
        )
    })?;
    let expected_dialect = entry.dialect.decompile_dialect();

    let chunk = compile_manifest_case(entry);
    let result = decompile(&chunk, decompile_options(entry)).map_err(|error| {
        TestFailure::new(
            FailureKind::DecompileFailed,
            format!("decompile failed: {error}"),
            format!("decompile failed: {error}"),
        )
    })?;
    assert_auto_dialect(
        "generated",
        result.state.dialect,
        expected_dialect,
        entry.path,
    )?;
    assert_structure_contracts(entry, result.state.structure_facts.as_ref())?;

    let generated = result.state.generated.as_ref().ok_or_else(|| {
        TestFailure::new(
            FailureKind::GenerateWithoutSource,
            "generate stage finished without source",
            format!("generate stage finished without source for {}", entry.path),
        )
    })?;
    assert_source_chunk("generated", generated.kind, entry.path)?;
    assert_readability("generated", &generated.source, &assertions, true)?;
    let generated_source_path = write_generated_case_source(entry, suite_label, &generated.source)
        .map_err(|error| {
            TestFailure::new(
                FailureKind::WriteGeneratedSourceFailed,
                "write generated source failed",
                format!("write generated source failed: {error}"),
            )
        })?;

    let (generated_chunk_path, compile_output) = compile_generated_source_to_suite_artifact(
        entry,
        suite_label,
        &generated_source_path,
        !entry.options.retain_debug,
    )
    .map_err(|error| {
        TestFailure::new(
            FailureKind::CompileGeneratedSourceFailed,
            "compile generated source failed",
            format!("compile generated source failed: {error}"),
        )
    })?;
    if !compile_output.success() {
        let reason = primary_command_reason(&compile_output)
            .map(|reason| format!(": {reason}"))
            .unwrap_or_default();
        let summary = format!(
            "generated source compilation failed{reason} (status: {})",
            compile_output.status_code.unwrap_or_default(),
        );
        return Err(TestFailure::new(
            FailureKind::GeneratedSourceCompilationFailed,
            summary.clone(),
            format!(
                "{summary}\nsource artifact: {}\nchunk artifact: {}\n{}\ngenerated source:\n{}",
                repo_relative_display(&generated_source_path),
                repo_relative_display(&generated_chunk_path),
                compile_output.render(),
                generated.source
            ),
        ));
    }

    let generated_runtime_path = if toolchain.can_run_compiled_chunks {
        &generated_chunk_path
    } else {
        &generated_source_path
    };
    let generated_output =
        run_lua_file(dialect_label, generated_runtime_path).map_err(|error| {
            TestFailure::new(
                FailureKind::RunGeneratedChunkFailed,
                "run generated artifact failed",
                format!("run generated artifact failed: {error}"),
            )
        })?;
    if !generated_output.success() {
        let reason = primary_command_reason(&generated_output)
            .map(|reason| format!(": {reason}"))
            .unwrap_or_default();
        let summary = format!(
            "generated artifact execution failed{reason} (runtime artifact: {}, status: {})",
            repo_relative_display(generated_runtime_path),
            generated_output.status_code.unwrap_or_default(),
        );
        return Err(TestFailure::new(
            FailureKind::GeneratedChunkExecutionFailed,
            summary.clone(),
            format!(
                "{summary}\nsource artifact: {}\nchunk artifact: {}\nruntime artifact: {}\n{}\ngenerated source:\n{}",
                repo_relative_display(&generated_source_path),
                repo_relative_display(&generated_chunk_path),
                repo_relative_display(generated_runtime_path),
                generated_output.render(),
                generated.source
            ),
        ));
    }

    if let Some(diff) = diff_command_outputs(
        "expected-source",
        &baseline.source_output,
        "generated-artifact",
        &generated_output,
    ) {
        let proto_count = count_output_tags(&baseline.source_output.stdout);
        let failed_tags =
            diff_output_tags(&baseline.source_output.stdout, &generated_output.stdout);
        let summary = format!(
            "generated output mismatch (runtime artifact: {})",
            repo_relative_display(generated_runtime_path),
        );
        return Err(TestFailure::new(
            FailureKind::GeneratedOutputMismatch,
            summary.clone(),
            format!(
                "{summary}\nsource artifact: {}\nchunk artifact: {}\nruntime artifact: {}\n{diff}\ngenerated source:\n{}",
                repo_relative_display(&generated_source_path),
                repo_relative_display(&generated_chunk_path),
                repo_relative_display(generated_runtime_path),
                generated.source
            ),
        ).with_proto_stats(proto_count, failed_tags));
    }

    // 重编译轮次：拿上一轮生成的源码，再走一遍 compile → decompile → compile → run → 对比 baseline，
    // 同时做前后两轮生成源码的文本收敛检查。
    let rounds = entry
        .options
        .recompile_rounds
        .unwrap_or_else(recompile_rounds);
    let require_convergence = entry
        .options
        .recompile_rounds
        .is_some_and(|rounds| rounds > 0);
    let mut prev_generated_source = generated.source.clone();
    for round in 1..=rounds {
        let round_label = format!("recompile-round-{round}");

        // 把上一轮生成的源码编译成 chunk
        let prev_source_path = write_generated_case_source(
            entry,
            &format!("{suite_label}/{round_label}"),
            &prev_generated_source,
        )
        .map_err(|error| {
            TestFailure::new(
                FailureKind::WriteGeneratedSourceFailed,
                format!("[{round_label}] write generated source failed"),
                format!("[{round_label}] write generated source failed: {error}"),
            )
        })?;
        let (prev_chunk_path, prev_compile_output) = compile_generated_source_to_suite_artifact(
            entry,
            &format!("{suite_label}/{round_label}"),
            &prev_source_path,
            !entry.options.retain_debug,
        )
        .map_err(|error| {
            TestFailure::new(
                FailureKind::RecompileGeneratedSourceCompilationFailed,
                format!("[{round_label}] compile generated source failed"),
                format!("[{round_label}] compile generated source failed: {error}"),
            )
        })?;
        if !prev_compile_output.success() {
            let reason = primary_command_reason(&prev_compile_output)
                .map(|reason| format!(": {reason}"))
                .unwrap_or_default();
            let summary = format!(
                "[{round_label}] generated source compilation failed{reason} (status: {})",
                prev_compile_output.status_code.unwrap_or_default(),
            );
            return Err(TestFailure::new(
                FailureKind::RecompileGeneratedSourceCompilationFailed,
                summary.clone(),
                format!(
                    "{summary}\nsource artifact: {}\nchunk artifact: {}\n{}\ngenerated source:\n{}",
                    repo_relative_display(&prev_source_path),
                    repo_relative_display(&prev_chunk_path),
                    prev_compile_output.render(),
                    prev_generated_source,
                ),
            ));
        }

        // 反编译 chunk
        let prev_chunk_bytes = fs::read(&prev_chunk_path).map_err(|error| {
            TestFailure::new(
                FailureKind::RecompileDecompileFailed,
                format!("[{round_label}] read recompiled chunk failed"),
                format!(
                    "[{round_label}] read recompiled chunk {}: {error}",
                    repo_relative_display(&prev_chunk_path)
                ),
            )
        })?;
        let recompile_result =
            decompile(&prev_chunk_bytes, decompile_options(entry)).map_err(|error| {
                TestFailure::new(
                    FailureKind::RecompileDecompileFailed,
                    format!("[{round_label}] decompile failed: {error}"),
                    format!("[{round_label}] decompile failed: {error}"),
                )
            })?;
        assert_auto_dialect(
            &round_label,
            recompile_result.state.dialect,
            expected_dialect,
            entry.path,
        )?;
        let recompile_generated = recompile_result.state.generated.as_ref().ok_or_else(|| {
            TestFailure::new(
                FailureKind::RecompileDecompileFailed,
                format!("[{round_label}] generate stage finished without source"),
                format!(
                    "[{round_label}] generate stage finished without source for {}",
                    entry.path
                ),
            )
        })?;
        assert_source_chunk(&round_label, recompile_generated.kind, entry.path)?;
        // 正向 shape 只约束原始 bytecode 的首次恢复；目标编译器可能把合法的
        // `break`/`while true` 等价规范化成 `return`/`repeat`。安全型负向约束仍需
        // 在每个 roundtrip 重验，防止 goto、unresolved 或诊断源码回流。
        assert_readability(
            &round_label,
            &recompile_generated.source,
            &assertions,
            false,
        )?;

        // 写出、编译、执行再次生成的源码
        let regen_source_path = write_generated_case_source(
            entry,
            &format!("{suite_label}/{round_label}-regen"),
            &recompile_generated.source,
        )
        .map_err(|error| {
            TestFailure::new(
                FailureKind::WriteGeneratedSourceFailed,
                format!("[{round_label}] write regen source failed"),
                format!("[{round_label}] write regen source failed: {error}"),
            )
        })?;
        let (regen_chunk_path, regen_compile_output) = compile_generated_source_to_suite_artifact(
            entry,
            &format!("{suite_label}/{round_label}-regen"),
            &regen_source_path,
            !entry.options.retain_debug,
        )
        .map_err(|error| {
            TestFailure::new(
                FailureKind::RecompileGeneratedSourceCompilationFailed,
                format!("[{round_label}] compile regen source failed"),
                format!("[{round_label}] compile regen source failed: {error}"),
            )
        })?;
        if !regen_compile_output.success() {
            let reason = primary_command_reason(&regen_compile_output)
                .map(|reason| format!(": {reason}"))
                .unwrap_or_default();
            let summary = format!(
                "[{round_label}] regen source compilation failed{reason} (status: {})",
                regen_compile_output.status_code.unwrap_or_default(),
            );
            return Err(TestFailure::new(
                FailureKind::RecompileGeneratedSourceCompilationFailed,
                summary.clone(),
                format!(
                    "{summary}\nsource artifact: {}\nchunk artifact: {}\n{}\ngenerated source:\n{}",
                    repo_relative_display(&regen_source_path),
                    repo_relative_display(&regen_chunk_path),
                    regen_compile_output.render(),
                    recompile_generated.source,
                ),
            ));
        }

        let regen_runtime_path = if toolchain.can_run_compiled_chunks {
            &regen_chunk_path
        } else {
            &regen_source_path
        };
        let regen_output = run_lua_file(dialect_label, regen_runtime_path).map_err(|error| {
            TestFailure::new(
                FailureKind::RecompileGeneratedChunkExecutionFailed,
                format!("[{round_label}] run regen artifact failed"),
                format!("[{round_label}] run regen artifact failed: {error}"),
            )
        })?;
        if !regen_output.success() {
            let reason = primary_command_reason(&regen_output)
                .map(|reason| format!(": {reason}"))
                .unwrap_or_default();
            let summary = format!(
                "[{round_label}] regen artifact execution failed{reason} (status: {})",
                regen_output.status_code.unwrap_or_default(),
            );
            return Err(TestFailure::new(
                FailureKind::RecompileGeneratedChunkExecutionFailed,
                summary.clone(),
                format!(
                    "{summary}\nruntime artifact: {}\n{}\ngenerated source:\n{}",
                    repo_relative_display(regen_runtime_path),
                    regen_output.render(),
                    recompile_generated.source,
                ),
            ));
        }

        // 语义检查：执行输出应与 baseline 一致
        if let Some(diff) = diff_command_outputs(
            "expected-source",
            &baseline.source_output,
            &format!("{round_label}-regen"),
            &regen_output,
        ) {
            let proto_count = count_output_tags(&baseline.source_output.stdout);
            let failed_tags =
                diff_output_tags(&baseline.source_output.stdout, &regen_output.stdout);
            let summary = format!(
                "[{round_label}] regen output mismatch (runtime artifact: {})",
                repo_relative_display(regen_runtime_path),
            );
            return Err(TestFailure::new(
                FailureKind::RecompileGeneratedOutputMismatch,
                summary.clone(),
                format!(
                    "{summary}\n{diff}\ngenerated source:\n{}",
                    recompile_generated.source,
                ),
            )
            .with_proto_stats(proto_count, failed_tags));
        }

        if prev_generated_source == recompile_generated.source {
            if require_convergence {
                break;
            }
        } else if require_convergence && round == rounds {
            let summary = format!("[{round_label}] generated source did not converge");
            return Err(TestFailure::new(
                FailureKind::RecompileConvergenceMismatch,
                summary.clone(),
                format!(
                    "{summary}\nprevious source:\n{}\ncurrent source:\n{}",
                    prev_generated_source, recompile_generated.source,
                ),
            ));
        }

        prev_generated_source = recompile_generated.source.clone();
    }

    if entry.expectation == LuaCaseExpectation::LuaJitBuiltinTableRemove {
        assert_luajit_table_remove_contract(entry, suite_label)?;
    }

    let proto_count = count_output_tags(&baseline.source_output.stdout);
    Ok(TestSuccess { proto_count })
}

fn assert_luajit_table_remove_contract(
    entry: &LuaCaseManifestEntry,
    suite_label: &str,
) -> Result<(), TestFailure> {
    if entry.dialect != LuaCaseDialect::Luajit {
        return Err(luajit_builtin_contract_failure(
            entry,
            "table.remove contract requires the LuaJIT dialect",
        ));
    }

    let source = repo_root().join(entry.path);
    let dump = run_lua_file_with_args("luajit", &source, &["--dump-table-remove"])
        .map_err(|error| luajit_builtin_contract_failure(entry, error))?;
    if !dump.success() {
        return Err(luajit_builtin_contract_failure(
            entry,
            format!(
                "official runtime failed to dump table.remove\n{}",
                dump.render()
            ),
        ));
    }

    let artifact = suite_artifact_path(
        suite_label,
        "luajit",
        entry.variant,
        "toolchain-fixture",
        entry.path,
        "luajit",
    );
    write_output_file(&artifact, &dump.stdout).map_err(|error| {
        luajit_builtin_contract_failure(
            entry,
            format!("write {} failed: {error}", repo_relative_display(&artifact)),
        )
    })?;

    let mut options = decompile_options(entry);
    options.generate.mode = GenerateMode::Permissive;
    let result = decompile(&dump.stdout, options).map_err(|error| {
        luajit_builtin_contract_failure(
            entry,
            format!(
                "decompile {} failed: {error}",
                repo_relative_display(&artifact)
            ),
        )
    })?;
    assert_auto_dialect(
        "LuaJIT table.remove fixture",
        result.state.dialect,
        DecompileDialect::Luajit,
        entry.path,
    )?;

    let lowered = result.state.lowered.as_ref().ok_or_else(|| {
        luajit_builtin_contract_failure(entry, "generate stage returned no lowered chunk")
    })?;
    let generated = result.state.generated.as_ref().ok_or_else(|| {
        luajit_builtin_contract_failure(entry, "generate stage returned no generated chunk")
    })?;

    let mut guards = Vec::new();
    let mut raw_gets = Vec::new();
    let mut raw_sets = Vec::new();
    for instr in &lowered.main.instrs {
        match instr {
            LowInstr::TypeGuard(instr) => guards.push((instr.subject, instr.kind)),
            LowInstr::GetTable(instr) if instr.kind == GetTableKind::Raw => {
                raw_gets.push((instr.dst, instr.base, instr.key));
            }
            LowInstr::SetTable(instr) if instr.kind == SetTableKind::Raw => {
                raw_sets.push((instr.base, instr.key, instr.value));
            }
            _ => {}
        }
    }

    let guards_match = matches!(
        guards.as_slice(),
        [
            (Reg(0), TypeGuardKind::Table),
            (Reg(1), TypeGuardKind::Integer | TypeGuardKind::Number)
        ]
    );
    let expected_raw_gets = [
        (Reg(3), AccessBase::Reg(Reg(0)), AccessKey::Reg(Reg(2))),
        (Reg(3), AccessBase::Reg(Reg(0)), AccessKey::Reg(Reg(1))),
        (Reg(9), AccessBase::Reg(Reg(0)), AccessKey::Reg(Reg(7))),
    ];
    let expected_raw_sets = [
        (
            AccessBase::Reg(Reg(0)),
            AccessKey::Reg(Reg(2)),
            ValueOperand::Reg(Reg(4)),
        ),
        (
            AccessBase::Reg(Reg(0)),
            AccessKey::Reg(Reg(8)),
            ValueOperand::Reg(Reg(9)),
        ),
        (
            AccessBase::Reg(Reg(0)),
            AccessKey::Reg(Reg(2)),
            ValueOperand::Reg(Reg(4)),
        ),
    ];
    if !guards_match || raw_gets != expected_raw_gets || raw_sets != expected_raw_sets {
        let lir = lowered
            .main
            .instrs
            .iter()
            .map(format_low_instr)
            .collect::<Vec<_>>()
            .join("\n");
        return Err(luajit_builtin_contract_failure(
            entry,
            format!(
                "typed LIR contract mismatch in {}\nguards={guards:?}\nraw_gets={raw_gets:?}\nraw_sets={raw_sets:?}\nlow-ir:\n{lir}",
                repo_relative_display(&artifact)
            ),
        ));
    }

    const RAW_READ_DIAGNOSTIC: &str = "LuaJIT raw table read has no exact Lua source form";
    const RAW_WRITE_DIAGNOSTIC: &str = "LuaJIT raw table write has no exact Lua source form";
    let read_diagnostics = generated.source.matches(RAW_READ_DIAGNOSTIC).count();
    let write_diagnostics = generated.source.matches(RAW_WRITE_DIAGNOSTIC).count();
    if generated.kind != GeneratedChunkKind::DiagnosticPseudocode
        || read_diagnostics != 3
        || write_diagnostics != 3
    {
        return Err(luajit_builtin_contract_failure(
            entry,
            format!(
                "raw access diagnostic contract mismatch in {}: kind={:?}, reads={read_diagnostics}, writes={write_diagnostics}\n{}",
                repo_relative_display(&artifact),
                generated.kind,
                generated.source
            ),
        ));
    }

    Ok(())
}

fn luajit_builtin_contract_failure(
    entry: &LuaCaseManifestEntry,
    detail: impl Into<String>,
) -> TestFailure {
    let detail = detail.into();
    TestFailure::new(
        FailureKind::LuaJitBuiltinContractAssertionFailed,
        "LuaJIT builtin contract failed",
        format!(
            "LuaJIT builtin contract failed for {}: {detail}",
            entry.path
        ),
    )
}

fn run_unsupported_island_contract(
    entry: &LuaCaseManifestEntry,
    jump_pc: usize,
    target_pc: usize,
) -> Result<TestSuccess, TestFailure> {
    let mut chunk = compile_manifest_case(entry);
    patch_lua51_main_jump(&mut chunk, jump_pc, target_pc).map_err(|detail| {
        TestFailure::new(
            FailureKind::StructureContractAssertionFailed,
            "prepare unsupported island fixture failed",
            detail,
        )
    })?;

    let mut structure_options = decompile_options(entry);
    structure_options.target_stage = DecompileStage::Structure;
    let structure = decompile(&chunk, structure_options).map_err(|error| {
        structure_contract_failure(format!(
            "unsupported island fixture failed before the frozen StructurePlan: {error}"
        ))
    })?;
    let facts =
        structure.state.structure_facts.as_ref().ok_or_else(|| {
            structure_contract_failure("structure stage returned no StructureFacts")
        })?;
    let has_island = facts
        .plan()
        .regions()
        .any(|(_, region)| matches!(region, RegionPlan::Unstructured { .. }));
    let requires_goto = facts
        .plan()
        .requirements()
        .unavailable_features()
        .contains(&ControlFlowFeature::GotoLabel);
    if !has_island || !requires_goto {
        return Err(structure_contract_failure(format!(
            "mutated Lua 5.1 fixture did not freeze an unavailable goto island: island={has_island}, requires_goto={requires_goto}"
        )));
    }

    let mut strict_options = decompile_options(entry);
    strict_options.generate.mode = GenerateMode::Strict;
    match decompile(&chunk, strict_options) {
        Err(DecompileError::Ast(AstLowerError::UnsupportedFeature {
            dialect: DecompileDialect::Lua51,
            feature: "goto/label",
            context: "StructurePlan",
        })) => {}
        Err(error) => {
            return Err(structure_contract_failure(format!(
                "strict mode returned the wrong unsupported-island error: {error}"
            )));
        }
        Ok(_) => {
            return Err(structure_contract_failure(
                "strict mode accepted an unavailable goto island",
            ));
        }
    }

    let mut permissive_options = decompile_options(entry);
    permissive_options.generate.mode = GenerateMode::Permissive;
    let permissive = decompile(&chunk, permissive_options).map_err(|error| {
        structure_contract_failure(format!(
            "permissive mode rejected an unsupported island: {error}"
        ))
    })?;
    let generated =
        permissive.state.generated.as_ref().ok_or_else(|| {
            structure_contract_failure("permissive mode returned no generated chunk")
        })?;
    if generated.kind != GeneratedChunkKind::DiagnosticPseudocode
        || !generated
            .source
            .contains("-- [unluac error] diagnostic pseudocode:")
        || !generated.source.contains("StructurePlan requirements:")
    {
        return Err(structure_contract_failure(format!(
            "permissive mode did not preserve the plan diagnostic contract: kind={:?}\n{}",
            generated.kind, generated.source
        )));
    }

    Ok(TestSuccess { proto_count: 1 })
}

fn structure_contract_failure(detail: impl Into<String>) -> TestFailure {
    TestFailure::new(
        FailureKind::StructureContractAssertionFailed,
        "StructurePlan strict/permissive contract failed",
        detail,
    )
}

fn patch_lua51_main_jump(chunk: &mut [u8], jump_pc: usize, target_pc: usize) -> Result<(), String> {
    const LUA_SIGNATURE: &[u8; 4] = b"\x1bLua";
    const LUA51_VERSION: u8 = 0x51;
    const OP_JMP: u32 = 22;
    const MAXARG_SBX: i32 = 131_071;

    let header = chunk
        .get(..12)
        .ok_or_else(|| "Lua 5.1 fixture is shorter than its binary header".to_owned())?;
    if &header[..4] != LUA_SIGNATURE || header[4] != LUA51_VERSION || header[5] != 0 {
        return Err("unsupported-island fixture is not a standard Lua 5.1 chunk".to_owned());
    }
    let little_endian = match header[6] {
        0 => false,
        1 => true,
        value => return Err(format!("invalid Lua 5.1 endian flag {value}")),
    };
    let int_size = usize::from(header[7]);
    let size_t_size = usize::from(header[8]);
    let instruction_size = usize::from(header[9]);
    if int_size == 0 || size_t_size == 0 || instruction_size != 4 {
        return Err(format!(
            "unsupported Lua 5.1 fixture widths: int={int_size}, size_t={size_t_size}, instruction={instruction_size}"
        ));
    }

    let mut cursor = 12usize;
    let source_len = read_lua_uint(chunk, &mut cursor, size_t_size, little_endian)?;
    cursor = cursor
        .checked_add(source_len)
        .ok_or_else(|| "Lua 5.1 source name length overflow".to_owned())?;
    let proto_header_len = int_size
        .checked_mul(2)
        .and_then(|len| len.checked_add(4))
        .ok_or_else(|| "Lua 5.1 proto header width overflow".to_owned())?;
    cursor = cursor
        .checked_add(proto_header_len)
        .ok_or_else(|| "Lua 5.1 proto header offset overflow".to_owned())?;
    let code_len = read_lua_uint(chunk, &mut cursor, int_size, little_endian)?;
    if jump_pc == 0 || jump_pc > code_len || target_pc == 0 || target_pc > code_len {
        return Err(format!(
            "Lua 5.1 jump patch is outside the main code arena: pc={jump_pc}, target={target_pc}, code={code_len}"
        ));
    }
    let instruction_offset = (jump_pc - 1)
        .checked_mul(instruction_size)
        .ok_or_else(|| "Lua 5.1 instruction index overflow".to_owned())?;
    let offset = cursor
        .checked_add(instruction_offset)
        .ok_or_else(|| "Lua 5.1 instruction offset overflow".to_owned())?;
    let end = offset
        .checked_add(instruction_size)
        .ok_or_else(|| "Lua 5.1 instruction end overflow".to_owned())?;
    let bytes = chunk
        .get_mut(offset..end)
        .ok_or_else(|| "Lua 5.1 main code is truncated".to_owned())?;
    let encoded: [u8; 4] = bytes
        .as_ref()
        .try_into()
        .map_err(|_| "Lua 5.1 instruction is not four bytes".to_owned())?;
    let mut word = if little_endian {
        u32::from_le_bytes(encoded)
    } else {
        u32::from_be_bytes(encoded)
    };
    if word & 0x3f != OP_JMP {
        return Err(format!(
            "Lua 5.1 fixture pc {jump_pc} is opcode {}, expected JMP",
            word & 0x3f
        ));
    }
    let sbx = i32::try_from(target_pc)
        .and_then(|target| i32::try_from(jump_pc).map(|pc| target - pc - 1))
        .map_err(|_| "Lua 5.1 jump pc does not fit i32".to_owned())?;
    let bx = sbx + MAXARG_SBX;
    if !(0..=2 * MAXARG_SBX + 1).contains(&bx) {
        return Err(format!("Lua 5.1 jump offset {sbx} is not encodable"));
    }
    word = (word & 0x3fff) | ((bx as u32) << 14);
    let encoded = if little_endian {
        word.to_le_bytes()
    } else {
        word.to_be_bytes()
    };
    bytes.copy_from_slice(&encoded);
    Ok(())
}

fn read_lua_uint(
    bytes: &[u8],
    cursor: &mut usize,
    width: usize,
    little_endian: bool,
) -> Result<usize, String> {
    if width > 8 {
        return Err(format!("Lua integer width {width} exceeds u64"));
    }
    let end = cursor
        .checked_add(width)
        .ok_or_else(|| "Lua integer offset overflow".to_owned())?;
    let raw = bytes
        .get(*cursor..end)
        .ok_or_else(|| "Lua chunk is truncated while reading an integer".to_owned())?;
    *cursor = end;
    let mut value = 0u64;
    if little_endian {
        for (shift, byte) in raw.iter().copied().enumerate() {
            value |= u64::from(byte) << (shift * 8);
        }
    } else {
        for byte in raw {
            value = (value << 8) | u64::from(*byte);
        }
    }
    usize::try_from(value).map_err(|_| format!("Lua integer {value} does not fit usize"))
}

fn decompile_options(entry: &LuaCaseManifestEntry) -> DecompileOptions {
    let mut options = DecompileOptions {
        dialect: DecompileDialect::Auto,
        target_stage: DecompileStage::Generate,
        debug: Default::default(),
        ..DecompileOptions::default()
    };
    if let Some(mode) = entry.options.naming_mode {
        options.naming.mode = mode;
    }
    options.generate.luau_vector_constructor =
        entry
            .options
            .luau_vector
            .map(|vector| LuauVectorConstructor {
                library: vector.library.map(str::to_owned),
                constructor: vector.constructor.to_owned(),
                size: match vector.components {
                    3 => LuauVectorSize::Three,
                    4 => LuauVectorSize::Four,
                    components => panic!("unsupported Luau vector component count: {components}"),
                },
            });
    options
}

/// 使用 vendored 的 `luac` 把某个仓库内 Lua case 编译成测试 chunk。
#[allow(dead_code)]
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

fn compile_manifest_case(entry: &LuaCaseManifestEntry) -> Vec<u8> {
    compile_lua_case_inner(
        <&'static str>::from(entry.dialect),
        entry.path,
        !entry.options.retain_debug,
        entry.options,
    )
}

static TEST_CHUNK_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn compile_lua_case_inner(
    dialect_label: &str,
    source_relative: &str,
    strip_debug: bool,
    options: LuaCaseOptions,
) -> Vec<u8> {
    let repo_root = repo_root();
    let source = repo_root.join(source_relative);
    let toolchain = lua_toolchain(dialect_label)
        .unwrap_or_else(|error| panic!("invalid test dialect {dialect_label}: {error}"));
    let output = test_chunk_output_path(
        repo_root,
        dialect_label,
        &source,
        strip_debug,
        toolchain.chunk_extension,
    );
    let command_output =
        compile_lua_file_to_path(dialect_label, &source, &output, strip_debug, options)
            .unwrap_or_else(|error| {
                panic!("should compile test chunk {}: {error}", source.display())
            });
    assert!(
        command_output.success(),
        "bundled compiler failed for {}:\n{}",
        source.display(),
        command_output.render()
    );

    fs::read(&output).unwrap_or_else(|error| {
        panic!(
            "should read compiled test chunk {}: {error}",
            output.display()
        )
    })
}

/// 使用 vendored 的 `luac` 把已经生成好的源码落成稳定的 health chunk 产物。
pub(crate) fn compile_generated_source_to_suite_artifact(
    entry: &LuaCaseManifestEntry,
    suite_label: &str,
    generated_source_path: &Path,
    strip_debug: bool,
) -> Result<(PathBuf, LuaCommandOutput), String> {
    let dialect_label = <&'static str>::from(entry.dialect);
    let toolchain = lua_toolchain(dialect_label)?;
    let output = suite_artifact_path(
        suite_label,
        dialect_label,
        entry.variant,
        "generated-chunk",
        entry.path,
        toolchain.chunk_extension,
    );
    let command_output = compile_lua_file_to_path(
        dialect_label,
        generated_source_path,
        &output,
        strip_debug,
        entry.options,
    )?;
    Ok((output, command_output))
}

fn compile_lua_file_to_path(
    dialect_label: &str,
    source: &Path,
    output: &Path,
    strip_debug: bool,
    options: LuaCaseOptions,
) -> Result<LuaCommandOutput, String> {
    let toolchain = lua_toolchain(dialect_label)?;
    let compiler = lua_tool_path(dialect_label, toolchain.compiler_name)?;
    ensure_parent_dir(output)?;
    run_compiler_to_output_path(toolchain, &compiler, source, output, strip_debug, options)
}

#[allow(dead_code)]
fn test_chunk_output_path(
    repo_root: &Path,
    dialect_label: &str,
    source: &Path,
    strip_debug: bool,
    chunk_extension: &str,
) -> PathBuf {
    let unique = TEST_CHUNK_COUNTER.fetch_add(1, Ordering::Relaxed);
    let relative = source
        .strip_prefix(repo_root)
        .expect("test source should stay inside repo root");
    repo_root
        .join("target")
        .join("unluac-tests")
        .join(dialect_label)
        .join(if strip_debug { "stripped" } else { "debug" })
        .join(relative)
        .with_extension(format!("{chunk_extension}.{}.{unique}", std::process::id()))
}

pub(crate) fn diff_command_outputs(
    expected_label: &str,
    expected: &LuaCommandOutput,
    actual_label: &str,
    actual: &LuaCommandOutput,
) -> Option<String> {
    let mut diffs = Vec::new();

    if expected.status_code != actual.status_code {
        diffs.push(format!(
            "status mismatch:\n  {expected_label}: {}\n  {actual_label}: {}",
            render_status_code(expected.status_code),
            render_status_code(actual.status_code)
        ));
    }

    if expected.stdout != actual.stdout {
        diffs.push(format!(
            "stdout mismatch:\n  {expected_label}:\n{}\n  {actual_label}:\n{}",
            render_bytes(&expected.stdout),
            render_bytes(&actual.stdout)
        ));
    }

    if expected.stderr != actual.stderr {
        diffs.push(format!(
            "stderr mismatch:\n  {expected_label}:\n{}\n  {actual_label}:\n{}",
            render_bytes(&expected.stderr),
            render_bytes(&actual.stderr)
        ));
    }

    (!diffs.is_empty()).then(|| diffs.join("\n"))
}

/// 从 stdout 行中提取 `file#N` 风格标签（每行第一个 tab 之前的字段，需包含 `#`）。
fn extract_line_tag(line: &str) -> Option<&str> {
    let field = line.split('\t').next()?;
    if field.contains('#') {
        Some(field)
    } else {
        None
    }
}

/// 统计 stdout 中出现过的不重复 tag 数量，即文件内的 proto 数量。
fn count_output_tags(stdout: &[u8]) -> usize {
    let text = String::from_utf8_lossy(stdout);
    let mut seen = std::collections::BTreeSet::new();
    for line in text.lines() {
        if let Some(tag) = extract_line_tag(line) {
            seen.insert(tag.to_owned());
        }
    }
    seen.len()
}

/// 按 tag 对比两份 stdout，返回不一致的 tag 列表。
fn diff_output_tags(expected_stdout: &[u8], actual_stdout: &[u8]) -> Vec<String> {
    use std::collections::BTreeMap;

    fn group_by_tag(stdout: &[u8]) -> BTreeMap<String, Vec<String>> {
        let text = String::from_utf8_lossy(stdout);
        let mut map: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for line in text.lines() {
            if let Some(tag) = extract_line_tag(line) {
                map.entry(tag.to_owned()).or_default().push(line.to_owned());
            }
        }
        map
    }

    let expected = group_by_tag(expected_stdout);
    let actual = group_by_tag(actual_stdout);
    let mut failed = Vec::new();

    // 在 expected 中出现但 actual 不同（或缺失）的 tag
    for (tag, expected_lines) in &expected {
        match actual.get(tag) {
            Some(actual_lines) if actual_lines == expected_lines => {}
            _ => failed.push(tag.clone()),
        }
    }
    // 在 actual 中出现但 expected 没有的 tag（不应发生，但防御性记录）
    for tag in actual.keys() {
        if !expected.contains_key(tag) && !failed.contains(tag) {
            failed.push(tag.clone());
        }
    }
    failed
}

fn repo_root() -> &'static PathBuf {
    static REPO_ROOT: OnceLock<PathBuf> = OnceLock::new();

    REPO_ROOT.get_or_init(|| {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .map(Path::to_path_buf)
            .expect("test support crate should live under packages/")
    })
}

fn sanitize_repo_paths(text: &str) -> String {
    let root = repo_root();
    let root = root.to_string_lossy();
    let root_with_separator = format!("{root}/");
    text.replace(&root_with_separator, "")
}

fn primary_command_reason(output: &LuaCommandOutput) -> Option<String> {
    [&output.stderr, &output.stdout]
        .into_iter()
        .find_map(|bytes| {
            String::from_utf8_lossy(bytes)
                .lines()
                .map(str::trim)
                .find(|line| !line.is_empty())
                .map(sanitize_repo_paths)
        })
        .map(|line| {
            line.rsplit(": ")
                .next()
                .map(str::trim)
                .filter(|reason| !reason.is_empty())
                .unwrap_or(line.as_str())
                .to_owned()
        })
}

fn lua_tool_path(dialect_label: &str, tool_name: &str) -> Result<PathBuf, String> {
    let tool = repo_root()
        .join("lua")
        .join("build")
        .join(dialect_label)
        .join(tool_name);
    if !tool.exists() {
        return Err(format!(
            "missing bundled {tool_name} for {dialect_label}: {}",
            tool.display()
        ));
    }
    Ok(tool)
}

fn suite_artifact_path(
    suite_label: &str,
    dialect_label: &str,
    variant: Option<LuaCaseVariant>,
    artifact_label: &str,
    source_relative: &str,
    extension: &str,
) -> PathBuf {
    let dialect_root = repo_root()
        .join("target")
        .join("unluac-tests")
        .join(suite_label)
        .join(dialect_label);
    variant
        .map_or(dialect_root.clone(), |variant| {
            dialect_root.join(variant.label())
        })
        .join(artifact_label)
        .join(source_relative)
        .with_extension(extension)
}

fn write_output_file(path: &Path, bytes: &[u8]) -> Result<(), String> {
    ensure_parent_dir(path)?;
    fs::write(path, bytes)
        .map_err(|error| format!("should write output file {}: {error}", path.display()))
}

fn ensure_parent_dir(path: &Path) -> Result<(), String> {
    let Some(parent) = path.parent() else {
        return Err(format!(
            "path {} should always have a parent",
            path.display()
        ));
    };
    fs::create_dir_all(parent)
        .map_err(|error| format!("should create directory {}: {error}", parent.display()))
}

fn run_compiler_to_output_path(
    toolchain: LuaToolchain,
    compiler: &Path,
    source: &Path,
    output: &Path,
    strip_debug: bool,
    options: LuaCaseOptions,
) -> Result<LuaCommandOutput, String> {
    if toolchain.compiler_protocol != LuaCompilerProtocol::LuauBinaryStdout
        && (options.luau_optimization_level.is_some() || options.luau_vector.is_some())
    {
        return Err("Luau case options require the Luau compiler".to_owned());
    }

    match toolchain.compiler_protocol {
        LuaCompilerProtocol::LuacStyle => {
            let mut command = Command::new(compiler);
            if strip_debug {
                command.arg("-s");
            }
            command.arg("-o").arg(output).arg(source);
            let output = command.output().map_err(|error| {
                format!(
                    "should spawn compiler {} for {}: {error}",
                    compiler.display(),
                    source.display()
                )
            })?;
            Ok(LuaCommandOutput {
                status_code: output.status.code(),
                stdout: output.stdout,
                stderr: output.stderr,
            })
        }
        LuaCompilerProtocol::LuaJitBytecodeTool => {
            let mut command = Command::new(compiler);
            if strip_debug {
                command.arg("-s");
            }
            let output = command.arg(source).arg(output).output().map_err(|error| {
                format!(
                    "should spawn compiler {} for {}: {error}",
                    compiler.display(),
                    source.display()
                )
            })?;
            Ok(LuaCommandOutput {
                status_code: output.status.code(),
                stdout: output.stdout,
                stderr: output.stderr,
            })
        }
        LuaCompilerProtocol::LuauBinaryStdout => {
            let debug_level = if strip_debug { "-g0" } else { "-g2" };
            let mut command = Command::new(compiler);
            command.arg("--binary").arg(debug_level);
            if let Some(level) = options.luau_optimization_level {
                if level > 2 {
                    return Err(format!("invalid Luau optimization level: {level}"));
                }
                command.arg(format!("-O{level}"));
            }
            if let Some(vector) = options.luau_vector {
                if vector.constructor.is_empty() {
                    return Err("Luau vector constructor must not be empty".to_owned());
                }
                if !matches!(vector.components, 3 | 4) {
                    return Err(format!(
                        "unsupported Luau vector component count: {}",
                        vector.components
                    ));
                }
                if let Some(library) = vector.library {
                    if library.is_empty() {
                        return Err("Luau vector library must not be empty".to_owned());
                    }
                    command.arg(format!("--vector-lib={library}"));
                }
                command.arg(format!("--vector-ctor={}", vector.constructor));
            }
            let output_bytes = command.arg(source).output().map_err(|error| {
                format!(
                    "should spawn compiler {} for {}: {error}",
                    compiler.display(),
                    source.display()
                )
            })?;
            if output_bytes.status.success() {
                write_output_file(output, &output_bytes.stdout)?;
            }
            Ok(LuaCommandOutput {
                status_code: output_bytes.status.code(),
                stdout: output_bytes.stdout,
                stderr: output_bytes.stderr,
            })
        }
    }
}

fn run_command<I, S>(
    command_path: &Path,
    args: I,
    tool_name: &str,
) -> Result<LuaCommandOutput, String>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let output = Command::new(command_path)
        .args(args)
        .output()
        .map_err(|error| {
            format!(
                "should spawn {tool_name} {}: {error}",
                command_path.display()
            )
        })?;
    Ok(LuaCommandOutput {
        status_code: output.status.code(),
        stdout: output.stdout,
        stderr: output.stderr,
    })
}

fn render_status_code(status_code: Option<i32>) -> String {
    match status_code {
        Some(code) => code.to_string(),
        None => "terminated-by-signal".to_owned(),
    }
}

fn render_bytes(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        "<empty>".to_owned()
    } else {
        sanitize_repo_paths(&String::from_utf8_lossy(bytes))
    }
}
