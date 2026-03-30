//! 这个 crate 承载仓库测试共享的轻量辅助函数。
//!
//! 这些 helper 只负责测试夹具解码这类稳定、无业务语义的重复逻辑，避免 unit
//! 和 regression 两套入口各自复制同一份样板代码。
#![allow(dead_code)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{
    OnceLock,
    atomic::{AtomicUsize, Ordering},
};

use unluac::decompile::{DecompileOptions, DecompileStage, decompile};

#[allow(dead_code)]
mod case_manifest;
pub use case_manifest::{LuaCaseDialect, LuaCaseManifestEntry};
use case_manifest::{case_health_cases, decompile_pipeline_health_cases};

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

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum FailureKind {
    RunSourceFailed,
    SourceExecutionFailed,
    CompileSourceFailed,
    SourceCompilationFailed,
    RunCompiledChunkFailed,
    CompiledChunkExecutionFailed,
    SourceChunkOutputMismatch,
    CaseHealthBaselineFailed,
    UnsupportedDecompileDialect,
    DecompileFailed,
    GenerateWithoutSource,
    WriteGeneratedSourceFailed,
    CompileGeneratedSourceFailed,
    GeneratedSourceCompilationFailed,
    RunGeneratedChunkFailed,
    GeneratedChunkExecutionFailed,
    GeneratedOutputMismatch,
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
            Self::CaseHealthBaselineFailed => "case-health-baseline-failed",
            Self::UnsupportedDecompileDialect => "unsupported-decompile-dialect",
            Self::DecompileFailed => "decompile-failed",
            Self::GenerateWithoutSource => "generate-without-source",
            Self::WriteGeneratedSourceFailed => "write-generated-source-failed",
            Self::CompileGeneratedSourceFailed => "compile-generated-source-failed",
            Self::GeneratedSourceCompilationFailed => "generated-source-compilation-failed",
            Self::RunGeneratedChunkFailed => "run-generated-chunk-failed",
            Self::GeneratedChunkExecutionFailed => "generated-chunk-execution-failed",
            Self::GeneratedOutputMismatch => "generated-output-mismatch",
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TestFailure {
    kind: FailureKind,
    summary: String,
    detail: String,
}

impl TestFailure {
    fn new(kind: FailureKind, summary: impl Into<String>, detail: impl Into<String>) -> Self {
        Self {
            kind,
            summary: summary.into(),
            detail: detail.into(),
        }
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
    CaseHealth,
    DecompilePipelineHealth,
}

impl UnitSuite {
    pub fn label(self) -> &'static str {
        match self {
            Self::CaseHealth => "case-health",
            Self::DecompilePipelineHealth => "decompile-pipeline-health",
        }
    }

    pub fn parse(value: &str) -> Result<Self, String> {
        match value {
            "case-health" => Ok(Self::CaseHealth),
            "decompile-pipeline-health" => Ok(Self::DecompilePipelineHealth),
            _ => Err(format!(
                "unknown unit suite: {value} (expected `case-health` or `decompile-pipeline-health`)"
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
    case_health_cases()
        .map(|entry| UnitCaseSpec {
            suite: UnitSuite::CaseHealth,
            entry,
        })
        .chain(decompile_pipeline_health_cases().map(|entry| UnitCaseSpec {
            suite: UnitSuite::DecompilePipelineHealth,
            entry,
        }))
        .collect()
}

pub fn find_unit_case_spec(
    suite: UnitSuite,
    dialect_label: &str,
    path: &str,
) -> Option<UnitCaseSpec> {
    unit_case_specs().into_iter().find(|spec| {
        spec.suite == suite
            && spec.entry.dialect.label() == dialect_label
            && spec.entry.path == path
    })
}

pub fn run_unit_case(spec: UnitCaseSpec) -> Result<(), TestFailure> {
    match spec.suite {
        UnitSuite::CaseHealth => run_case_health(&spec.entry),
        UnitSuite::DecompilePipelineHealth => run_decompile_pipeline_health(&spec.entry),
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct CaseHealthBaseline {
    pub(crate) source_output: LuaCommandOutput,
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
    run_command(&runtime, &[input_path.as_os_str()], toolchain.runtime_name)
}

/// 使用 vendored 的 `luac` 把一个仓库内 case 编译到 health suite 的稳定产物路径。
pub(crate) fn compile_lua_case_to_suite_artifact(
    dialect_label: &str,
    source_relative: &str,
    suite_label: &str,
    artifact_label: &str,
    strip_debug: bool,
) -> Result<(PathBuf, LuaCommandOutput), String> {
    let toolchain = lua_toolchain(dialect_label)?;
    let source = repo_root().join(source_relative);
    let output = suite_artifact_path(
        suite_label,
        dialect_label,
        artifact_label,
        source_relative,
        toolchain.chunk_extension,
    );
    let command_output = compile_lua_file_to_path(dialect_label, &source, &output, strip_debug)?;
    Ok((output, command_output))
}

/// 把反编译得到的源码落到稳定产物路径，便于后续编译、执行和排错。
pub(crate) fn write_generated_case_source(
    dialect_label: &str,
    suite_label: &str,
    source_relative: &str,
    generated_source: &str,
) -> Result<PathBuf, String> {
    let output = suite_artifact_path(
        suite_label,
        dialect_label,
        "generated-source",
        source_relative,
        "lua",
    );
    write_output_file(&output, generated_source.as_bytes())?;
    Ok(output)
}

/// 执行 case-health，并返回后续 pipeline health 可以直接复用的基线输出。
pub(crate) fn build_case_health_baseline(
    entry: &case_manifest::LuaCaseManifestEntry,
    suite_label: &str,
) -> Result<CaseHealthBaseline, TestFailure> {
    let dialect_label = entry.dialect.label();
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
        dialect_label,
        entry.path,
        suite_label,
        "compiled-source",
        true,
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
        return Ok(CaseHealthBaseline { source_output });
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

    Ok(CaseHealthBaseline { source_output })
}

pub(crate) fn run_case_health(entry: &LuaCaseManifestEntry) -> Result<(), TestFailure> {
    build_case_health_baseline(entry, UnitSuite::CaseHealth.label()).map(|_| ())
}

pub(crate) fn run_decompile_pipeline_health(
    entry: &LuaCaseManifestEntry,
) -> Result<(), TestFailure> {
    let dialect_label = entry.dialect.label();
    let toolchain = lua_toolchain(dialect_label).map_err(|error| {
        TestFailure::new(
            FailureKind::RunGeneratedChunkFailed,
            "unknown test dialect",
            format!("unknown test dialect {dialect_label}: {error}"),
        )
    })?;
    let baseline = build_case_health_baseline(entry, UnitSuite::DecompilePipelineHealth.label())
        .map_err(|failure| {
            TestFailure::new(
                FailureKind::CaseHealthBaselineFailed,
                format!("case-health baseline failed first: {}", failure.summary()),
                format!("case-health baseline failed first\n{}", failure.detail()),
            )
        })?;
    let dialect = entry.dialect.decompile_dialect().ok_or_else(|| {
        TestFailure::new(
            FailureKind::UnsupportedDecompileDialect,
            "unsupported decompile dialect",
            format!("unsupported decompile dialect for {}", entry.path),
        )
    })?;

    let chunk = compile_lua_case(dialect_label, entry.path);
    let result = decompile(
        &chunk,
        DecompileOptions {
            dialect,
            target_stage: DecompileStage::Generate,
            debug: Default::default(),
            ..DecompileOptions::default()
        },
    )
    .map_err(|error| {
        TestFailure::new(
            FailureKind::DecompileFailed,
            format!("decompile failed: {error}"),
            format!("decompile failed: {error}"),
        )
    })?;

    let generated = result.state.generated.as_ref().ok_or_else(|| {
        TestFailure::new(
            FailureKind::GenerateWithoutSource,
            "generate stage finished without source",
            format!("generate stage finished without source for {}", entry.path),
        )
    })?;
    let generated_source_path = write_generated_case_source(
        dialect_label,
        UnitSuite::DecompilePipelineHealth.label(),
        entry.path,
        &generated.source,
    )
    .map_err(|error| {
        TestFailure::new(
            FailureKind::WriteGeneratedSourceFailed,
            "write generated source failed",
            format!("write generated source failed: {error}"),
        )
    })?;

    let (generated_chunk_path, compile_output) = compile_generated_source_to_suite_artifact(
        dialect_label,
        entry.path,
        UnitSuite::DecompilePipelineHealth.label(),
        &generated_source_path,
        true,
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
        ));
    }

    Ok(())
}

/// 使用 vendored 的 `luac` 把某个仓库内 Lua case 编译成测试 chunk。
#[allow(dead_code)]
pub fn compile_lua_case(dialect_label: &str, source_relative: &str) -> Vec<u8> {
    compile_lua_case_inner(dialect_label, source_relative, true)
}

#[allow(dead_code)]
pub fn compile_lua_case_with_debug(dialect_label: &str, source_relative: &str) -> Vec<u8> {
    compile_lua_case_inner(dialect_label, source_relative, false)
}

static TEST_CHUNK_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn compile_lua_case_inner(
    dialect_label: &str,
    source_relative: &str,
    strip_debug: bool,
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
    let command_output = compile_lua_file_to_path(dialect_label, &source, &output, strip_debug)
        .unwrap_or_else(|error| panic!("should compile test chunk {}: {error}", source.display()));
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
    dialect_label: &str,
    source_relative: &str,
    suite_label: &str,
    generated_source_path: &Path,
    strip_debug: bool,
) -> Result<(PathBuf, LuaCommandOutput), String> {
    let toolchain = lua_toolchain(dialect_label)?;
    let output = suite_artifact_path(
        suite_label,
        dialect_label,
        "generated-chunk",
        source_relative,
        toolchain.chunk_extension,
    );
    let command_output =
        compile_lua_file_to_path(dialect_label, generated_source_path, &output, strip_debug)?;
    Ok((output, command_output))
}

fn compile_lua_file_to_path(
    dialect_label: &str,
    source: &Path,
    output: &Path,
    strip_debug: bool,
) -> Result<LuaCommandOutput, String> {
    let toolchain = lua_toolchain(dialect_label)?;
    let compiler = lua_tool_path(dialect_label, toolchain.compiler_name)?;
    ensure_parent_dir(output)?;
    run_compiler_to_output_path(toolchain, &compiler, source, output, strip_debug)
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
        .with_extension(format!("{chunk_extension}.{unique}"))
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
    artifact_label: &str,
    source_relative: &str,
    extension: &str,
) -> PathBuf {
    repo_root()
        .join("target")
        .join("unluac-tests")
        .join(suite_label)
        .join(dialect_label)
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
) -> Result<LuaCommandOutput, String> {
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
            let output_bytes = Command::new(compiler)
                .arg("--binary")
                .arg(debug_level)
                .arg(source)
                .output()
                .map_err(|error| {
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

fn run_command(
    command_path: &Path,
    args: &[&std::ffi::OsStr],
    tool_name: &str,
) -> Result<LuaCommandOutput, String> {
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
