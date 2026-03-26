//! 这个模块承载 tests 目录下共享的轻量辅助函数。
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

#[allow(dead_code)]
pub(crate) mod case_manifest;

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct LuaCommandOutput {
    pub(crate) status_code: Option<i32>,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: Vec<u8>,
}

impl LuaCommandOutput {
    pub(crate) fn success(&self) -> bool {
        self.status_code == Some(0)
    }

    pub(crate) fn render(&self) -> String {
        format!(
            "status: {}\nstdout:\n{}\nstderr:\n{}",
            render_status_code(self.status_code),
            render_bytes(&self.stdout),
            render_bytes(&self.stderr)
        )
    }
}

const TEST_OUTPUT_ENV: &str = "UNLUAC_TEST_OUTPUT";

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) enum TestOutputMode {
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

pub(crate) fn test_output_mode() -> TestOutputMode {
    *TEST_OUTPUT_MODE.get_or_init(|| match std::env::var(TEST_OUTPUT_ENV) {
        Ok(raw) => TestOutputMode::parse(raw.trim()).unwrap_or_else(|error| panic!("{error}")),
        Err(std::env::VarError::NotPresent) => TestOutputMode::Simple,
        Err(error) => panic!("failed to read {TEST_OUTPUT_ENV}: {error}"),
    })
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct TestFailure {
    summary: String,
    detail: String,
}

impl TestFailure {
    pub(crate) fn new(summary: impl Into<String>, detail: impl Into<String>) -> Self {
        Self {
            summary: summary.into(),
            detail: detail.into(),
        }
    }

    pub(crate) fn summary(&self) -> &str {
        &self.summary
    }

    pub(crate) fn detail(&self) -> &str {
        &self.detail
    }
}

pub(crate) fn format_case_failure(path: &str, failure: &TestFailure) -> String {
    match test_output_mode() {
        TestOutputMode::Simple => format!("{path} :: {}", failure.summary()),
        TestOutputMode::Verbose => format!("case: {path}\n{}", failure.detail()),
    }
}

pub(crate) fn failure_separator() -> &'static str {
    match test_output_mode() {
        TestOutputMode::Simple => "\n",
        TestOutputMode::Verbose => "\n\n",
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
    let lua = lua_tool_path(dialect_label, "lua")?;
    run_command(&lua, &[input_path.as_os_str()], "lua")
}

/// 使用 vendored 的 `luac` 把一个仓库内 case 编译到 health suite 的稳定产物路径。
pub(crate) fn compile_lua_case_to_suite_artifact(
    dialect_label: &str,
    source_relative: &str,
    suite_label: &str,
    artifact_label: &str,
    strip_debug: bool,
) -> Result<(PathBuf, LuaCommandOutput), String> {
    let source = repo_root().join(source_relative);
    let output = suite_artifact_path(
        suite_label,
        dialect_label,
        artifact_label,
        source_relative,
        "luac",
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
    let dialect_label = entry.dialect.luac_label();
    let source_output = run_lua_case(dialect_label, entry.path).map_err(|error| {
        TestFailure::new("run source failed", format!("run source failed: {error}"))
    })?;
    if !source_output.success() {
        let summary = format!(
            "source execution failed (status: {})",
            render_status_code(source_output.status_code)
        );
        return Err(TestFailure::new(
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
            "compile source failed",
            format!("compile source failed: {error}"),
        )
    })?;
    if !compile_output.success() {
        let summary = format!(
            "source compilation failed (artifact: {}, status: {})",
            compiled_path.display(),
            render_status_code(compile_output.status_code)
        );
        return Err(TestFailure::new(
            summary.clone(),
            format!("{summary}\n{}", compile_output.render()),
        ));
    }

    let chunk_output = run_lua_file(dialect_label, &compiled_path).map_err(|error| {
        TestFailure::new(
            "run compiled chunk failed",
            format!("run compiled chunk failed: {error}"),
        )
    })?;
    if !chunk_output.success() {
        let summary = format!(
            "compiled chunk execution failed (artifact: {}, status: {})",
            compiled_path.display(),
            render_status_code(chunk_output.status_code)
        );
        return Err(TestFailure::new(
            summary.clone(),
            format!("{summary}\n{}", chunk_output.render()),
        ));
    }

    if let Some(diff) =
        diff_command_outputs("source", &source_output, "compiled-chunk", &chunk_output)
    {
        let summary = format!(
            "source/chunk output mismatch (artifact: {})",
            compiled_path.display(),
        );
        return Err(TestFailure::new(
            summary.clone(),
            format!("{summary}\n{diff}"),
        ));
    }

    Ok(CaseHealthBaseline { source_output })
}

/// 使用 vendored 的 `luac` 把某个仓库内 Lua case 编译成测试 chunk。
#[allow(dead_code)]
pub(crate) fn compile_lua_case(dialect_label: &str, source_relative: &str) -> Vec<u8> {
    compile_lua_case_inner(dialect_label, source_relative, true)
}

#[allow(dead_code)]
pub(crate) fn compile_lua_case_with_debug(dialect_label: &str, source_relative: &str) -> Vec<u8> {
    compile_lua_case_inner(dialect_label, source_relative, false)
}

static TEST_CHUNK_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn compile_lua_case_inner(
    dialect_label: &str,
    source_relative: &str,
    strip_debug: bool,
) -> Vec<u8> {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let source = repo_root.join(source_relative);
    let luac = repo_root
        .join("lua")
        .join("build")
        .join(dialect_label)
        .join("luac");
    assert!(
        luac.exists(),
        "missing bundled luac for {dialect_label}: {}",
        luac.display()
    );

    let output = test_chunk_output_path(&repo_root, dialect_label, &source, strip_debug);
    fs::create_dir_all(
        output
            .parent()
            .expect("test chunk output path should always have a parent"),
    )
    .expect("should create test chunk output directory");

    let status = Command::new(&luac)
        .args(strip_debug.then_some("-s"))
        .arg("-o")
        .arg(&output)
        .arg(&source)
        .status()
        .expect("should spawn bundled luac for test case");
    assert!(
        status.success(),
        "bundled luac failed for {} with status {status}",
        source.display()
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
    let output = suite_artifact_path(
        suite_label,
        dialect_label,
        "generated-chunk",
        source_relative,
        "luac",
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
    let luac = lua_tool_path(dialect_label, "luac")?;
    ensure_parent_dir(output)?;
    run_command_with_optional_strip(&luac, source, output, strip_debug)
}

#[allow(dead_code)]
fn test_chunk_output_path(
    repo_root: &Path,
    dialect_label: &str,
    source: &Path,
    strip_debug: bool,
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
        .with_extension(format!("{}.out", unique))
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

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
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

fn run_command_with_optional_strip(
    luac: &Path,
    source: &Path,
    output: &Path,
    strip_debug: bool,
) -> Result<LuaCommandOutput, String> {
    let mut command = Command::new(luac);
    if strip_debug {
        command.arg("-s");
    }
    command.arg("-o").arg(output).arg(source);
    let output = command.output().map_err(|error| {
        format!(
            "should spawn luac {} for {}: {error}",
            luac.display(),
            source.display()
        )
    })?;
    Ok(LuaCommandOutput {
        status_code: output.status.code(),
        stdout: output.stdout,
        stderr: output.stderr,
    })
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
        String::from_utf8_lossy(bytes).into_owned()
    }
}
