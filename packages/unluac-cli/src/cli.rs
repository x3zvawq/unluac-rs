//! 这个文件实现仓库自带命令行的执行入口。
//!
//! 参数声明与归一化由 `cli/args.rs` 负责；这里保留编译器查找和调用、核心 pipeline
//! 执行、输出路由与调试结果拼装，避免这些发布形态相关的细节渗回核心库。

use std::env;
use std::ffi::OsStr;
use std::fmt;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use unluac::decompile::{
    CommentStyle, DecompileDialect, DecompileError, DecompileOptions, DecompileStage, GenerateMode,
    GeneratedChunkKind, NamingMode, TableStyle, collect_error_protos, decompile,
    generate_proto_source, render_timing_report,
};
use unluac::parser::{ParseError, ParseMode};

const OUTPUT_ONLY_SUPPORTS_FINAL_SOURCE: &str = "`--output` only supports pure final generated \
source output; remove `--output` or keep `--stop-after=generate` without debug or timing flags.";

mod args;
mod batch;
mod json;

use args::{output_argument_conflict, parse_args};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum CliExit {
    Ok,
    PartialDiagnostic,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum OutputFormat {
    Text,
    Json,
}

impl std::str::FromStr for OutputFormat {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.trim().to_ascii_lowercase().as_str() {
            "text" => Ok(Self::Text),
            "json" => Ok(Self::Json),
            _ => Err(format!("unsupported output format: {s}")),
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum CliPreset {
    Readable,
    Exact,
    Ai,
}

impl std::str::FromStr for CliPreset {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.trim().to_ascii_lowercase().as_str() {
            "readable" => Ok(Self::Readable),
            "exact" => Ok(Self::Exact),
            "ai" => Ok(Self::Ai),
            _ => Err(format!("unsupported preset: {s}")),
        }
    }
}

impl CliPreset {
    fn apply(self, options: &mut DecompileOptions) {
        match self {
            Self::Readable => {
                options.naming.mode = NamingMode::Heuristic;
                options.generate.comment = CommentStyle::Minimal;
                options.generate.table_style = TableStyle::Aligned;
                options.generate.table_drop_index_keys = true;
            }
            Self::Exact => {
                options.parse.mode = ParseMode::Strict;
                options.naming.mode = NamingMode::DebugLike;
                options.generate.comment = CommentStyle::Full;
                options.generate.mode = GenerateMode::Strict;
                options.generate.readable_strings = false;
                options.generate.table_style = TableStyle::Balanced;
                options.generate.table_drop_index_keys = false;
            }
            Self::Ai => {
                options.naming.mode = NamingMode::Heuristic;
                options.generate.comment = CommentStyle::Minimal;
                options.generate.table_style = TableStyle::Compact;
                options.generate.table_drop_index_keys = true;
            }
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum CompilerProtocol {
    LuacStyle,
    LuaJitBytecodeTool,
    LuauBinaryStdout,
}

#[derive(Debug)]
struct CliOptions {
    input: Option<PathBuf>,
    source: Option<PathBuf>,
    output: Option<PathBuf>,
    luac: Option<PathBuf>,
    strip_debug: bool,
    decompile: DecompileOptions,
    /// 请求仅打印 proto 列表后直接退出。
    list_protos: bool,
    /// 仅输出指定 proto 的最终 Lua 源码。
    proto_source: Option<usize>,
    format: OutputFormat,
    jobs: Option<usize>,
}

pub fn run<I>(args: I) -> Result<CliExit, CliError>
where
    I: IntoIterator,
    I::Item: Into<std::ffi::OsString> + Clone,
{
    let options = parse_args(args)?;

    // 目录输入触发递归并发批量模式
    if let Some(input_path) = options.input.as_ref()
        && input_path != Path::new("-")
        && input_path.is_dir()
    {
        return run_directory_batch(&options, input_path);
    }

    let (input_source, temp_compiled) = resolve_input_path(&options)?;
    if let (Some(in_path), Some(out_path)) = (options.input.as_deref(), options.output.as_deref())
        && in_path != Path::new("-")
        && paths_refer_to_same_existing_file(in_path, out_path)
    {
        return Err(CliError::Usage(format!(
            "refusing to overwrite input file `{}` in place; choose a different `--output` path",
            in_path.display()
        )));
    }
    let bytes = match input_source {
        None => read_stdin(std::io::stdin())?,
        Some(path) => {
            let read_res = fs::read(&path).map_err(|source| CliError::Io {
                action: "read input chunk",
                path: path.clone(),
                source,
            });
            if let Some(tmp) = temp_compiled {
                let _ = fs::remove_file(tmp);
            }
            read_res?
        }
    };
    let debug_detail = options.decompile.debug.detail;
    let debug_color = options.decompile.debug.color;
    let list_protos = options.list_protos;
    let proto_source = options.proto_source;
    let format = options.format;
    let generate_options = options.decompile.generate.clone();
    let encoding_label = options.decompile.parse.string_encoding.as_str().to_owned();
    let result = decompile(&bytes, options.decompile)?;
    if list_protos {
        let chunk = result.state.raw_chunk.as_ref().ok_or_else(|| {
            CliError::Usage("list-protos requires the parse stage to complete".into())
        })?;
        let listing = match format {
            OutputFormat::Text => render_proto_listing(chunk),
            OutputFormat::Json => json::render_proto_listing_json(chunk, result.state.dialect),
        };
        if let Some(text) = emit_generated_source(&listing, options.output.as_deref())? {
            print!("{text}");
        }
        return Ok(CliExit::Ok);
    }
    if result.debug_output.is_empty() && result.timing_report.is_none() {
        if let Some(generated) = result.state.generated.as_ref() {
            let (final_source, effective_kind, failed_protos) = if let Some(pid) = proto_source {
                let src = generate_proto_source(&result, pid, &generate_options, &encoding_label)
                    .map_err(|err| CliError::Process(err.to_string()))?
                    .ok_or_else(|| {
                        CliError::Usage(format!(
                            "proto#{pid} not found in module (use `--list-protos` to inspect available proto ids)"
                        ))
                    })?;
                let subtree_failed = result
                    .state
                    .ast
                    .as_ref()
                    .map(|ast| collect_proto_subtree_error_ids(ast, pid))
                    .unwrap_or_default();
                let kind = if !subtree_failed.is_empty() || src.contains("-- [unluac error]") {
                    GeneratedChunkKind::DiagnosticPseudocode
                } else {
                    GeneratedChunkKind::Source
                };
                (src, kind, subtree_failed)
            } else {
                let all_failed = result
                    .state
                    .ast
                    .as_ref()
                    .map(collect_error_protos)
                    .unwrap_or_default();
                (generated.source.clone(), generated.kind, all_failed)
            };
            let exit = if effective_kind == GeneratedChunkKind::DiagnosticPseudocode {
                CliExit::PartialDiagnostic
            } else {
                CliExit::Ok
            };
            match format {
                OutputFormat::Text => {
                    if let Some(source) =
                        emit_generated_source(&final_source, options.output.as_deref())?
                    {
                        print!("{source}");
                    }
                }
                OutputFormat::Json => {
                    let proto_count = result.state.ast.as_ref().map_or(0, |a| a.protos.len());
                    let payload = json::render_single_result_json(
                        generated.dialect,
                        effective_kind,
                        &final_source,
                        proto_source,
                        proto_count,
                        &failed_protos,
                    );
                    if let Some(source) =
                        emit_generated_source(&payload, options.output.as_deref())?
                    {
                        print!("{source}");
                    }
                }
            }
            return Ok(exit);
        }
        if options.output.is_some() {
            return Err(output_argument_conflict());
        }
        println!(
            "pipeline stopped after {}",
            result
                .state
                .completed_stage
                .unwrap_or(DecompileStage::Parser)
        );
    } else {
        if options.output.is_some() {
            return Err(output_argument_conflict());
        }
        for (index, output) in result.debug_output.iter().enumerate() {
            if index > 0 {
                println!();
            }
            print!("{}", output.content);
        }
        if let Some(report) = result.timing_report.as_ref() {
            if !result.debug_output.is_empty() {
                println!();
            }
            print!(
                "{}",
                render_timing_report(report, debug_detail, debug_color)
            );
        }
    }

    Ok(CliExit::Ok)
}

fn run_directory_batch(options: &CliOptions, input_dir: &Path) -> Result<CliExit, CliError> {
    if options.list_protos || options.proto_source.is_some() || options.decompile.debug.enable {
        return Err(CliError::Usage(
            "directory batch mode does not support `--list-protos`, `--proto`, or debug dump flags"
                .to_owned(),
        ));
    }
    let output_dir = options.output.as_deref().ok_or_else(|| {
        CliError::Usage(
            "directory input requires `--output <OUT_DIR>` for batch decompilation".to_owned(),
        )
    })?;
    let summary = batch::run_batch_directory(input_dir, output_dir, &options.decompile, options.jobs)?;
    match options.format {
        OutputFormat::Json => print!("{}", json::render_batch_summary_json(&summary)),
        OutputFormat::Text => {
            eprintln!(
                "batch complete: {} decompiled ({} diagnostic), {} skipped, {} failed (scanned {} files -> {})",
                summary.decompiled,
                summary.diagnostic,
                summary.skipped,
                summary.failed,
                summary.scanned,
                summary.output_dir
            );
            for item in summary.failures.iter().take(20) {
                eprintln!("  [fail] {}: {}", item.path, item.error);
            }
            if summary.failures.len() > 20 {
                eprintln!("  ... and {} more failure(s)", summary.failures.len() - 20);
            }
        }
    }
    if summary.failed > 0 {
        return Err(CliError::Process(format!(
            "{} file(s) failed during batch decompilation",
            summary.failed
        )));
    }
    if summary.diagnostic > 0 {
        return Ok(CliExit::PartialDiagnostic);
    }
    Ok(CliExit::Ok)
}

fn emit_generated_source<'a>(
    source: &'a str,
    output: Option<&Path>,
) -> Result<Option<&'a str>, CliError> {
    if let Some(path) = output {
        fs::write(path, source).map_err(|source_error| CliError::Io {
            action: "write output file",
            path: path.to_path_buf(),
            source: source_error,
        })?;
        return Ok(None);
    }

    Ok(Some(source))
}

fn read_stdin<R: Read>(mut reader: R) -> Result<Vec<u8>, CliError> {
    let mut buffer = Vec::new();
    reader
        .read_to_end(&mut buffer)
        .map_err(|source| CliError::Io {
            action: "read input chunk",
            path: PathBuf::from("-"),
            source,
        })?;
    Ok(buffer)
}

fn resolve_input_path(options: &CliOptions) -> Result<(Option<PathBuf>, Option<PathBuf>), CliError> {
    if let Some(input) = options.input.as_ref() {
        return Ok((
            if Path::new("-") == input {
                None
            } else {
                Some(input.clone())
            },
            None,
        ));
    }

    let source = options
        .source
        .as_ref()
        .ok_or_else(|| CliError::Usage("missing `--input` or `--source`".to_owned()))?;
    let compiled = compile_source(options, source)?;
    Ok((Some(compiled.clone()), Some(compiled)))
}

fn paths_refer_to_same_existing_file(a: &Path, b: &Path) -> bool {
    match (fs::canonicalize(a), fs::canonicalize(b)) {
        (Ok(ca), Ok(cb)) => ca == cb,
        _ => a == b,
    }
}

fn collect_proto_subtree_error_ids(module: &unluac::ast::AstModule, target: usize) -> Vec<usize> {
    let all_errors: std::collections::BTreeSet<usize> =
        collect_error_protos(module).into_iter().collect();
    if all_errors.is_empty() || target >= module.protos.len() {
        return Vec::new();
    }
    // 收集目标 proto 及其所有后代（通过 parent_captures 链路判定）
    let mut subtree = std::collections::BTreeSet::new();
    subtree.insert(target);
    let mut changed = true;
    while changed {
        changed = false;
        for proto in &module.protos {
            if let Some((parent, _)) = &proto.parent_captures
                && subtree.contains(&parent.index())
                && subtree.insert(proto.id.index())
            {
                changed = true;
            }
        }
    }
    all_errors.intersection(&subtree).copied().collect()
}

fn compile_source(options: &CliOptions, source: &Path) -> Result<PathBuf, CliError> {
    let dialect = source_compile_dialect(options.decompile.dialect)?;
    let compiler = resolve_compiler(options, dialect)?;
    let protocol = compiler_protocol(dialect);
    let output_dir = env::temp_dir().join("unluac-cli-compile");
    fs::create_dir_all(&output_dir).map_err(|source_error| CliError::Io {
        action: "create temp compile directory",
        path: output_dir.clone(),
        source: source_error,
    })?;

    let file_stem = source
        .file_stem()
        .and_then(OsStr::to_str)
        .unwrap_or("index")
        .to_owned();
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let pid = std::process::id();
    let output = output_dir.join(format!(
        "{file_stem}-{pid}-{nonce}.{}",
        compiled_chunk_extension(dialect)
    ));

    let mut command = build_compile_command(options, &compiler, protocol, source, &output);
    match protocol {
        CompilerProtocol::LuacStyle | CompilerProtocol::LuaJitBytecodeTool => {
            let status = command.status().map_err(|source_error| CliError::Io {
                action: "spawn compiler",
                path: compiler.clone(),
                source: source_error,
            })?;

            if !status.success() {
                return Err(CliError::Process(format!(
                    "compiler exited with status {status} while compiling {}",
                    source.display()
                )));
            }
        }
        CompilerProtocol::LuauBinaryStdout => {
            let command_output = command.output().map_err(|source_error| CliError::Io {
                action: "spawn compiler",
                path: compiler.clone(),
                source: source_error,
            })?;
            if !command_output.status.success() {
                return Err(CliError::Process(format!(
                    "compiler exited with status {} while compiling {}",
                    command_output.status,
                    source.display()
                )));
            }
            fs::write(&output, &command_output.stdout).map_err(|source_error| CliError::Io {
                action: "write compiled chunk",
                path: output.clone(),
                source: source_error,
            })?;
        }
    }

    Ok(output)
}

fn build_compile_command(
    options: &CliOptions,
    compiler: &Path,
    protocol: CompilerProtocol,
    source: &Path,
    output: &Path,
) -> Command {
    let mut command = Command::new(compiler);
    match protocol {
        CompilerProtocol::LuacStyle => {
            if options.strip_debug {
                command.arg("-s");
            }
            command.arg("-o").arg(output).arg(source);
        }
        CompilerProtocol::LuaJitBytecodeTool => {
            let is_direct_luajit_bin = compiler
                .file_stem()
                .and_then(OsStr::to_str)
                .is_some_and(|stem| stem.to_ascii_lowercase().starts_with("luajit"));
            if is_direct_luajit_bin {
                command.arg("-b");
                command
                    .arg(if options.strip_debug { "-s" } else { "-g" })
                    .arg(source)
                    .arg(output);
            } else {
                #[cfg(windows)]
                configure_windows_luajit_compiler(&mut command, compiler);
                command
                    .arg(if options.strip_debug { "-s" } else { "-g" })
                    .arg(source)
                    .arg(output);
            }
        }
        CompilerProtocol::LuauBinaryStdout => {
            command
                .arg("--binary")
                .arg(if options.strip_debug { "-g0" } else { "-g2" });
            if let Some(vector) = &options.decompile.generate.luau_vector_constructor {
                if let Some(library) = &vector.library {
                    command.arg(format!("--vector-lib={library}"));
                }
                command.arg(format!("--vector-ctor={}", vector.constructor));
            }
            command.arg(source);
        }
    }
    command
}

#[cfg(windows)]
fn configure_windows_luajit_compiler(command: &mut Command, compiler: &Path) {
    // Windows bootstrap 直接把 LuaJIT 可执行文件作为 `luac` 入口；它不像 Unix
    // shell wrapper 那样自动补参数，因此需要显式指定字节码子命令和模块路径。
    command.arg("-b");
    let root = compiler.parent().unwrap_or_else(|| Path::new("."));
    let lua_path = [
        root.join("?.lua"),
        root.join("?").join("init.lua"),
        root.join("jit").join("?.lua"),
        root.join("jit").join("?").join("init.lua"),
    ]
    .into_iter()
    .map(|path| path.to_string_lossy().into_owned())
    .chain(std::iter::once(String::new()))
    .collect::<Vec<_>>()
    .join(";");
    command.env("LUA_PATH", lua_path);
}

fn source_compile_dialect(dialect: DecompileDialect) -> Result<DecompileDialect, CliError> {
    if dialect == DecompileDialect::Auto {
        return Err(CliError::Usage(
            "`--source` requires an explicit `--dialect`; auto detection only applies to compiled bytecode inputs".to_owned(),
        ));
    }
    Ok(dialect)
}

fn resolve_compiler(options: &CliOptions, dialect: DecompileDialect) -> Result<PathBuf, CliError> {
    if let Some(path) = options.luac.as_ref() {
        return Ok(path.clone());
    }

    let bundled = repo_root()
        .join("lua")
        .join("build")
        .join(<&'static str>::from(dialect))
        .join(executable_name(bundled_compiler_name(dialect)));
    if bundled.exists() {
        return Ok(bundled);
    }

    let candidates: &[&str] = match dialect {
        DecompileDialect::Auto => unreachable!("source compile dialect must be explicit"),
        DecompileDialect::Lua51 => &["luac5.1", "luac51", "luac"],
        DecompileDialect::Lua52 => &["luac5.2", "luac52", "luac"],
        DecompileDialect::Lua53 => &["luac5.3", "luac53", "luac"],
        DecompileDialect::Lua54 => &["luac5.4", "luac54", "luac"],
        DecompileDialect::Lua55 => &["luac5.5", "luac55", "luac"],
        DecompileDialect::Luajit => &["luajit"],
        DecompileDialect::Luau => &["luau-compile"],
    };
    if let Some(found) = find_in_path(candidates) {
        return Ok(found);
    }
    Ok(PathBuf::from(executable_name(candidates[0])))
}

fn find_in_path(names: &[&str]) -> Option<PathBuf> {
    let path_var = env::var_os("PATH")?;
    for name in names {
        let exe = executable_name(name);
        for dir in env::split_paths(&path_var) {
            let candidate = dir.join(&exe);
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    None
}

fn compiler_protocol(dialect: DecompileDialect) -> CompilerProtocol {
    match dialect {
        DecompileDialect::Auto => unreachable!("source compile dialect must be explicit"),
        DecompileDialect::Lua51
        | DecompileDialect::Lua52
        | DecompileDialect::Lua53
        | DecompileDialect::Lua54
        | DecompileDialect::Lua55 => CompilerProtocol::LuacStyle,
        DecompileDialect::Luajit => CompilerProtocol::LuaJitBytecodeTool,
        DecompileDialect::Luau => CompilerProtocol::LuauBinaryStdout,
    }
}

fn bundled_compiler_name(dialect: DecompileDialect) -> &'static str {
    match dialect {
        DecompileDialect::Auto => unreachable!("source compile dialect must be explicit"),
        DecompileDialect::Lua51
        | DecompileDialect::Lua52
        | DecompileDialect::Lua53
        | DecompileDialect::Lua54
        | DecompileDialect::Lua55 => "luac",
        DecompileDialect::Luajit => "luac",
        DecompileDialect::Luau => "luau-compile",
    }
}

fn executable_name(name: &str) -> String {
    format!("{name}{}", std::env::consts::EXE_SUFFIX)
}

fn compiled_chunk_extension(dialect: DecompileDialect) -> &'static str {
    match dialect {
        DecompileDialect::Auto => unreachable!("source compile dialect must be explicit"),
        DecompileDialect::Lua51
        | DecompileDialect::Lua52
        | DecompileDialect::Lua53
        | DecompileDialect::Lua54
        | DecompileDialect::Lua55 => "out",
        DecompileDialect::Luajit => "luajit",
        DecompileDialect::Luau => "luau",
    }
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("cli crate should stay under <workspace>/packages/unluac-cli")
}

/// 把 RawChunk 渲染成 `--list-protos` 需要的扁平表格。
///
/// 这里故意只依赖 parser 层已经掌握的事实（行号、指令数、子 proto 数），
/// 让这个命令不触发后续任何 pass。用户拿到 id 之后可以再用 `--proto <id>`
/// 配合 `--proto-depth` 去观察具体 pass 的细节。
fn render_proto_listing(chunk: &unluac::parser::RawChunk) -> String {
    use std::fmt::Write as _;

    let mut rows: Vec<ProtoListRow> = Vec::new();
    collect_proto_rows(&chunk.main, None, 0, &mut rows);

    let mut output = String::new();
    let _ = writeln!(
        output,
        "{:<6} {:<6} {:<12} {:<8} {:<8}  name",
        "id", "parent", "lines", "instrs", "children",
    );
    for row in &rows {
        let indent = "  ".repeat(row.depth);
        let parent = row
            .parent
            .map(|p| format!("{p}"))
            .unwrap_or_else(|| "-".to_owned());
        let lines = format!("{}..{}", row.line_start, row.line_end);
        let _ = writeln!(
            output,
            "{:<6} {:<6} {:<12} {:<8} {:<8}  {indent}proto#{}",
            row.id, parent, lines, row.instrs, row.children, row.id,
        );
    }
    output
}

struct ProtoListRow {
    id: usize,
    parent: Option<usize>,
    depth: usize,
    line_start: u32,
    line_end: u32,
    instrs: usize,
    children: usize,
}

fn collect_proto_rows(
    proto: &unluac::parser::RawProto,
    parent: Option<usize>,
    depth: usize,
    rows: &mut Vec<ProtoListRow>,
) {
    let id = rows.len();
    rows.push(ProtoListRow {
        id,
        parent,
        depth,
        line_start: proto.common.line_range.defined_start,
        line_end: proto.common.line_range.defined_end,
        instrs: proto.common.instructions.len(),
        children: proto.common.children.len(),
    });
    for child in &proto.common.children {
        collect_proto_rows(child, Some(id), depth + 1, rows);
    }
}

#[derive(Debug)]
pub enum CliError {
    HelpShown,
    Usage(String),
    Io {
        action: &'static str,
        path: PathBuf,
        source: std::io::Error,
    },
    WriteCliOutput(std::io::Error),
    Process(String),
    Decompile(unluac::decompile::DecompileError),
}

impl fmt::Display for CliError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::HelpShown => Ok(()),
            Self::Usage(message) => f.write_str(message),
            Self::Io {
                action,
                path,
                source,
            } => write!(f, "{action} `{}` failed: {source}", path.display()),
            Self::WriteCliOutput(source) => write!(f, "write cli output failed: {source}"),
            Self::Process(message) => f.write_str(message),
            Self::Decompile(error) => {
                fmt::Display::fmt(error, f)?;
                match error {
                    DecompileError::Parse(ParseError::InvalidSignature { .. }) => {
                        write!(
                            f,
                            "\nhint: input does not look like compiled Lua/LuaJIT/Luau bytecode; \
                             if this is plain Lua source, compile it first or pass `-s <file.lua> -D <dialect>`"
                        )?;
                    }
                    DecompileError::Parse(ParseError::StringDecode { .. }) => {
                        write!(
                            f,
                            "\nhint: try specifying source encoding with `-e gbk` / `-e big5` / `-e shift_jis`, \
                             or pass `--decode-mode lossy`"
                        )?;
                    }
                    _ => {}
                }
                Ok(())
            }
        }
    }
}

impl From<unluac::decompile::DecompileError> for CliError {
    fn from(value: unluac::decompile::DecompileError) -> Self {
        Self::Decompile(value)
    }
}
