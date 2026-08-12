//! 这个文件实现仓库自带命令行的执行入口。
//!
//! 参数声明与归一化由 `cli/args.rs` 负责；这里保留编译器查找和调用、核心 pipeline
//! 执行、输出路由与调试结果拼装，避免这些发布形态相关的细节渗回核心库。

use std::env;
use std::ffi::OsStr;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use unluac::decompile::{
    DecompileDialect, DecompileOptions, DecompileStage, decompile, render_timing_report,
};

const OUTPUT_ONLY_SUPPORTS_FINAL_SOURCE: &str = "`--output` only supports pure final generated \
source output; remove `--output` or keep `--stop-after=generate` without debug or timing flags.";

mod args;

#[cfg(test)]
use args::CliArgs;
use args::{output_argument_conflict, parse_args};

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
}

pub fn run<I>(args: I) -> Result<(), CliError>
where
    I: IntoIterator,
    I::Item: Into<std::ffi::OsString> + Clone,
{
    let options = parse_args(args)?;
    let input_path = resolve_input_path(&options)?;
    let bytes = fs::read(&input_path).map_err(|source| CliError::Io {
        action: "read input chunk",
        path: input_path.clone(),
        source,
    })?;
    let debug_detail = options.decompile.debug.detail;
    let debug_color = options.decompile.debug.color;
    let list_protos = options.list_protos;
    let result = decompile(&bytes, options.decompile)?;
    if list_protos {
        let chunk = result.state.raw_chunk.as_ref().ok_or_else(|| {
            CliError::Usage("list-protos requires the parse stage to complete".into())
        })?;
        print!("{}", render_proto_listing(chunk));
        return Ok(());
    }
    if result.debug_output.is_empty() && result.timing_report.is_none() {
        if let Some(generated) = result.state.generated.as_ref() {
            if let Some(source) =
                emit_generated_source(&generated.source, options.output.as_deref())?
            {
                print!("{source}");
            }
            return Ok(());
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

    Ok(())
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

fn resolve_input_path(options: &CliOptions) -> Result<PathBuf, CliError> {
    if let Some(input) = options.input.as_ref() {
        return Ok(input.clone());
    }

    let source = options
        .source
        .as_ref()
        .ok_or_else(|| CliError::Usage("missing `--input` or `--source`".to_owned()))?;
    compile_source(options, source)
}

fn compile_source(options: &CliOptions, source: &Path) -> Result<PathBuf, CliError> {
    let dialect = source_compile_dialect(options.decompile.dialect)?;
    let compiler = resolve_compiler(options, dialect)?;
    let protocol = compiler_protocol(dialect);
    let output_dir = repo_root()
        .join("target")
        .join("unluac-debug")
        .join(<&'static str>::from(dialect));
    fs::create_dir_all(&output_dir).map_err(|source_error| CliError::Io {
        action: "create debug build directory",
        path: output_dir.clone(),
        source: source_error,
    })?;

    let file_stem = source
        .file_stem()
        .and_then(OsStr::to_str)
        .unwrap_or("index")
        .to_owned();
    let output = output_dir.join(format!("{file_stem}.{}", compiled_chunk_extension(dialect)));

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
            command
                .arg(if options.strip_debug { "-s" } else { "-g" })
                .arg(source)
                .arg(output);
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
        .join(bundled_compiler_name(dialect));
    if bundled.exists() {
        return Ok(bundled);
    }

    Ok(match dialect {
        DecompileDialect::Auto => unreachable!("source compile dialect must be explicit"),
        DecompileDialect::Lua51 => PathBuf::from("lua5.1"),
        DecompileDialect::Lua52 => PathBuf::from("lua5.2"),
        DecompileDialect::Lua53 => PathBuf::from("lua5.3"),
        DecompileDialect::Lua54 => PathBuf::from("lua5.4"),
        DecompileDialect::Lua55 => PathBuf::from("lua5.5"),
        DecompileDialect::Luajit => PathBuf::from("luajit"),
        DecompileDialect::Luau => PathBuf::from("luau-compile"),
    })
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
            Self::Decompile(error) => fmt::Display::fmt(error, f),
        }
    }
}

impl From<unluac::decompile::DecompileError> for CliError {
    fn from(value: unluac::decompile::DecompileError) -> Self {
        Self::Decompile(value)
    }
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
