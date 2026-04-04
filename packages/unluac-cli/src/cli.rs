//! 这个文件实现仓库自带的命令行入口。
//!
//! 它负责把外部命令行参数映射成核心库的 `DecompileOptions`，并明确把 CLI 侧的
//! 输入约束、编译器查找和调试输出拼装留在二进制包里，避免这些发布形态相关的
//! 细节重新渗回核心库。

use std::env;
use std::ffi::OsStr;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use clap::{Parser, builder::BoolishValueParser};
use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugFilters, DecompileDialect, DecompileOptions, DecompileStage,
    GenerateMode, NamingMode, QuoteStyle, TableStyle, decompile, render_timing_report,
};
use unluac::parser::{ParseMode, StringDecodeMode, StringEncoding};

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
    luac: Option<PathBuf>,
    decompile: DecompileOptions,
}

#[derive(Parser, Debug)]
#[command(
    name = "unluac",
    version,
    about = "Decompile Lua, LuaJIT, and Luau bytecode inputs, or source inputs when an external compiler is available.",
    disable_help_subcommand = true
)]
struct CliArgs {
    /// Dialect to compile or decompile against.
    #[arg(long, value_parser = parse_dialect_arg)]
    dialect: Option<DecompileDialect>,
    /// Existing compiled chunk path.
    #[arg(long, conflicts_with = "source", required_unless_present = "source")]
    input: Option<PathBuf>,
    /// Lua source path to compile before decompilation. Requires an external compiler via `--luac`,
    /// a bundled compiler under `lua/build/<dialect>/`, or a compatible compiler on PATH.
    #[arg(long, conflicts_with = "input", required_unless_present = "input")]
    source: Option<PathBuf>,
    /// Enable debug output using the default final-source preset.
    #[arg(long)]
    debug: bool,
    /// Override the external compiler path used by `--source`.
    #[arg(long)]
    luac: Option<PathBuf>,
    /// String decoding encoding.
    #[arg(long, value_parser = parse_string_encoding_arg)]
    encoding: Option<StringEncoding>,
    /// String decoding failure mode.
    #[arg(long, value_parser = parse_string_decode_mode_arg)]
    decode_mode: Option<StringDecodeMode>,
    /// Parser strictness.
    #[arg(long, value_parser = parse_parse_mode_arg)]
    parse_mode: Option<ParseMode>,
    /// Dump one or more pipeline stages.
    #[arg(long, value_parser = parse_stage_arg)]
    dump: Vec<DecompileStage>,
    /// Stop the pipeline after a specific stage.
    #[arg(long, value_parser = parse_stage_arg)]
    stop_after: Option<DecompileStage>,
    /// Debug output detail level.
    #[arg(long, value_parser = parse_debug_detail_arg)]
    detail: Option<DebugDetail>,
    /// Debug color mode.
    #[arg(long, value_parser = parse_debug_color_arg)]
    color: Option<DebugColorMode>,
    /// Restrict debug dumps to a specific proto id.
    #[arg(long)]
    proto: Option<usize>,
    /// Emit timing report.
    #[arg(long)]
    timing: bool,
    /// Max inline complexity for returned expressions.
    #[arg(long)]
    return_inline_max_complexity: Option<usize>,
    /// Max inline complexity for table index expressions.
    #[arg(long)]
    index_inline_max_complexity: Option<usize>,
    /// Max inline complexity for call arguments.
    #[arg(long)]
    args_inline_max_complexity: Option<usize>,
    /// Max inline complexity for table access bases.
    #[arg(long)]
    access_base_inline_max_complexity: Option<usize>,
    /// Naming strategy.
    #[arg(long, value_parser = parse_naming_mode_arg)]
    naming_mode: Option<NamingMode>,
    /// Whether debug-like names should include function-shaped names.
    #[arg(long, value_name = "BOOL", value_parser = BoolishValueParser::new())]
    debug_like_include_function: Option<bool>,
    /// Generated source indentation width.
    #[arg(long)]
    indent_width: Option<usize>,
    /// Preferred maximum line length.
    #[arg(long)]
    max_line_length: Option<usize>,
    /// String quote style.
    #[arg(long, value_parser = parse_quote_style_arg)]
    quote_style: Option<QuoteStyle>,
    /// Table constructor layout style.
    #[arg(long, value_parser = parse_table_style_arg)]
    table_style: Option<TableStyle>,
    /// Whether to prefer conservative source generation.
    #[arg(long, value_name = "BOOL", value_parser = BoolishValueParser::new())]
    conservative_output: Option<bool>,
    /// Whether to emit generate-stage comments and metadata.
    #[arg(long, value_name = "BOOL", value_parser = BoolishValueParser::new())]
    comment: Option<bool>,
    /// How to handle syntax not supported by the requested target dialect.
    #[arg(long, value_parser = parse_generate_mode_arg)]
    generate_mode: Option<GenerateMode>,
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
    let result = decompile(&bytes, options.decompile)?;
    if let Some(generated) = result.state.generated.as_ref() {
        for warning in &generated.warnings {
            eprintln!("[unluac][generate-warning] {warning}");
        }
    }

    if result.debug_output.is_empty() && result.timing_report.is_none() {
        if let Some(generated) = result.state.generated.as_ref() {
            print!("{}", generated.source);
            return Ok(());
        }
        println!(
            "pipeline stopped after {}",
            result
                .state
                .completed_stage
                .unwrap_or(DecompileStage::Parse)
        );
    } else {
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

fn parse_args<I>(args: I) -> Result<CliOptions, CliError>
where
    I: IntoIterator,
    I::Item: Into<std::ffi::OsString> + Clone,
{
    let args = match CliArgs::try_parse_from(args) {
        Ok(args) => args,
        Err(error) => {
            if error.use_stderr() {
                return Err(CliError::Usage(error.to_string()));
            }
            error.print().map_err(CliError::WriteCliOutput)?;
            return Err(CliError::HelpShown);
        }
    };

    let mut decompile = DecompileOptions::default();
    let has_explicit_dump = !args.dump.is_empty();
    let has_explicit_debug_output = args.debug
        || has_explicit_dump
        || args.detail.is_some()
        || args.color.is_some()
        || args.proto.is_some();

    // CLI 默认直接输出最终源码；只有显式请求时才启用 repo debug preset 的调试行为。
    decompile.debug.enable = false;
    decompile.debug.output_stages.clear();
    decompile.debug.timing = false;

    if let Some(dialect) = args.dialect {
        decompile.dialect = dialect;
    }
    if let Some(encoding) = args.encoding {
        decompile.parse.string_encoding = encoding;
    }
    if let Some(mode) = args.decode_mode {
        decompile.parse.string_decode_mode = mode;
    }
    if let Some(mode) = args.parse_mode {
        decompile.parse.mode = mode;
    }
    if let Some(stage) = args.stop_after {
        decompile.target_stage = stage;
    }
    if let Some(detail) = args.detail {
        decompile.debug.detail = detail;
    }
    if let Some(color) = args.color {
        decompile.debug.color = color;
    }
    decompile.debug.filters = DebugFilters { proto: args.proto };

    if has_explicit_debug_output {
        decompile.debug.enable = true;
        if has_explicit_dump {
            decompile.debug.output_stages = args.dump;
        } else {
            // 只要显式请求了 debug 输出但没指定 dump，就沿用默认 preset
            // 的“当前目标阶段”约定，而不是静默什么都不打印。
            decompile.debug.output_stages = vec![decompile.target_stage];
        }
    }

    if args.timing {
        decompile.debug.enable = true;
        decompile.debug.timing = true;
        if !has_explicit_debug_output {
            decompile.debug.output_stages.clear();
        }
    }

    if let Some(value) = args.return_inline_max_complexity {
        decompile.readability.return_inline_max_complexity = value;
    }
    if let Some(value) = args.index_inline_max_complexity {
        decompile.readability.index_inline_max_complexity = value;
    }
    if let Some(value) = args.args_inline_max_complexity {
        decompile.readability.args_inline_max_complexity = value;
    }
    if let Some(value) = args.access_base_inline_max_complexity {
        decompile.readability.access_base_inline_max_complexity = value;
    }

    if let Some(mode) = args.naming_mode {
        decompile.naming.mode = mode;
    }
    if let Some(value) = args.debug_like_include_function {
        decompile.naming.debug_like_include_function = value;
    }

    if let Some(value) = args.indent_width {
        decompile.generate.indent_width = value;
    }
    if let Some(value) = args.max_line_length {
        decompile.generate.max_line_length = value;
    }
    if let Some(style) = args.quote_style {
        decompile.generate.quote_style = style;
    }
    if let Some(style) = args.table_style {
        decompile.generate.table_style = style;
    }
    if let Some(value) = args.conservative_output {
        decompile.generate.conservative_output = value;
    }
    if let Some(value) = args.comment {
        decompile.generate.comment = value;
    }
    if let Some(mode) = args.generate_mode {
        decompile.generate.mode = mode;
    }

    Ok(CliOptions {
        input: args.input,
        source: args.source,
        luac: args.luac,
        decompile,
    })
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
    let compiler = resolve_compiler(options)?;
    let protocol = compiler_protocol(options.decompile.dialect);
    let output_dir = repo_root()
        .join("target")
        .join("unluac-debug")
        .join(options.decompile.dialect.label());
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
    let output = output_dir.join(format!(
        "{file_stem}.{}",
        compiled_chunk_extension(options.decompile.dialect)
    ));

    match protocol {
        CompilerProtocol::LuacStyle => {
            let status = Command::new(&compiler)
                .arg("-s")
                .arg("-o")
                .arg(&output)
                .arg(source)
                .status()
                .map_err(|source_error| CliError::Io {
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
        CompilerProtocol::LuaJitBytecodeTool => {
            let status = Command::new(&compiler)
                .arg("-s")
                .arg(source)
                .arg(&output)
                .status()
                .map_err(|source_error| CliError::Io {
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
            let command_output = Command::new(&compiler)
                .arg("--binary")
                .arg("-g0")
                .arg(source)
                .output()
                .map_err(|source_error| CliError::Io {
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

fn resolve_compiler(options: &CliOptions) -> Result<PathBuf, CliError> {
    if let Some(path) = options.luac.as_ref() {
        return Ok(path.clone());
    }

    let bundled = repo_root()
        .join("lua")
        .join("build")
        .join(options.decompile.dialect.label())
        .join(bundled_compiler_name(options.decompile.dialect));
    if bundled.exists() {
        return Ok(bundled);
    }

    Ok(match options.decompile.dialect {
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

fn parse_dialect_arg(value: &str) -> Result<DecompileDialect, String> {
    DecompileDialect::parse(value).ok_or_else(|| format!("unsupported dialect: {value}"))
}

fn parse_stage_arg(value: &str) -> Result<DecompileStage, String> {
    DecompileStage::parse(value).ok_or_else(|| format!("unsupported stage: {value}"))
}

fn parse_debug_detail_arg(value: &str) -> Result<DebugDetail, String> {
    DebugDetail::parse(value).ok_or_else(|| format!("unsupported debug detail: {value}"))
}

fn parse_debug_color_arg(value: &str) -> Result<DebugColorMode, String> {
    DebugColorMode::parse(value).ok_or_else(|| format!("unsupported debug color mode: {value}"))
}

fn parse_string_encoding_arg(value: &str) -> Result<StringEncoding, String> {
    StringEncoding::parse(value).ok_or_else(|| format!("unsupported encoding: {value}"))
}

fn parse_string_decode_mode_arg(value: &str) -> Result<StringDecodeMode, String> {
    StringDecodeMode::parse(value).ok_or_else(|| format!("unsupported string decode mode: {value}"))
}

fn parse_parse_mode_arg(value: &str) -> Result<ParseMode, String> {
    ParseMode::parse(value).ok_or_else(|| format!("unsupported parse mode: {value}"))
}

fn parse_naming_mode_arg(value: &str) -> Result<NamingMode, String> {
    NamingMode::parse(value).ok_or_else(|| format!("unsupported naming mode: {value}"))
}

fn parse_quote_style_arg(value: &str) -> Result<QuoteStyle, String> {
    QuoteStyle::parse(value).ok_or_else(|| format!("unsupported quote style: {value}"))
}

fn parse_table_style_arg(value: &str) -> Result<TableStyle, String> {
    TableStyle::parse(value).ok_or_else(|| format!("unsupported table style: {value}"))
}

fn parse_generate_mode_arg(value: &str) -> Result<GenerateMode, String> {
    GenerateMode::parse(value).ok_or_else(|| format!("unsupported generate mode: {value}"))
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
