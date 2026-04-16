//! 这个文件实现仓库自带的命令行入口。
//!
//! 它负责把外部命令行参数映射成核心库的 `DecompileOptions`，并明确把 CLI 侧的
//! 输入约束、编译器查找、输出路由和调试输出拼装留在二进制包里，避免这些
//! 发布形态相关的细节重新渗回核心库。

use std::env;
use std::ffi::OsStr;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use clap::{CommandFactory, Parser, builder::BoolishValueParser, error::ErrorKind};
use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugFilters, DecompileDialect, DecompileOptions, DecompileStage,
    GenerateMode, NamingMode, QuoteStyle, TableStyle, decompile, render_timing_report,
};
use unluac::parser::{ParseMode, StringDecodeMode, StringEncoding};

const CLI_VERSION_TEXT: &str = concat!(
    env!("CARGO_PKG_VERSION"),
    "\n",
    env!("CARGO_PKG_REPOSITORY")
);
const CLI_AFTER_HELP: &str = concat!("Repository: ", env!("CARGO_PKG_REPOSITORY"));
const OUTPUT_ONLY_SUPPORTS_FINAL_SOURCE: &str = "`--output` only supports pure final generated \
source output; remove `--output` or keep `--stop-after=generate` without debug or timing flags.";

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
    decompile: DecompileOptions,
}

#[derive(Parser, Debug)]
#[command(
    name = "unluac-cli",
    bin_name = "unluac-cli",
    version = CLI_VERSION_TEXT,
    long_version = CLI_VERSION_TEXT,
    after_help = CLI_AFTER_HELP,
    about = "Decompile Lua, LuaJIT, and Luau bytecode inputs, or source inputs when an external compiler is available.",
    disable_help_subcommand = true
)]
struct CliArgs {
    /// Dialect to compile or decompile against.
    #[arg(short = 'D', long, value_parser = parse_dialect_arg, help_heading = "Input")]
    dialect: Option<DecompileDialect>,
    /// Existing compiled chunk path.
    #[arg(
        short = 'i',
        long,
        conflicts_with = "source",
        required_unless_present = "source",
        help_heading = "Input"
    )]
    input: Option<PathBuf>,
    /// Lua source path to compile before decompilation. Requires an external compiler via `--luac`,
    /// a bundled compiler under `lua/build/<dialect>/`, or a compatible compiler on PATH.
    #[arg(
        short = 's',
        long,
        conflicts_with = "input",
        required_unless_present = "input",
        help_heading = "Input"
    )]
    source: Option<PathBuf>,
    /// Override the external compiler path used by `--source`.
    #[arg(short = 'l', long, help_heading = "Input")]
    luac: Option<PathBuf>,
    /// String decoding encoding.
    #[arg(
        short = 'e',
        long,
        value_parser = parse_string_encoding_arg,
        help_heading = "Input"
    )]
    encoding: Option<StringEncoding>,
    /// String decoding failure mode.
    #[arg(
        short = 'm',
        long,
        value_parser = parse_string_decode_mode_arg,
        help_heading = "Input"
    )]
    decode_mode: Option<StringDecodeMode>,
    /// Parser strictness.
    #[arg(
        short = 'p',
        long,
        value_parser = parse_parse_mode_arg,
        help_heading = "Input"
    )]
    parse_mode: Option<ParseMode>,
    /// Enable debug output using the default final-source preset.
    #[arg(short = 'd', long, help_heading = "Debug")]
    debug: bool,
    /// Dump one or more pipeline stages.
    #[arg(long, value_parser = parse_stage_arg, help_heading = "Debug")]
    dump: Vec<DecompileStage>,
    /// Debug output detail level.
    #[arg(long, value_parser = parse_debug_detail_arg, help_heading = "Debug")]
    detail: Option<DebugDetail>,
    /// Debug color mode.
    #[arg(
        short = 'c',
        long,
        value_parser = parse_debug_color_arg,
        help_heading = "Debug"
    )]
    color: Option<DebugColorMode>,
    /// Restrict debug dumps to a specific proto id.
    #[arg(long, help_heading = "Debug")]
    proto: Option<usize>,
    /// Emit timing report.
    #[arg(short = 't', long, help_heading = "Debug")]
    timing: bool,
    /// Dump before/after snapshots for specific passes (comma-separated names).
    /// Supports HIR simplify passes (e.g. `carried-locals`, `temp-inline`) and
    /// AST readability passes (e.g. `inline-exprs`, `branch-pretty`).
    #[arg(long, value_delimiter = ',', help_heading = "Debug")]
    dump_pass: Vec<String>,
    /// Max inline complexity for returned expressions.
    #[arg(long, help_heading = "Generate")]
    return_inline_max_complexity: Option<usize>,
    /// Max inline complexity for table index expressions.
    #[arg(long, help_heading = "Generate")]
    index_inline_max_complexity: Option<usize>,
    /// Max inline complexity for call arguments.
    #[arg(long, help_heading = "Generate")]
    args_inline_max_complexity: Option<usize>,
    /// Max inline complexity for table access bases.
    #[arg(long, help_heading = "Generate")]
    access_base_inline_max_complexity: Option<usize>,
    /// Naming strategy.
    #[arg(
        short = 'n',
        long,
        value_parser = parse_naming_mode_arg,
        help_heading = "Generate"
    )]
    naming_mode: Option<NamingMode>,
    /// Whether debug-like names should include function-shaped names.
    #[arg(
        long,
        value_name = "BOOL",
        value_parser = BoolishValueParser::new(),
        help_heading = "Generate"
    )]
    debug_like_include_function: Option<bool>,
    /// Generated source indentation width.
    #[arg(long, help_heading = "Generate")]
    indent_width: Option<usize>,
    /// Preferred maximum line length.
    #[arg(long, help_heading = "Generate")]
    max_line_length: Option<usize>,
    /// String quote style.
    #[arg(
        long,
        value_parser = parse_quote_style_arg,
        help_heading = "Generate"
    )]
    quote_style: Option<QuoteStyle>,
    /// Table constructor layout style.
    #[arg(
        long,
        value_parser = parse_table_style_arg,
        help_heading = "Generate"
    )]
    table_style: Option<TableStyle>,
    /// Whether to prefer conservative source generation.
    #[arg(
        long,
        value_name = "BOOL",
        value_parser = BoolishValueParser::new(),
        help_heading = "Generate"
    )]
    conservative_output: Option<bool>,
    /// Whether to emit generate-stage comments and metadata.
    #[arg(
        long,
        value_name = "BOOL",
        value_parser = BoolishValueParser::new(),
        help_heading = "Generate"
    )]
    comment: Option<bool>,
    /// How to handle syntax not supported by the requested target dialect.
    #[arg(
        short = 'g',
        long,
        value_parser = parse_generate_mode_arg,
        help_heading = "Generate"
    )]
    generate_mode: Option<GenerateMode>,
    /// Stop the pipeline after a specific stage.
    #[arg(long, value_parser = parse_stage_arg, help_heading = "Output")]
    stop_after: Option<DecompileStage>,
    /// Write the final generated source to a file instead of stdout. Only available for pure final-source runs.
    #[arg(
        short = 'o',
        long,
        conflicts_with_all = ["debug", "dump", "detail", "color", "proto", "timing", "dump_pass"],
        help_heading = "Output"
    )]
    output: Option<PathBuf>,
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
                .unwrap_or(DecompileStage::Parse)
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

fn parse_args<I>(args: I) -> Result<CliOptions, CliError>
where
    I: IntoIterator,
    I::Item: Into<std::ffi::OsString> + Clone,
{
    let args = match CliArgs::try_parse_from(args) {
        Ok(args) => args,
        Err(error) => {
            if error.use_stderr() {
                return Err(clap_usage_error(error));
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
            decompile.debug.output_stages = args.dump.clone();
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

    if !args.dump_pass.is_empty() {
        decompile.debug.dump_passes = args.dump_pass.clone();
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
    } else {
        // CLI 层默认使用 Permissive，让用户默认获得尽可能完整的输出。
        decompile.generate.mode = GenerateMode::Permissive;
    }

    validate_output_request(&args, &decompile)?;

    Ok(CliOptions {
        input: args.input,
        source: args.source,
        output: args.output,
        luac: args.luac,
        decompile,
    })
}

fn validate_output_request(args: &CliArgs, decompile: &DecompileOptions) -> Result<(), CliError> {
    if args.output.is_some()
        && (decompile.target_stage != DecompileStage::Generate
            || decompile.debug.enable
            || decompile.debug.timing
            || !decompile.debug.output_stages.is_empty())
    {
        return Err(output_argument_conflict());
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

fn output_argument_conflict() -> CliError {
    let error = CliArgs::command().error(
        ErrorKind::ArgumentConflict,
        OUTPUT_ONLY_SUPPORTS_FINAL_SOURCE,
    );
    clap_usage_error(error)
}

fn clap_usage_error(error: clap::Error) -> CliError {
    let rendered = error.to_string();
    let message = rendered
        .strip_prefix("error: ")
        .unwrap_or(rendered.as_str())
        .to_owned();
    CliError::Usage(message)
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
        .join(options.decompile.dialect.as_str());
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
        .join(options.decompile.dialect.as_str())
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
    value.parse().map_err(|_| format!("unsupported dialect: {value}"))
}

fn parse_stage_arg(value: &str) -> Result<DecompileStage, String> {
    value.parse().map_err(|_| format!("unsupported stage: {value}"))
}

fn parse_debug_detail_arg(value: &str) -> Result<DebugDetail, String> {
    value
        .parse()
        .map_err(|_| format!("unsupported debug detail: {value}"))
}

fn parse_debug_color_arg(value: &str) -> Result<DebugColorMode, String> {
    value
        .parse()
        .map_err(|_| format!("unsupported debug color mode: {value}"))
}

fn parse_string_encoding_arg(value: &str) -> Result<StringEncoding, String> {
    value.parse().map_err(|_| format!("unsupported encoding: {value}"))
}

fn parse_string_decode_mode_arg(value: &str) -> Result<StringDecodeMode, String> {
    value
        .parse()
        .map_err(|_| format!("unsupported string decode mode: {value}"))
}

fn parse_parse_mode_arg(value: &str) -> Result<ParseMode, String> {
    value.parse().map_err(|_| format!("unsupported parse mode: {value}"))
}

fn parse_naming_mode_arg(value: &str) -> Result<NamingMode, String> {
    value.parse().map_err(|_| format!("unsupported naming mode: {value}"))
}

fn parse_quote_style_arg(value: &str) -> Result<QuoteStyle, String> {
    value
        .parse()
        .map_err(|_| format!("unsupported quote style: {value}"))
}

fn parse_table_style_arg(value: &str) -> Result<TableStyle, String> {
    value
        .parse()
        .map_err(|_| format!("unsupported table style: {value}"))
}

fn parse_generate_mode_arg(value: &str) -> Result<GenerateMode, String> {
    value
        .parse()
        .map_err(|_| format!("unsupported generate mode: {value}"))
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
