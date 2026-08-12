//! 这个文件集中声明 CLI 参数模型，并把它们归一化成执行层使用的 `CliOptions`。
//!
//! 参数分组、依赖和冲突尽量交给 clap 表达；各分组只负责更新自己拥有的核心选项，
//! 避免执行入口同时维护参数语法和一条不断增长的线性赋值链。

use std::ffi::OsString;
use std::path::PathBuf;

use clap::{Args, CommandFactory, Parser, builder::BoolishValueParser, error::ErrorKind};
use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugFilters, DecompileDialect, DecompileOptions, DecompileStage,
    GenerateMode, LuauVectorConstructor, LuauVectorSize, NamingMode, NumberFormat, ProtoDepth,
    QuoteStyle, TableStyle,
};
use unluac::parser::{ParseMode, StringDecodeMode, StringEncoding};

use super::{CliError, CliOptions, OUTPUT_ONLY_SUPPORTS_FINAL_SOURCE};

const CLI_VERSION_TEXT: &str = concat!(
    env!("CARGO_PKG_VERSION"),
    "\n",
    env!("CARGO_PKG_REPOSITORY")
);
const CLI_AFTER_HELP: &str = concat!("Repository: ", env!("CARGO_PKG_REPOSITORY"));

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
pub(super) struct CliArgs {
    #[command(flatten)]
    input: InputArgs,
    #[command(flatten)]
    debug: DebugArgs,
    #[command(flatten)]
    readability: ReadabilityArgs,
    #[command(flatten)]
    generate: GenerateArgs,
    #[command(flatten)]
    output: OutputArgs,
}

#[derive(Args, Debug)]
struct InputArgs {
    /// Dialect to compile or decompile against.
    #[arg(
        short = 'D',
        long,
        value_parser = clap::value_parser!(DecompileDialect),
        help_heading = "Input"
    )]
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
    /// Whether source compilation strips debug and local-variable metadata.
    #[arg(
        long,
        value_name = "BOOL",
        value_parser = BoolishValueParser::new(),
        conflicts_with = "input",
        help_heading = "Input"
    )]
    strip: Option<bool>,
    /// String decoding encoding (`auto` or any Encoding Standard label).
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
        value_parser = clap::value_parser!(StringDecodeMode),
        help_heading = "Input"
    )]
    decode_mode: Option<StringDecodeMode>,
    /// Parser strictness.
    #[arg(
        short = 'p',
        long,
        value_parser = clap::value_parser!(ParseMode),
        help_heading = "Input"
    )]
    parse_mode: Option<ParseMode>,
    /// Ignore all source debug metadata after validating its encoded layout.
    #[arg(long, help_heading = "Input")]
    ignore_debug: bool,
}

impl InputArgs {
    fn apply(&self, options: &mut DecompileOptions) {
        set_if_some(&mut options.dialect, self.dialect);
        set_if_some(&mut options.parse.string_encoding, self.encoding);
        set_if_some(&mut options.parse.string_decode_mode, self.decode_mode);
        set_if_some(&mut options.parse.mode, self.parse_mode);
        options.parse.ignore_debug = self.ignore_debug;
    }
}

#[derive(Args, Debug)]
struct DebugArgs {
    /// Enable debug output using the default final-source preset.
    #[arg(short = 'd', long, help_heading = "Debug")]
    debug: bool,
    /// Dump one or more outer pipeline stages.
    #[arg(
        long,
        value_parser = clap::value_parser!(DecompileStage),
        help_heading = "Debug"
    )]
    dump: Vec<DecompileStage>,
    /// Debug output detail level.
    #[arg(
        long,
        value_parser = clap::value_parser!(DebugDetail),
        help_heading = "Debug"
    )]
    detail: Option<DebugDetail>,
    /// Debug color mode.
    #[arg(
        short = 'c',
        long,
        value_parser = clap::value_parser!(DebugColorMode),
        help_heading = "Debug"
    )]
    color: Option<DebugColorMode>,
    /// Restrict debug dumps to a specific proto id.
    #[arg(long, help_heading = "Debug")]
    proto: Option<usize>,
    /// Max depth of child protos to expand in debug dumps, relative to the focused proto.
    /// `0` (default) hides all child protos (replaced with single-line summaries);
    /// `1` expands direct children; `all` restores full output.
    #[arg(long, value_parser = parse_proto_depth_arg, help_heading = "Debug")]
    proto_depth: Option<ProtoDepth>,
    /// Emit timing report.
    #[arg(short = 't', long, help_heading = "Debug")]
    timing: bool,
    /// Dump before/after snapshots for specific passes (comma-separated names).
    /// Supports HIR simplify passes (e.g. `carried-locals`, `temp-inline`) and
    /// AST readability passes (e.g. `inline-exprs`, `branch-pretty`).
    #[arg(long, value_delimiter = ',', help_heading = "Debug")]
    dump_pass: Vec<String>,
    /// List all protos in the chunk (id, parent, lines, instrs, children) and exit.
    /// Runs up to the parse stage only; useful for picking a `--proto` target.
    #[arg(long, help_heading = "Debug")]
    list_protos: bool,
}

impl DebugArgs {
    fn apply(self, options: &mut DecompileOptions) -> bool {
        let has_explicit_dump = !self.dump.is_empty();
        let has_explicit_debug_output = self.debug
            || has_explicit_dump
            || self.detail.is_some()
            || self.color.is_some()
            || self.proto.is_some()
            || self.proto_depth.is_some();

        set_if_some(&mut options.debug.detail, self.detail);
        set_if_some(&mut options.debug.color, self.color);
        options.debug.filters = DebugFilters {
            proto: self.proto,
            proto_depth: self.proto_depth.unwrap_or(ProtoDepth::Fixed(0)),
        };

        if has_explicit_debug_output {
            options.debug.enable = true;
            options.debug.output_stages = if has_explicit_dump {
                self.dump
            } else {
                vec![options.target_stage]
            };
        }

        if self.timing {
            options.debug.enable = true;
            options.debug.timing = true;
            if !has_explicit_debug_output {
                options.debug.output_stages.clear();
            }
        }

        options.debug.dump_passes = self.dump_pass;

        if self.list_protos {
            options.target_stage = DecompileStage::Parser;
            options.debug.enable = false;
            options.debug.timing = false;
            options.debug.output_stages.clear();
        }

        self.list_protos
    }
}

#[derive(Args, Debug)]
struct ReadabilityArgs {
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
        value_parser = clap::value_parser!(NamingMode),
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
}

impl ReadabilityArgs {
    fn apply(&self, options: &mut DecompileOptions) {
        set_if_some(
            &mut options.readability.return_inline_max_complexity,
            self.return_inline_max_complexity,
        );
        set_if_some(
            &mut options.readability.index_inline_max_complexity,
            self.index_inline_max_complexity,
        );
        set_if_some(
            &mut options.readability.args_inline_max_complexity,
            self.args_inline_max_complexity,
        );
        set_if_some(
            &mut options.readability.access_base_inline_max_complexity,
            self.access_base_inline_max_complexity,
        );
        set_if_some(&mut options.naming.mode, self.naming_mode);
        set_if_some(
            &mut options.naming.debug_like_include_function,
            self.debug_like_include_function,
        );
    }
}

#[derive(Args, Debug)]
struct GenerateArgs {
    /// Generated source indentation width.
    #[arg(long, help_heading = "Generate")]
    indent_width: Option<usize>,
    /// Preferred maximum line length.
    #[arg(long, help_heading = "Generate")]
    max_line_length: Option<usize>,
    /// String quote style.
    #[arg(
        long,
        value_parser = clap::value_parser!(QuoteStyle),
        help_heading = "Generate"
    )]
    quote_style: Option<QuoteStyle>,
    /// Number literal style.
    #[arg(
        long,
        value_parser = clap::value_parser!(NumberFormat),
        help_heading = "Generate"
    )]
    number_format: Option<NumberFormat>,
    /// Table constructor layout style.
    #[arg(
        long,
        value_parser = clap::value_parser!(TableStyle),
        help_heading = "Generate"
    )]
    table_style: Option<TableStyle>,
    /// Optional Luau vector library name used with `--luau-vector-constructor`.
    #[arg(long, requires = "luau_vector_constructor", help_heading = "Generate")]
    luau_vector_library: Option<String>,
    /// Luau vector constructor used to render vector constants and compile `--source` inputs.
    #[arg(long, requires = "luau_vector_size", help_heading = "Generate")]
    luau_vector_constructor: Option<String>,
    /// Luau vector width (`3` or `4`); required with `--luau-vector-constructor`.
    #[arg(
        long,
        requires = "luau_vector_constructor",
        value_parser = parse_luau_vector_size_arg,
        help_heading = "Generate"
    )]
    luau_vector_size: Option<LuauVectorSize>,
    /// Whether to emit generate-stage comments and metadata.
    #[arg(
        long,
        value_name = "BOOL",
        value_parser = BoolishValueParser::new(),
        help_heading = "Generate"
    )]
    comment: Option<bool>,
    /// Whether unstructured control flow may be emitted as diagnostic pseudocode.
    #[arg(
        short = 'g',
        long,
        value_parser = clap::value_parser!(GenerateMode),
        help_heading = "Generate"
    )]
    generate_mode: Option<GenerateMode>,
}

impl GenerateArgs {
    fn apply(self, options: &mut DecompileOptions) {
        set_if_some(&mut options.generate.indent_width, self.indent_width);
        set_if_some(&mut options.generate.max_line_length, self.max_line_length);
        set_if_some(&mut options.generate.quote_style, self.quote_style);
        set_if_some(&mut options.generate.number_format, self.number_format);
        set_if_some(&mut options.generate.table_style, self.table_style);
        if let (Some(constructor), Some(size)) =
            (self.luau_vector_constructor, self.luau_vector_size)
        {
            options.generate.luau_vector_constructor = Some(LuauVectorConstructor {
                library: self.luau_vector_library,
                constructor,
                size,
            });
        }
        set_if_some(&mut options.generate.comment, self.comment);
        options.generate.mode = self.generate_mode.unwrap_or(GenerateMode::Permissive);
    }
}

#[derive(Args, Debug)]
struct OutputArgs {
    /// Stop the pipeline after a specific stage.
    #[arg(
        long,
        value_parser = clap::value_parser!(DecompileStage),
        help_heading = "Output"
    )]
    stop_after: Option<DecompileStage>,
    /// Write the final generated source to a file instead of stdout. Only available for pure final-source runs.
    #[arg(
        short = 'o',
        long,
        conflicts_with_all = ["debug", "dump", "detail", "color", "proto", "proto_depth", "timing", "dump_pass", "list_protos"],
        help_heading = "Output"
    )]
    output: Option<PathBuf>,
}

impl OutputArgs {
    fn apply(&self, options: &mut DecompileOptions) {
        set_if_some(&mut options.target_stage, self.stop_after);
    }
}

pub(super) fn parse_args<I>(args: I) -> Result<CliOptions, CliError>
where
    I: IntoIterator,
    I::Item: Into<OsString> + Clone,
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

    args.into_options()
}

impl CliArgs {
    fn into_options(self) -> Result<CliOptions, CliError> {
        let mut decompile = DecompileOptions::default();
        decompile.debug.enable = false;
        decompile.debug.output_stages.clear();
        decompile.debug.timing = false;

        self.input.apply(&mut decompile);
        self.output.apply(&mut decompile);
        let list_protos = self.debug.apply(&mut decompile);
        self.readability.apply(&mut decompile);
        self.generate.apply(&mut decompile);
        validate_output_request(self.output.output.as_ref(), &decompile)?;

        Ok(CliOptions {
            input: self.input.input,
            source: self.input.source,
            output: self.output.output,
            luac: self.input.luac,
            strip_debug: self.input.strip.unwrap_or(true),
            decompile,
            list_protos,
        })
    }
}

fn set_if_some<T>(target: &mut T, value: Option<T>) {
    if let Some(value) = value {
        *target = value;
    }
}

fn validate_output_request(
    output: Option<&PathBuf>,
    decompile: &DecompileOptions,
) -> Result<(), CliError> {
    if output.is_some()
        && (decompile.target_stage != DecompileStage::Generate
            || decompile.debug.enable
            || decompile.debug.timing
            || !decompile.debug.output_stages.is_empty())
    {
        return Err(output_argument_conflict());
    }

    Ok(())
}

pub(super) fn output_argument_conflict() -> CliError {
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

fn parse_proto_depth_arg(value: &str) -> Result<ProtoDepth, String> {
    match value {
        "all" | "max" | "*" => Ok(ProtoDepth::All),
        other => other.parse::<usize>().map(ProtoDepth::Fixed).map_err(|_| {
            format!("unsupported proto depth: {value} (expected a non-negative integer or `all`)")
        }),
    }
}

fn parse_string_encoding_arg(value: &str) -> Result<StringEncoding, String> {
    value
        .parse()
        .map_err(|_| format!("unsupported encoding: {value}"))
}

fn parse_luau_vector_size_arg(value: &str) -> Result<LuauVectorSize, String> {
    match value {
        "3" => Ok(LuauVectorSize::Three),
        "4" => Ok(LuauVectorSize::Four),
        _ => Err(format!("unsupported Luau vector size: {value}")),
    }
}
