//! 这个文件集中声明 CLI 参数模型，并把它们归一化成执行层使用的 `CliOptions`。
//!
//! 参数分组、依赖和冲突尽量交给 clap 表达；各分组只负责更新自己拥有的核心选项，
//! 避免执行入口同时维护参数语法和一条不断增长的线性赋值链。

use std::ffi::OsString;
use std::path::PathBuf;
use std::str::FromStr;

use clap::{
    Args, CommandFactory, Parser,
    builder::{BoolishValueParser, PossibleValuesParser, TypedValueParser},
    error::ErrorKind,
};
use unluac::decompile::{
    CommentStyle, DebugColorMode, DebugDetail, DebugFilters, DecompileDialect, DecompileOptions,
    DecompileStage, GenerateMode, LuauVectorConstructor, LuauVectorSize, NamingMode, NumberFormat,
    ProtoDepth, QuoteStyle, TableStyle,
};
use unluac::generate::TableCellAlign;
use unluac::parser::{ParseMode, StringDecodeMode, StringEncoding};

use super::{
    CliError, CliOptions, CliPreset, OUTPUT_ONLY_SUPPORTS_FINAL_SOURCE, OutputFormat,
};

const CLI_VERSION_TEXT: &str = concat!(
    env!("CARGO_PKG_VERSION"),
    "\n",
    env!("CARGO_PKG_REPOSITORY")
);
const CLI_AFTER_HELP: &str = concat!("Repository: ", env!("CARGO_PKG_REPOSITORY"));
const DIALECT_VALUES: &[&str] = &[
    "auto", "lua5.1", "lua51", "lua5.2", "lua52", "lua5.3", "lua53", "lua5.4", "lua54", "lua5.5",
    "lua55", "luajit", "luau",
];
const DECODE_MODE_VALUES: &[&str] = &["strict", "lossy"];
const PARSE_MODE_VALUES: &[&str] = &["strict", "permissive"];
const STAGE_VALUES: &[&str] = &[
    "parser",
    "parse",
    "transformer",
    "transform",
    "analysis",
    "ast",
    "generate",
];
const DETAIL_VALUES: &[&str] = &["summary", "normal", "verbose"];
const COLOR_VALUES: &[&str] = &["auto", "always", "never"];
const NAMING_MODE_VALUES: &[&str] = &["debug-like", "simple", "heuristic"];
const QUOTE_STYLE_VALUES: &[&str] = &["prefer-double", "prefer-single", "min-escape"];
const NUMBER_FORMAT_VALUES: &[&str] = &["decimal", "hex"];
const TABLE_STYLE_VALUES: &[&str] = &["compact", "balanced", "aligned", "expanded"];
const TABLE_ALIGN_CELLS_VALUES: &[&str] = &["auto", "left", "right"];
const COMMENT_STYLE_VALUES: &[&str] = &["none", "minimal", "full", "true", "false"];
const GENERATE_MODE_VALUES: &[&str] = &["strict", "permissive"];
const PRESET_VALUES: &[&str] = &["readable", "exact", "ai"];
const OUTPUT_FORMAT_VALUES: &[&str] = &["text", "json"];

fn known_value_parser<T>(values: &'static [&'static str]) -> impl TypedValueParser<Value = T>
where
    T: FromStr + Clone + Send + Sync + 'static,
    T::Err: Into<Box<dyn std::error::Error + Send + Sync + 'static>>,
{
    PossibleValuesParser::new(values.iter().copied()).try_map(|value| value.parse::<T>())
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
    /// Compiled chunk file, directory (for recursive batch mode), or `-` for stdin.
    #[arg(
        value_name = "INPUT",
        conflicts_with_all = ["input", "source"],
        help_heading = "Input"
    )]
    input_pos: Option<PathBuf>,
    /// Dialect to compile or decompile against.
    #[arg(
        short = 'D',
        long,
        value_parser = known_value_parser::<DecompileDialect>(DIALECT_VALUES),
        help_heading = "Input"
    )]
    dialect: Option<DecompileDialect>,
    /// Existing compiled chunk path, directory (with `-o`), or `-` to read from stdin.
    #[arg(
        short = 'i',
        long,
        conflicts_with = "source",
        help_heading = "Input"
    )]
    input: Option<PathBuf>,
    /// Lua source path to compile before decompilation. Requires an external compiler via `--luac`,
    /// a bundled compiler under `lua/build/<dialect>/`, or a compatible compiler on PATH.
    #[arg(
        short = 's',
        long,
        conflicts_with = "input",
        help_heading = "Input"
    )]
    source: Option<PathBuf>,
    /// Override the external compiler path used by `--source`.
    #[arg(
        short = 'l',
        long,
        conflicts_with_all = ["input", "input_pos"],
        help_heading = "Input"
    )]
    luac: Option<PathBuf>,
    /// Whether source compilation strips debug and local-variable metadata.
    #[arg(
        long,
        value_name = "BOOL",
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = BoolishValueParser::new(),
        conflicts_with_all = ["input", "input_pos"],
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
        value_parser = known_value_parser::<StringDecodeMode>(DECODE_MODE_VALUES),
        help_heading = "Input"
    )]
    decode_mode: Option<StringDecodeMode>,
    /// Parser strictness.
    #[arg(
        short = 'p',
        long,
        value_parser = known_value_parser::<ParseMode>(PARSE_MODE_VALUES),
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
        value_parser = known_value_parser::<DecompileStage>(STAGE_VALUES),
        help_heading = "Debug"
    )]
    dump: Vec<DecompileStage>,
    /// Debug output detail level.
    #[arg(
        long,
        value_parser = known_value_parser::<DebugDetail>(DETAIL_VALUES),
        help_heading = "Debug"
    )]
    detail: Option<DebugDetail>,
    /// Debug color mode.
    #[arg(
        short = 'c',
        long,
        value_parser = known_value_parser::<DebugColorMode>(COLOR_VALUES),
        help_heading = "Debug"
    )]
    color: Option<DebugColorMode>,
    /// Focus a specific proto id: emits only that proto's Lua source on normal runs,
    /// or restricts stage dumps when combined with `--dump` / `-d`.
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
    /// Dump before/after snapshots for specific internal pipeline passes (comma-separated names).
    #[arg(long, value_delimiter = ',', help_heading = "Debug")]
    dump_pass: Vec<String>,
    /// List all protos in the chunk (id, parent, lines, instrs, children) and exit.
    /// Combine with `--format json` to include decoded string constants per proto.
    #[arg(long, help_heading = "Debug")]
    list_protos: bool,
}

impl DebugArgs {
    fn apply(self, options: &mut DecompileOptions) -> (bool, Option<usize>) {
        let has_explicit_dump = !self.dump.is_empty();
        // `--proto-depth` 仅配合 `--dump`/`--debug` 控制调试展开深度；单独传入不强行开启 debug dump。
        let has_explicit_debug_output =
            self.debug || has_explicit_dump || self.detail.is_some() || self.color.is_some();

        let proto_source = if !has_explicit_debug_output && !self.list_protos {
            self.proto
        } else {
            None
        };

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

        (self.list_protos, proto_source)
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
    /// Fallback names: debug-like uses numbered names, simple uses generic roles,
    /// heuristic infers names from expressions and usage. All modes prefer debug names.
    #[arg(
        short = 'n',
        long,
        value_parser = known_value_parser::<NamingMode>(NAMING_MODE_VALUES),
        help_heading = "Generate"
    )]
    naming_mode: Option<NamingMode>,
    /// Whether debug-like names should include the function index.
    #[arg(
        long,
        value_name = "BOOL",
        num_args = 0..=1,
        default_missing_value = "true",
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
    /// Apply a curated option preset before explicit flags (`readable`, `exact`, or `ai`).
    #[arg(
        long,
        value_parser = known_value_parser::<CliPreset>(PRESET_VALUES),
        help_heading = "Generate"
    )]
    preset: Option<CliPreset>,
    /// Generated source indentation width.
    #[arg(long, help_heading = "Generate")]
    indent_width: Option<usize>,
    /// Preferred maximum line length.
    #[arg(long, help_heading = "Generate")]
    max_line_length: Option<usize>,
    /// String quote style.
    #[arg(
        long,
        value_parser = known_value_parser::<QuoteStyle>(QUOTE_STYLE_VALUES),
        help_heading = "Generate"
    )]
    quote_style: Option<QuoteStyle>,
    /// Emit decoded strings as readable UTF-8 text (default: true); false preserves original bytes.
    #[arg(
        long,
        value_name = "BOOL",
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = BoolishValueParser::new(),
        help_heading = "Generate"
    )]
    readable_strings: Option<bool>,
    /// Number literal style.
    #[arg(
        long,
        value_parser = known_value_parser::<NumberFormat>(NUMBER_FORMAT_VALUES),
        help_heading = "Generate"
    )]
    number_format: Option<NumberFormat>,
    /// Table constructor layout style.
    #[arg(
        long,
        value_parser = known_value_parser::<TableStyle>(TABLE_STYLE_VALUES),
        help_heading = "Generate"
    )]
    table_style: Option<TableStyle>,
    /// Align record keys by `=` in non-single-line aligned tables
    /// (default: true).
    #[arg(
        long,
        value_name = "BOOL",
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = BoolishValueParser::new(),
        help_heading = "Generate"
    )]
    table_align_eq: Option<bool>,
    /// Max padding spaces when aligning record keys by `=`; a longer key starts
    /// a new alignment run instead of stretching every row (default: 8).
    #[arg(long, help_heading = "Generate")]
    table_align_eq_max_spaces: Option<usize>,
    /// Omit contiguous `[1]..[n]` keys in proven-safe PUC scalar constructors;
    /// dynamic/nil values and unsupported allocation layouts keep their keys (default: false).
    #[arg(
        long,
        value_name = "BOOL",
        num_args = 0..=1,
        default_missing_value = "true",
        value_parser = BoolishValueParser::new(),
        help_heading = "Generate"
    )]
    table_drop_index_keys: Option<bool>,
    /// Max rendered row width (including indentation) of `--table-style aligned` grids; defaults to `--max-line-length`.
    #[arg(long, help_heading = "Generate")]
    table_align_width: Option<usize>,
    /// Max rendered width of string literals allowed inside `--table-style aligned` grids.
    #[arg(long, help_heading = "Generate")]
    table_align_string_width: Option<usize>,
    /// Horizontal alignment of `--table-style aligned` grid cells. `auto` picks per
    /// cell kind: numbers right-align (digits and commas line up), strings, names,
    /// booleans and nil left-align (word-like values share a left edge). `left`/`right`
    /// force one direction for all kinds.
    #[arg(
        long,
        value_parser = known_value_parser::<TableCellAlign>(TABLE_ALIGN_CELLS_VALUES),
        help_heading = "Generate"
    )]
    table_align_cells: Option<TableCellAlign>,
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
    /// Comment verbosity: `minimal` (default: header + line ranges), `full` (per-proto stats), or `none` (`true`/`false` aliases supported).
    #[arg(
        long,
        value_name = "STYLE",
        value_parser = known_value_parser::<CommentStyle>(COMMENT_STYLE_VALUES),
        help_heading = "Generate"
    )]
    comment: Option<CommentStyle>,
    /// Whether unstructured control flow may be emitted as diagnostic pseudocode.
    #[arg(
        short = 'g',
        long,
        value_parser = known_value_parser::<GenerateMode>(GENERATE_MODE_VALUES),
        help_heading = "Generate"
    )]
    generate_mode: Option<GenerateMode>,
}

impl GenerateArgs {
    fn apply(self, options: &mut DecompileOptions) {
        set_if_some(&mut options.generate.indent_width, self.indent_width);
        set_if_some(&mut options.generate.max_line_length, self.max_line_length);
        set_if_some(&mut options.generate.quote_style, self.quote_style);
        set_if_some(
            &mut options.generate.readable_strings,
            self.readable_strings,
        );
        set_if_some(&mut options.generate.number_format, self.number_format);
        set_if_some(&mut options.generate.table_style, self.table_style);
        set_if_some(&mut options.generate.table_align_eq, self.table_align_eq);
        set_if_some(
            &mut options.generate.table_align_eq_max_spaces,
            self.table_align_eq_max_spaces,
        );
        set_if_some(
            &mut options.generate.table_drop_index_keys,
            self.table_drop_index_keys,
        );
        options.generate.table_align_width = self.table_align_width;
        set_if_some(
            &mut options.generate.table_align_string_width,
            self.table_align_string_width,
        );
        set_if_some(
            &mut options.generate.table_align_cells,
            self.table_align_cells,
        );
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
        if let Some(mode) = self.generate_mode {
            options.generate.mode = mode;
        }
    }
}

#[derive(Args, Debug)]
struct OutputArgs {
    /// Stop the pipeline after a specific stage.
    #[arg(
        long,
        value_parser = known_value_parser::<DecompileStage>(STAGE_VALUES),
        help_heading = "Output"
    )]
    stop_after: Option<DecompileStage>,
    /// Output file path (single chunk or `--list-protos`) or output directory path (recursive directory batch mode).
    #[arg(
        short = 'o',
        long,
        conflicts_with_all = ["debug", "dump", "detail", "color", "timing", "dump_pass"],
        help_heading = "Output"
    )]
    output: Option<PathBuf>,
    /// Output format for normal runs, `--list-protos`, and batch summaries.
    #[arg(
        long,
        value_parser = known_value_parser::<OutputFormat>(OUTPUT_FORMAT_VALUES),
        help_heading = "Output"
    )]
    format: Option<OutputFormat>,
    /// Worker thread count for directory batch decompilation (defaults to CPU count).
    #[arg(short = 'j', long, help_heading = "Output")]
    jobs: Option<usize>,
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
        decompile.generate.mode = GenerateMode::Permissive;

        if let Some(preset) = self.generate.preset {
            preset.apply(&mut decompile);
        }

        self.input.apply(&mut decompile);
        self.output.apply(&mut decompile);
        let (list_protos, proto_source) = self.debug.apply(&mut decompile);
        self.readability.apply(&mut decompile);
        self.generate.apply(&mut decompile);

        let input = self.input.input.or(self.input.input_pos);
        let source = self.input.source;
        if input.is_none() && source.is_none() {
            return Err(CliError::Usage(
                "missing input path (pass `<INPUT>`, `--input <PATH>`, or `--source <PATH>`)"
                    .to_owned(),
            ));
        }

        validate_output_request(self.output.output.as_ref(), &decompile, list_protos)?;

        Ok(CliOptions {
            input,
            source,
            output: self.output.output,
            luac: self.input.luac,
            strip_debug: self.input.strip.unwrap_or(true),
            decompile,
            list_protos,
            proto_source,
            format: self.output.format.unwrap_or(OutputFormat::Text),
            jobs: self.output.jobs,
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
    list_protos: bool,
) -> Result<(), CliError> {
    if output.is_some()
        && ((!list_protos && decompile.target_stage != DecompileStage::Generate)
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
