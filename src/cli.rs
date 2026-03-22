//! 这个文件实现一个面向本地调试的轻量 CLI。
//!
//! 它故意不做成复杂命令系统，而是优先服务当前“快速编译一个 Lua case 并看
//! dump 输出”的工作流；等后续 pipeline 层数变多，再在这个壳上继续扩展。

use std::env;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use unluac::decompile::{
    DebugDetail, DebugFilters, DebugOptions, DecompileDialect, DecompileOptions, DecompileStage,
    decompile,
};
use unluac::parser::{ParseMode, StringDecodeMode, StringEncoding};

const DEFAULT_SOURCE: &str = "tests/cases/common/control_flow/07_branch_state_carry.lua";

#[derive(Debug)]
struct CliOptions {
    dialect: DecompileDialect,
    input: Option<PathBuf>,
    source: Option<PathBuf>,
    luac: Option<PathBuf>,
    parse_mode: ParseMode,
    string_encoding: StringEncoding,
    string_decode_mode: StringDecodeMode,
    target_stage: DecompileStage,
    debug_options: DebugOptions,
}

impl Default for CliOptions {
    fn default() -> Self {
        Self {
            dialect: DecompileDialect::Lua51,
            input: None,
            source: Some(repo_root().join(DEFAULT_SOURCE)),
            luac: None,
            parse_mode: ParseMode::Strict,
            string_encoding: StringEncoding::Utf8,
            string_decode_mode: StringDecodeMode::Strict,
            target_stage: DecompileStage::Parse,
            debug_options: DebugOptions {
                enable: true,
                output_stages: vec![DecompileStage::Parse],
                detail: DebugDetail::Normal,
                filters: DebugFilters::default(),
            },
        }
    }
}

pub fn run<I>(args: I) -> Result<(), CliError>
where
    I: IntoIterator<Item = OsString>,
{
    let options = parse_args(args)?;
    let input_path = resolve_input_path(&options)?;
    let bytes = fs::read(&input_path).map_err(|source| CliError::Io {
        action: "read input chunk",
        path: input_path.clone(),
        source,
    })?;
    let CliOptions {
        dialect,
        parse_mode,
        string_encoding,
        string_decode_mode,
        target_stage,
        debug_options,
        ..
    } = options;

    let result = decompile(
        &bytes,
        DecompileOptions {
            dialect,
            parse: unluac::parser::ParseOptions {
                mode: parse_mode,
                string_encoding,
                string_decode_mode,
            },
            target_stage,
            debug: debug_options,
        },
    )?;

    if result.debug_output.is_empty() {
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
    }

    Ok(())
}

fn parse_args<I>(args: I) -> Result<CliOptions, CliError>
where
    I: IntoIterator<Item = OsString>,
{
    let mut options = CliOptions::default();
    let mut saw_explicit_dump = false;
    let mut args = args.into_iter();
    let _program = args.next();

    while let Some(arg) = args.next() {
        let Some(value) = arg.to_str() else {
            return Err(CliError::Usage("只支持 UTF-8 形式的命令行参数".to_owned()));
        };

        if matches!(value, "-h" | "--help") {
            print_help();
            return Err(CliError::HelpShown);
        }

        if let Some(flag) = value.strip_prefix("--dialect=") {
            options.dialect = parse_dialect(flag)?;
            continue;
        }
        if value == "--dialect" {
            options.dialect = parse_dialect(next_value(&mut args, "--dialect")?)?;
            continue;
        }
        if let Some(flag) = value.strip_prefix("--input=") {
            options.input = Some(PathBuf::from(flag));
            options.source = None;
            continue;
        }
        if value == "--input" {
            options.input = Some(PathBuf::from(next_value(&mut args, "--input")?));
            options.source = None;
            continue;
        }
        if let Some(flag) = value.strip_prefix("--source=") {
            options.source = Some(PathBuf::from(flag));
            continue;
        }
        if value == "--source" {
            options.source = Some(PathBuf::from(next_value(&mut args, "--source")?));
            continue;
        }
        if let Some(flag) = value.strip_prefix("--luac=") {
            options.luac = Some(PathBuf::from(flag));
            continue;
        }
        if value == "--luac" {
            options.luac = Some(PathBuf::from(next_value(&mut args, "--luac")?));
            continue;
        }
        if let Some(flag) = value.strip_prefix("--encoding=") {
            options.string_encoding = parse_string_encoding(flag)?;
            continue;
        }
        if value == "--encoding" {
            options.string_encoding = parse_string_encoding(next_value(&mut args, "--encoding")?)?;
            continue;
        }
        if let Some(flag) = value.strip_prefix("--decode-mode=") {
            options.string_decode_mode = parse_string_decode_mode(flag)?;
            continue;
        }
        if value == "--decode-mode" {
            options.string_decode_mode =
                parse_string_decode_mode(next_value(&mut args, "--decode-mode")?)?;
            continue;
        }
        if let Some(flag) = value.strip_prefix("--parse-mode=") {
            options.parse_mode = parse_parse_mode(flag)?;
            continue;
        }
        if value == "--parse-mode" {
            options.parse_mode = parse_parse_mode(next_value(&mut args, "--parse-mode")?)?;
            continue;
        }
        if let Some(flag) = value.strip_prefix("--dump=") {
            if !saw_explicit_dump {
                // 默认值只是为了开箱即用；一旦用户显式指定，就以用户列表为准。
                options.debug_options.output_stages.clear();
                saw_explicit_dump = true;
            }
            options.debug_options.output_stages.push(parse_stage(flag)?);
            options.debug_options.enable = true;
            continue;
        }
        if value == "--dump" {
            if !saw_explicit_dump {
                // 默认值只是为了开箱即用；一旦用户显式指定，就以用户列表为准。
                options.debug_options.output_stages.clear();
                saw_explicit_dump = true;
            }
            options
                .debug_options
                .output_stages
                .push(parse_stage(next_value(&mut args, "--dump")?)?);
            options.debug_options.enable = true;
            continue;
        }
        if let Some(flag) = value.strip_prefix("--stop-after=") {
            options.target_stage = parse_stage(flag)?;
            continue;
        }
        if value == "--stop-after" {
            options.target_stage = parse_stage(next_value(&mut args, "--stop-after")?)?;
            continue;
        }
        if let Some(flag) = value.strip_prefix("--detail=") {
            options.debug_options.detail = parse_debug_detail(flag)?;
            continue;
        }
        if value == "--detail" {
            options.debug_options.detail = parse_debug_detail(next_value(&mut args, "--detail")?)?;
            continue;
        }
        if let Some(flag) = value.strip_prefix("--proto=") {
            options.debug_options.filters.proto = Some(parse_usize(flag, "--proto")?);
            continue;
        }
        if value == "--proto" {
            options.debug_options.filters.proto =
                Some(parse_usize(next_value(&mut args, "--proto")?, "--proto")?);
            continue;
        }
        if value == "--no-debug" {
            options.debug_options.enable = false;
            options.debug_options.output_stages.clear();
            continue;
        }

        return Err(CliError::Usage(format!("unknown flag: {value}")));
    }

    if options.input.is_some() && options.source.is_some() {
        return Err(CliError::Usage(
            "`--input` 和 `--source` 不能同时出现".to_owned(),
        ));
    }

    Ok(options)
}

fn next_value<I>(args: &mut I, flag: &str) -> Result<String, CliError>
where
    I: Iterator<Item = OsString>,
{
    let Some(value) = args.next() else {
        return Err(CliError::Usage(format!("missing value for {flag}")));
    };
    value
        .into_string()
        .map_err(|_| CliError::Usage(format!("{flag} 只支持 UTF-8 参数值")))
}

fn resolve_input_path(options: &CliOptions) -> Result<PathBuf, CliError> {
    if let Some(input) = options.input.as_ref() {
        return Ok(input.clone());
    }

    let source = options
        .source
        .as_ref()
        .ok_or_else(|| CliError::Usage("缺少 `--input` 或 `--source`".to_owned()))?;
    compile_source(options, source)
}

fn compile_source(options: &CliOptions, source: &Path) -> Result<PathBuf, CliError> {
    let luac = resolve_luac(options)?;
    let output_dir = repo_root()
        .join("target")
        .join("unluac-debug")
        .join(options.dialect.label());
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
    let output = output_dir.join(format!("{file_stem}.out"));

    let status = Command::new(&luac)
        .arg("-s")
        .arg("-o")
        .arg(&output)
        .arg(source)
        .status()
        .map_err(|source_error| CliError::Io {
            action: "spawn luac",
            path: luac.clone(),
            source: source_error,
        })?;

    if !status.success() {
        return Err(CliError::Process(format!(
            "luac exited with status {status} while compiling {}",
            source.display()
        )));
    }

    Ok(output)
}

fn resolve_luac(options: &CliOptions) -> Result<PathBuf, CliError> {
    if let Some(path) = options.luac.as_ref() {
        return Ok(path.clone());
    }

    let bundled = repo_root()
        .join("lua")
        .join("build")
        .join(options.dialect.label())
        .join("luac");
    if bundled.exists() {
        return Ok(bundled);
    }

    Ok(match options.dialect {
        DecompileDialect::Lua51 => PathBuf::from("luac"),
    })
}

fn parse_dialect(value: impl AsRef<str>) -> Result<DecompileDialect, CliError> {
    let value = value.as_ref();
    DecompileDialect::parse(value)
        .ok_or_else(|| CliError::Usage(format!("unsupported dialect: {value}")))
}

fn parse_stage(value: impl AsRef<str>) -> Result<DecompileStage, CliError> {
    let value = value.as_ref();
    DecompileStage::parse(value)
        .ok_or_else(|| CliError::Usage(format!("unsupported stage: {value}")))
}

fn parse_debug_detail(value: impl AsRef<str>) -> Result<DebugDetail, CliError> {
    let value = value.as_ref();
    DebugDetail::parse(value)
        .ok_or_else(|| CliError::Usage(format!("unsupported debug detail: {value}")))
}

fn parse_string_encoding(value: impl AsRef<str>) -> Result<StringEncoding, CliError> {
    let value = value.as_ref();
    match value {
        "utf8" | "utf-8" => Ok(StringEncoding::Utf8),
        "gbk" => Ok(StringEncoding::Gbk),
        _ => Err(CliError::Usage(format!("unsupported encoding: {value}"))),
    }
}

fn parse_string_decode_mode(value: impl AsRef<str>) -> Result<StringDecodeMode, CliError> {
    let value = value.as_ref();
    match value {
        "strict" => Ok(StringDecodeMode::Strict),
        "lossy" => Ok(StringDecodeMode::Lossy),
        _ => Err(CliError::Usage(format!(
            "unsupported string decode mode: {value}"
        ))),
    }
}

fn parse_parse_mode(value: impl AsRef<str>) -> Result<ParseMode, CliError> {
    let value = value.as_ref();
    match value {
        "strict" => Ok(ParseMode::Strict),
        "permissive" => Ok(ParseMode::Permissive),
        _ => Err(CliError::Usage(format!("unsupported parse mode: {value}"))),
    }
}

fn parse_usize(value: impl AsRef<str>, flag: &str) -> Result<usize, CliError> {
    let value = value.as_ref();
    value
        .parse()
        .map_err(|_| CliError::Usage(format!("invalid integer for {flag}: {value}")))
}

fn print_help() {
    println!("usage:");
    println!("  cargo run -- --dialect=lua5.1");
    println!("  cargo run -- --dialect=lua5.1 --source tests/cases/lua5.1/01_setfenv.lua");
    println!("  cargo run -- --dialect=lua5.1 --input /path/to/chunk.out --detail=verbose");
    println!();
    println!("options:");
    println!("  --dialect <lua5.1>");
    println!("  --input <chunk-path>");
    println!("  --source <lua-source-path>");
    println!("  --luac <luac-path>");
    println!("  --encoding <utf8|gbk>");
    println!("  --decode-mode <strict|lossy>");
    println!("  --parse-mode <strict|permissive>");
    println!("  --dump <stage>");
    println!("  --stop-after <stage>");
    println!("  --detail <summary|normal|verbose>");
    println!("  --proto <id>");
    println!("  --no-debug");
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
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
