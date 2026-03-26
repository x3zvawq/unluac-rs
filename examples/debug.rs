//! 这个 example 提供一个“改常量后直接运行”的开发调试入口。
//!
//! 它和正式 CLI 分开，是为了让日常排错可以直接在代码里固定 dialect、source
//! 和 dump 细节，而不会把真正对外的命令行入口越堆越像测试脚本。

use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugFilters, DebugOptions, DecompileDialect, DecompileOptions,
    DecompileStage, ReadabilityOptions, decompile, render_timing_report,
};
use unluac::naming::{NamingMode, NamingOptions};
use unluac::parser::{ParseMode, ParseOptions, StringDecodeMode, StringEncoding};

/// 开发时最常改的是这几个常量，直接编辑代码通常比来回敲命令更顺手。
const DIALECT: DecompileDialect = DecompileDialect::Lua51;
const SOURCE: &str = "tests/lua_cases/common/control_flow/07_branch_state_carry.lua";
const STRING_ENCODING: StringEncoding = StringEncoding::Utf8;
const STRING_DECODE_MODE: StringDecodeMode = StringDecodeMode::Strict;
const PARSE_MODE: ParseMode = ParseMode::Strict;
// 这个入口更常用来直接看“最终会长成什么源码形状”，所以默认停在 Readability。
const TARGET_STAGE: DecompileStage = DecompileStage::Generate;
const DEBUG_DETAIL: DebugDetail = DebugDetail::Verbose;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let source = repo_root.join(SOURCE);
    let luac = repo_root
        .join("lua")
        .join("build")
        .join(DIALECT.label())
        .join("luac");
    let chunk = compile_source(&luac, &source, DIALECT)?;
    let bytes = fs::read(&chunk)?;

    let result = decompile(
        &bytes,
        DecompileOptions {
            dialect: DIALECT,
            parse: ParseOptions {
                mode: PARSE_MODE,
                string_encoding: STRING_ENCODING,
                string_decode_mode: STRING_DECODE_MODE,
            },
            target_stage: TARGET_STAGE,
            debug: DebugOptions {
                enable: true,
                output_stages: vec![TARGET_STAGE],
                timing: false,
                color: DebugColorMode::Always,
                detail: DEBUG_DETAIL,
                filters: DebugFilters::default(),
            },
            readability: ReadabilityOptions {
                return_inline_max_complexity: 10,
                index_inline_max_complexity: 10,
                args_inline_max_complexity: 6,
                access_base_inline_max_complexity: 5,
            },
            naming: NamingOptions {
                mode: NamingMode::DebugLike,
                debug_like_include_function: true,
            },
            generate: Default::default(),
        },
    )?;

    println!("== Debug Input ==");
    println!("dialect: {}", DIALECT.label());
    println!("source: {}", source.display());
    println!("luac:   {}", luac.display());
    println!("chunk:  {}", chunk.display());
    println!();

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
                render_timing_report(report, DEBUG_DETAIL, DebugColorMode::Auto)
            );
        }
    }

    Ok(())
}

fn compile_source(
    luac: &Path,
    source: &Path,
    dialect: DecompileDialect,
) -> Result<PathBuf, Box<dyn std::error::Error>> {
    if !luac.exists() {
        return Err(format!(
            "missing bundled luac for {}: {}",
            dialect.label(),
            luac.display()
        )
        .into());
    }

    let output_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("unluac-debug")
        .join("examples")
        .join(dialect.label());
    fs::create_dir_all(&output_dir)?;

    let file_stem = source
        .file_stem()
        .and_then(OsStr::to_str)
        .unwrap_or("debug");
    let output = output_dir.join(format!("{file_stem}.out"));

    let status = Command::new(luac)
        .arg("-s")
        .arg("-o")
        .arg(&output)
        .arg(source)
        .status()?;
    if !status.success() {
        return Err(format!("luac exited with status {status}").into());
    }

    Ok(output)
}
