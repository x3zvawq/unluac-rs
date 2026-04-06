//! 这个文件覆盖 CLI 参数解析、帮助文案和输出路由的局部不变量。
//!
//! 这里重点锁定两类容易回退的对外行为：
//! 1. 长短参数是否持续映射到同一份 CLI 语义。
//! 2. `--output`、`--help`、`--version` 这些纯 CLI 侧体验是否稳定。

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use clap::CommandFactory;
use unluac::decompile::{DebugColorMode, DecompileStage, GenerateMode, NamingMode};
use unluac::parser::{ParseMode, StringDecodeMode, StringEncoding};

use super::{CliArgs, OUTPUT_ONLY_SUPPORTS_FINAL_SOURCE, emit_generated_source, parse_args};

fn args(values: &[&str]) -> Vec<OsString> {
    std::iter::once(OsString::from("unluac-cli"))
        .chain(values.iter().map(OsString::from))
        .collect()
}

fn unique_temp_path(name: &str) -> PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after unix epoch")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "unluac-cli-tests-{}-{name}-{nonce}",
        std::process::id()
    ))
}

fn render_help() -> String {
    let mut command = CliArgs::command();
    command.render_long_help().to_string()
}

fn render_version() -> String {
    let command = CliArgs::command();
    command.render_long_version()
}

#[test]
fn requires_explicit_input_or_source() {
    let error = parse_args(args(&[])).expect_err("cli should require input or source");
    let rendered = error.to_string();
    assert!(
        rendered.contains("--input <INPUT>") || rendered.contains("--source <SOURCE>"),
        "unexpected clap error: {rendered}"
    );
}

#[test]
fn defaults_to_pure_source_output_when_only_source_is_given() {
    let options = parse_args(args(&["--source", "case.lua"])).expect("source should parse");
    assert_eq!(options.source, Some(PathBuf::from("case.lua")));
    assert_eq!(options.decompile.dialect.label(), "lua5.1");
    assert_eq!(options.decompile.target_stage, DecompileStage::Generate);
    assert_eq!(options.decompile.naming.mode, NamingMode::DebugLike);
    assert!(!options.decompile.debug.enable);
    assert!(!options.decompile.debug.timing);
    assert!(options.decompile.debug.output_stages.is_empty());
    assert!(options.decompile.generate.comment);
}

#[test]
fn debug_flag_reenables_repo_debug_stage_dump() {
    let options =
        parse_args(args(&["--source", "case.lua", "--debug"])).expect("debug flag should parse");
    assert!(options.decompile.debug.enable);
    assert_eq!(
        options.decompile.debug.output_stages,
        vec![DecompileStage::Generate]
    );
}

#[test]
fn stop_after_without_explicit_dump_tracks_new_target_stage() {
    let options = parse_args(args(&["--source", "case.lua", "--stop-after", "hir"]))
        .expect("stop-after should parse");
    assert_eq!(options.decompile.target_stage, DecompileStage::Hir);
    assert!(!options.decompile.debug.enable);
    assert!(options.decompile.debug.output_stages.is_empty());
}

#[test]
fn stop_after_with_debug_tracks_new_target_stage() {
    let options = parse_args(args(&[
        "--source",
        "case.lua",
        "--debug",
        "--stop-after",
        "hir",
    ]))
    .expect("stop-after debug should parse");
    assert_eq!(options.decompile.target_stage, DecompileStage::Hir);
    assert_eq!(
        options.decompile.debug.output_stages,
        vec![DecompileStage::Hir]
    );
}

#[test]
fn explicit_dump_replaces_repo_debug_dump_stage() {
    let options = parse_args(args(&[
        "--source", "case.lua", "--dump", "parse", "--dump", "hir",
    ]))
    .expect("dump should parse");
    assert!(options.decompile.debug.enable);
    assert_eq!(
        options.decompile.debug.output_stages,
        vec![DecompileStage::Parse, DecompileStage::Hir]
    );
}

#[test]
fn timing_without_dump_emits_only_timing_report() {
    let options =
        parse_args(args(&["--source", "case.lua", "--timing"])).expect("timing should parse");
    assert!(options.decompile.debug.enable);
    assert!(options.decompile.debug.timing);
    assert!(options.decompile.debug.output_stages.is_empty());
}

#[test]
fn short_flags_map_to_the_same_cli_fields() {
    let options = parse_args(args(&[
        "-s",
        "case.lua",
        "-D",
        "lua5.4",
        "-d",
        "-l",
        "lua54-luac",
        "-e",
        "gbk",
        "-m",
        "lossy",
        "-p",
        "strict",
        "-c",
        "never",
        "-t",
        "-n",
        "simple",
        "-g",
        "best-effort",
    ]))
    .expect("short flags should parse");
    assert_eq!(options.source, Some(PathBuf::from("case.lua")));
    assert_eq!(options.luac, Some(PathBuf::from("lua54-luac")));
    assert_eq!(options.decompile.dialect.label(), "lua5.4");
    assert_eq!(options.decompile.parse.string_encoding, StringEncoding::Gbk);
    assert_eq!(
        options.decompile.parse.string_decode_mode,
        StringDecodeMode::Lossy
    );
    assert_eq!(options.decompile.parse.mode, ParseMode::Strict);
    assert_eq!(options.decompile.debug.color, DebugColorMode::Never);
    assert!(options.decompile.debug.enable);
    assert!(options.decompile.debug.timing);
    assert_eq!(options.decompile.naming.mode, NamingMode::Simple);
    assert_eq!(options.decompile.generate.mode, GenerateMode::BestEffort);
}

#[test]
fn output_short_flag_parses_for_pure_final_source_runs() {
    let options =
        parse_args(args(&["-s", "case.lua", "-o", "out.lua"])).expect("output flag should parse");
    assert_eq!(options.output, Some(PathBuf::from("out.lua")));
    assert!(!options.decompile.debug.enable);
    assert_eq!(options.decompile.target_stage, DecompileStage::Generate);
}

#[test]
fn output_rejects_debug_related_flags() {
    let cases = [
        (
            &["-s", "case.lua", "-o", "out.lua", "--debug"][..],
            "--debug",
        ),
        (
            &["-s", "case.lua", "-o", "out.lua", "--dump", "parse"][..],
            "--dump <DUMP>",
        ),
        (
            &["-s", "case.lua", "-o", "out.lua", "--detail", "summary"][..],
            "--detail <DETAIL>",
        ),
        (
            &["-s", "case.lua", "-o", "out.lua", "--color", "never"][..],
            "--color <COLOR>",
        ),
        (
            &["-s", "case.lua", "-o", "out.lua", "--proto", "1"][..],
            "--proto <PROTO>",
        ),
        (
            &["-s", "case.lua", "-o", "out.lua", "--timing"][..],
            "--timing",
        ),
    ];

    for (argv, conflicting_flag) in cases {
        let error = parse_args(args(argv)).expect_err("conflicting output mode should fail");
        let rendered = error.to_string();
        assert!(
            rendered.contains("--output <OUTPUT>") && rendered.contains(conflicting_flag),
            "unexpected clap error for {conflicting_flag}: {rendered}"
        );
    }
}

#[test]
fn output_rejects_non_generate_target_stage() {
    let error = parse_args(args(&[
        "-s",
        "case.lua",
        "--stop-after",
        "hir",
        "-o",
        "out.lua",
    ]))
    .expect_err("output should require the final generate stage");
    let rendered = error.to_string();
    assert!(
        rendered.contains(OUTPUT_ONLY_SUPPORTS_FINAL_SOURCE),
        "unexpected output validation error: {rendered}"
    );
}

#[test]
fn naming_mode_and_bool_options_override_defaults() {
    let options = parse_args(args(&[
        "--source",
        "case.lua",
        "--naming-mode",
        "simple",
        "--debug-like-include-function",
        "false",
        "--conservative-output",
        "false",
        "--comment",
        "false",
        "--generate-mode",
        "best-effort",
    ]))
    .expect("boolish options should parse");
    assert_eq!(options.decompile.naming.mode, NamingMode::Simple);
    assert!(!options.decompile.naming.debug_like_include_function);
    assert!(!options.decompile.generate.conservative_output);
    assert!(!options.decompile.generate.comment);
    assert_eq!(options.decompile.generate.mode, GenerateMode::BestEffort);
}

#[test]
fn help_is_grouped_by_section_and_includes_repo_link() {
    let help = render_help();
    let input = help
        .find("Input:\n")
        .expect("help should include Input heading");
    let debug = help
        .find("Debug:\n")
        .expect("help should include Debug heading");
    let generate = help
        .find("Generate:\n")
        .expect("help should include Generate heading");
    let output = help
        .find("Output:\n")
        .expect("help should include Output heading");

    assert!(help.contains("unluac-cli"));
    assert!(help.contains("Repository: https://github.com/x3zvawq/unluac-rs"));
    assert!(help.contains("-i, --input <INPUT>"));
    assert!(help.contains("-s, --source <SOURCE>"));
    assert!(help.contains("-o, --output <OUTPUT>"));
    assert!(input < debug && debug < generate && generate < output);
}

#[test]
fn version_includes_binary_name_and_repo_link() {
    let version = render_version();
    assert!(version.contains("unluac-cli 1.0.0"));
    assert!(version.contains("https://github.com/x3zvawq/unluac-rs"));
}

#[test]
fn emit_generated_source_writes_requested_output_file() {
    let output_dir = unique_temp_path("output-file");
    let output_path = output_dir.join("case.lua");
    fs::create_dir_all(&output_dir).expect("test temp directory should be created");

    let routed = emit_generated_source("print(1)\n", Some(output_path.as_path()))
        .expect("writing generated source should succeed");
    assert!(routed.is_none());
    assert_eq!(
        fs::read_to_string(&output_path).expect("output file should be readable"),
        "print(1)\n"
    );

    fs::remove_dir_all(&output_dir).expect("test temp directory should be removable");
}

#[test]
fn emit_generated_source_keeps_stdout_mode_when_output_is_not_requested() {
    let routed = emit_generated_source("print(1)\n", Option::<&Path>::None)
        .expect("stdout mode should not fail");
    assert_eq!(routed, Some("print(1)\n"));
}
