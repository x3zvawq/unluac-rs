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
use unluac::decompile::{
    DebugColorMode, DecompileStage, GenerateMode, LuauVectorConstructor, LuauVectorSize,
    NamingMode, NumberFormat,
};
use unluac::parser::{ParseMode, StringDecodeMode, StringEncoding};

use super::{
    CliArgs, CompilerProtocol, OUTPUT_ONLY_SUPPORTS_FINAL_SOURCE, build_compile_command,
    emit_generated_source, parse_args,
};

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

fn command_args(command: &std::process::Command) -> Vec<String> {
    command
        .get_args()
        .map(|arg| arg.to_string_lossy().into_owned())
        .collect()
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
    assert_eq!(<&'static str>::from(options.decompile.dialect), "auto");
    assert_eq!(options.decompile.target_stage, DecompileStage::Generate);
    assert_eq!(options.decompile.naming.mode, NamingMode::DebugLike);
    assert!(!options.decompile.debug.enable);
    assert!(!options.decompile.debug.timing);
    assert!(options.decompile.debug.output_stages.is_empty());
    assert!(options.decompile.generate.comment);
    assert_eq!(options.decompile.generate.mode, GenerateMode::Permissive);
    assert_eq!(
        options.decompile.parse.string_encoding,
        StringEncoding::Auto
    );
    assert!(options.strip_debug);
    assert!(!options.decompile.parse.ignore_debug);
}

#[test]
fn ignore_debug_is_an_independent_input_policy() {
    let source = parse_args(args(&[
        "--source",
        "case.lua",
        "--strip",
        "false",
        "--ignore-debug",
    ]))
    .expect("source debug policy should parse");
    assert!(!source.strip_debug);
    assert!(source.decompile.parse.ignore_debug);

    let input = parse_args(args(&["--input", "case.luac", "--ignore-debug"]))
        .expect("compiled input debug policy should parse");
    assert!(input.decompile.parse.ignore_debug);
}

#[test]
fn strip_false_retains_source_debug_metadata() {
    let options = parse_args(args(&["--source", "case.lua", "--strip", "false"]))
        .expect("strip=false should parse for source input");

    assert!(!options.strip_debug);
}

#[test]
fn strip_rejects_compiled_chunk_input() {
    let error = parse_args(args(&["--input", "case.out", "--strip", "false"]))
        .expect_err("strip should only apply to source compilation");
    let rendered = error.to_string();

    assert!(
        rendered.contains("--input <INPUT>") && rendered.contains("--strip <BOOL>"),
        "unexpected clap error: {rendered}"
    );
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
        vec![DecompileStage::Parser, DecompileStage::Hir]
    );
}

#[test]
fn stop_after_only_accepts_outer_stages() {
    let error = parse_args(args(&["--source", "case.lua", "--stop-after", "cfg"]))
        .expect_err("cfg is internal to structure and should not be a stop target");
    let rendered = error.to_string();
    assert!(
        rendered.contains("invalid value 'cfg'") && rendered.contains("--stop-after"),
        "unexpected clap error: {rendered}"
    );
}

#[test]
fn dump_only_accepts_outer_stages() {
    let error = parse_args(args(&["--source", "case.lua", "--dump", "dataflow"]))
        .expect_err("dataflow is included in the structure dump");
    let rendered = error.to_string();
    assert!(
        rendered.contains("invalid value 'dataflow'") && rendered.contains("--dump"),
        "unexpected clap error: {rendered}"
    );
}

#[test]
fn luac_command_omits_strip_flag_when_debug_metadata_is_retained() {
    let options = parse_args(args(&["--source", "case.lua", "--strip", "false"]))
        .expect("strip=false should parse");
    let command = build_compile_command(
        &options,
        Path::new("luac"),
        CompilerProtocol::LuacStyle,
        Path::new("case.lua"),
        Path::new("case.out"),
    );

    assert_eq!(command_args(&command), ["-o", "case.out", "case.lua"]);
}

#[test]
fn luac_command_strips_debug_metadata_by_default() {
    let options = parse_args(args(&["--source", "case.lua"])).expect("source input should parse");
    let command = build_compile_command(
        &options,
        Path::new("luac"),
        CompilerProtocol::LuacStyle,
        Path::new("case.lua"),
        Path::new("case.out"),
    );

    assert_eq!(command_args(&command), ["-s", "-o", "case.out", "case.lua"]);
}

#[test]
fn luajit_command_uses_debug_flag_when_debug_metadata_is_retained() {
    let options = parse_args(args(&["--source", "case.lua", "--strip", "false"]))
        .expect("strip=false should parse");
    let command = build_compile_command(
        &options,
        Path::new("luac"),
        CompilerProtocol::LuaJitBytecodeTool,
        Path::new("case.lua"),
        Path::new("case.luajit"),
    );

    assert_eq!(command_args(&command), ["-g", "case.lua", "case.luajit"]);
}

#[test]
fn luau_command_uses_full_debug_level_when_debug_metadata_is_retained() {
    let options = parse_args(args(&["--source", "case.luau", "--strip", "false"]))
        .expect("strip=false should parse");
    let command = build_compile_command(
        &options,
        Path::new("luau-compile"),
        CompilerProtocol::LuauBinaryStdout,
        Path::new("case.luau"),
        Path::new("case.luau-bytecode"),
    );

    assert_eq!(command_args(&command), ["--binary", "-g2", "case.luau"]);
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
        "strict",
        "--number-format",
        "hex",
    ]))
    .expect("short flags should parse");
    assert_eq!(options.source, Some(PathBuf::from("case.lua")));
    assert_eq!(options.luac, Some(PathBuf::from("lua54-luac")));
    assert_eq!(<&'static str>::from(options.decompile.dialect), "lua5.4");
    assert_eq!(
        options.decompile.parse.string_encoding,
        "gbk".parse().unwrap()
    );
    assert_eq!(
        options.decompile.parse.string_decode_mode,
        StringDecodeMode::Lossy
    );
    assert_eq!(options.decompile.parse.mode, ParseMode::Strict);
    assert_eq!(options.decompile.debug.color, DebugColorMode::Never);
    assert!(options.decompile.debug.enable);
    assert!(options.decompile.debug.timing);
    assert_eq!(options.decompile.naming.mode, NamingMode::Simple);
    assert_eq!(options.decompile.generate.mode, GenerateMode::Strict);
    assert_eq!(options.decompile.generate.number_format, NumberFormat::Hex);
}

#[test]
fn encoding_auto_arg_maps_to_auto() {
    let options = parse_args(args(&["--source", "case.lua", "--encoding", "auto"]))
        .expect("auto encoding should parse");

    assert_eq!(
        options.decompile.parse.string_encoding,
        StringEncoding::Auto
    );
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
fn naming_mode_and_bool_option_override_defaults() {
    let options = parse_args(args(&[
        "--source",
        "case.lua",
        "--naming-mode",
        "simple",
        "--debug-like-include-function",
        "false",
        "--comment",
        "false",
        "--generate-mode",
        "strict",
    ]))
    .expect("boolish options should parse");
    assert_eq!(options.decompile.naming.mode, NamingMode::Simple);
    assert!(!options.decompile.naming.debug_like_include_function);
    assert!(!options.decompile.generate.comment);
    assert_eq!(options.decompile.generate.mode, GenerateMode::Strict);
}

#[test]
fn luau_vector_options_map_to_generate_config() {
    let options = parse_args(args(&[
        "--source",
        "case.luau",
        "--dialect",
        "luau",
        "--luau-vector-library",
        "Vector3",
        "--luau-vector-constructor",
        "new",
        "--luau-vector-size",
        "3",
    ]))
    .expect("Luau vector options should parse");

    assert_eq!(
        options.decompile.generate.luau_vector_constructor,
        Some(LuauVectorConstructor {
            library: Some("Vector3".to_owned()),
            constructor: "new".to_owned(),
            size: LuauVectorSize::Three,
        })
    );
}

#[test]
fn luau_vector_library_requires_constructor() {
    let error = parse_args(args(&[
        "--source",
        "case.luau",
        "--dialect",
        "luau",
        "--luau-vector-library",
        "Vector3",
    ]))
    .expect_err("vector library without constructor should fail");

    assert!(error.to_string().contains("--luau-vector-constructor"));
}

#[test]
fn luau_vector_constructor_requires_size() {
    let error = parse_args(args(&[
        "--source",
        "case.luau",
        "--dialect",
        "luau",
        "--luau-vector-constructor",
        "vector",
    ]))
    .expect_err("vector constructor without a size should fail");

    assert!(error.to_string().contains("--luau-vector-size"));
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
    assert!(help.contains("--strip <BOOL>"));
    assert!(help.contains("--number-format <NUMBER_FORMAT>"));
    assert!(help.contains("-o, --output <OUTPUT>"));
    assert!(input < debug && debug < generate && generate < output);
}

#[test]
fn version_includes_binary_name_and_repo_link() {
    let version = render_version();
    assert!(version.contains(&format!("unluac-cli {}", env!("CARGO_PKG_VERSION"))));
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
