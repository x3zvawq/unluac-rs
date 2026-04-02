use std::ffi::OsString;
use std::path::PathBuf;

use unluac::decompile::{DecompileStage, GenerateMode, NamingMode};

use super::parse_args;

fn args(values: &[&str]) -> Vec<OsString> {
    std::iter::once(OsString::from("unluac"))
        .chain(values.iter().map(OsString::from))
        .collect()
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
        "--generate-mode",
        "best-effort",
    ]))
    .expect("boolish options should parse");
    assert_eq!(options.decompile.naming.mode, NamingMode::Simple);
    assert!(!options.decompile.naming.debug_like_include_function);
    assert!(!options.decompile.generate.conservative_output);
    assert_eq!(options.decompile.generate.mode, GenerateMode::BestEffort);
}
