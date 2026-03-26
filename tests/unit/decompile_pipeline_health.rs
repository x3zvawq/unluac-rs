//! 这些测试固定 decompile-pipeline-health。
//!
//! 它要求：编译后的 chunk 能成功反编译到最终源码，反编译源码可以重新编译并执行，
//! 而且执行结果必须和 case-health 的源码基线一致。

use unluac::decompile::{DecompileOptions, DecompileStage, decompile};

use crate::support::case_manifest::{LuaCaseDialect, decompile_pipeline_health_cases};
use crate::support::{
    build_case_health_baseline, compile_generated_source_to_suite_artifact, compile_lua_case,
    diff_command_outputs, run_lua_file, write_generated_case_source,
};

#[test]
fn lua51_cases_keep_decompile_pipeline_health() {
    assert_decompile_pipeline_health_for_dialect(LuaCaseDialect::Lua51);
}

#[test]
fn lua52_cases_keep_decompile_pipeline_health() {
    assert_decompile_pipeline_health_for_dialect(LuaCaseDialect::Lua52);
}

#[test]
fn lua53_cases_keep_decompile_pipeline_health() {
    assert_decompile_pipeline_health_for_dialect(LuaCaseDialect::Lua53);
}

#[test]
fn lua54_cases_keep_decompile_pipeline_health() {
    assert_decompile_pipeline_health_for_dialect(LuaCaseDialect::Lua54);
}

#[test]
fn lua55_cases_keep_decompile_pipeline_health() {
    assert_decompile_pipeline_health_for_dialect(LuaCaseDialect::Lua55);
}

fn assert_decompile_pipeline_health_for_dialect(dialect: LuaCaseDialect) {
    let mut failures = Vec::new();

    for entry in decompile_pipeline_health_cases().filter(|entry| entry.dialect == dialect) {
        if let Err(error) = assert_case_decompile_pipeline_health(&entry) {
            failures.push(format!("case: {}\n{}", entry.path, error));
        }
    }

    assert!(
        failures.is_empty(),
        "decompile-pipeline-health failed for {}:\n\n{}",
        dialect.luac_label(),
        failures.join("\n\n")
    );
}

fn assert_case_decompile_pipeline_health(
    entry: &crate::support::case_manifest::LuaCaseManifestEntry,
) -> Result<(), String> {
    let dialect_label = entry.dialect.luac_label();
    let baseline = build_case_health_baseline(entry, "decompile-pipeline-health")
        .map_err(|error| format!("case-health baseline failed first:\n{error}"))?;
    let dialect = entry
        .dialect
        .decompile_dialect()
        .ok_or_else(|| format!("unsupported decompile dialect for {}", entry.path))?;

    let chunk = compile_lua_case(dialect_label, entry.path);
    let result = decompile(
        &chunk,
        DecompileOptions {
            dialect,
            target_stage: DecompileStage::Generate,
            debug: Default::default(),
            ..DecompileOptions::default()
        },
    )
    .map_err(|error| format!("decompile failed: {error}"))?;

    let generated = result
        .state
        .generated
        .as_ref()
        .ok_or_else(|| format!("generate stage finished without source for {}", entry.path))?;
    let generated_source_path = write_generated_case_source(
        dialect_label,
        "decompile-pipeline-health",
        entry.path,
        &generated.source,
    )?;

    let (generated_chunk_path, compile_output) = compile_generated_source_to_suite_artifact(
        dialect_label,
        entry.path,
        "decompile-pipeline-health",
        &generated_source_path,
        true,
    )?;
    if !compile_output.success() {
        return Err(format!(
            "generated source compilation failed\nsource artifact: {}\nchunk artifact: {}\n{}\ngenerated source:\n{}",
            generated_source_path.display(),
            generated_chunk_path.display(),
            compile_output.render(),
            generated.source
        ));
    }

    let generated_output = run_lua_file(dialect_label, &generated_chunk_path)
        .map_err(|error| format!("run generated chunk failed: {error}"))?;
    if !generated_output.success() {
        return Err(format!(
            "generated chunk execution failed\nsource artifact: {}\nchunk artifact: {}\n{}\ngenerated source:\n{}",
            generated_source_path.display(),
            generated_chunk_path.display(),
            generated_output.render(),
            generated.source
        ));
    }

    if let Some(diff) = diff_command_outputs(
        "expected-source",
        &baseline.source_output,
        "generated-chunk",
        &generated_output,
    ) {
        return Err(format!(
            "generated output mismatch\nsource artifact: {}\nchunk artifact: {}\n{}\ngenerated source:\n{}",
            generated_source_path.display(),
            generated_chunk_path.display(),
            diff,
            generated.source
        ));
    }

    Ok(())
}
