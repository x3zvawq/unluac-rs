//! 这些测试固定 decompile-pipeline-health。
//!
//! 它要求：编译后的 chunk 能成功反编译到最终源码，反编译源码可以重新编译并执行，
//! 而且执行结果必须和 case-health 的源码基线一致。

use unluac::decompile::{DecompileOptions, DecompileStage, decompile};

use crate::support::case_manifest::{LuaCaseDialect, decompile_pipeline_health_cases};
use crate::support::{
    TestFailure, build_case_health_baseline, compile_generated_source_to_suite_artifact,
    compile_lua_case, diff_command_outputs, failure_separator, format_case_failure, run_lua_file,
    write_generated_case_source,
};

const MAX_REPORTED_FAILURES_PER_DIALECT: usize = 5;

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
    let mut failure_count = 0;
    let mut failures = Vec::new();

    for entry in decompile_pipeline_health_cases().filter(|entry| entry.dialect == dialect) {
        if let Err(error) = assert_case_decompile_pipeline_health(&entry) {
            failure_count += 1;
            if failures.len() < MAX_REPORTED_FAILURES_PER_DIALECT {
                failures.push(format_case_failure(entry.path, &error));
            }
        }
    }

    assert!(
        failure_count == 0,
        "decompile-pipeline-health failed for {}: {} case(s) failed, showing first {}\n{}",
        dialect.luac_label(),
        failure_count,
        MAX_REPORTED_FAILURES_PER_DIALECT,
        failures.join(failure_separator())
    );
}

fn assert_case_decompile_pipeline_health(
    entry: &crate::support::case_manifest::LuaCaseManifestEntry,
) -> Result<(), TestFailure> {
    let dialect_label = entry.dialect.luac_label();
    let baseline =
        build_case_health_baseline(entry, "decompile-pipeline-health").map_err(|failure| {
            TestFailure::new(
                format!("case-health baseline failed first: {}", failure.summary()),
                format!("case-health baseline failed first\n{}", failure.detail()),
            )
        })?;
    let dialect = entry.dialect.decompile_dialect().ok_or_else(|| {
        TestFailure::new(
            "unsupported decompile dialect",
            format!("unsupported decompile dialect for {}", entry.path),
        )
    })?;

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
    .map_err(|error| {
        TestFailure::new(
            format!("decompile failed: {error}"),
            format!("decompile failed: {error}"),
        )
    })?;

    let generated = result.state.generated.as_ref().ok_or_else(|| {
        TestFailure::new(
            "generate stage finished without source",
            format!("generate stage finished without source for {}", entry.path),
        )
    })?;
    let generated_source_path = write_generated_case_source(
        dialect_label,
        "decompile-pipeline-health",
        entry.path,
        &generated.source,
    )
    .map_err(|error| {
        TestFailure::new(
            "write generated source failed",
            format!("write generated source failed: {error}"),
        )
    })?;

    let (generated_chunk_path, compile_output) = compile_generated_source_to_suite_artifact(
        dialect_label,
        entry.path,
        "decompile-pipeline-health",
        &generated_source_path,
        true,
    )
    .map_err(|error| {
        TestFailure::new(
            "compile generated source failed",
            format!("compile generated source failed: {error}"),
        )
    })?;
    if !compile_output.success() {
        let summary = format!(
            "generated source compilation failed (source artifact: {}, chunk artifact: {}, status: {})",
            generated_source_path.display(),
            generated_chunk_path.display(),
            compile_output.status_code.unwrap_or_default(),
        );
        return Err(TestFailure::new(
            summary.clone(),
            format!(
                "{summary}\n{}\ngenerated source:\n{}",
                compile_output.render(),
                generated.source
            ),
        ));
    }

    let generated_output = run_lua_file(dialect_label, &generated_chunk_path).map_err(|error| {
        TestFailure::new(
            "run generated chunk failed",
            format!("run generated chunk failed: {error}"),
        )
    })?;
    if !generated_output.success() {
        let summary = format!(
            "generated chunk execution failed (source artifact: {}, chunk artifact: {}, status: {})",
            generated_source_path.display(),
            generated_chunk_path.display(),
            generated_output.status_code.unwrap_or_default(),
        );
        return Err(TestFailure::new(
            summary.clone(),
            format!(
                "{summary}\n{}\ngenerated source:\n{}",
                generated_output.render(),
                generated.source
            ),
        ));
    }

    if let Some(diff) = diff_command_outputs(
        "expected-source",
        &baseline.source_output,
        "generated-chunk",
        &generated_output,
    ) {
        let summary = format!(
            "generated output mismatch (source artifact: {}, chunk artifact: {})",
            generated_source_path.display(),
            generated_chunk_path.display(),
        );
        return Err(TestFailure::new(
            summary.clone(),
            format!("{summary}\n{diff}\ngenerated source:\n{}", generated.source),
        ));
    }

    Ok(())
}
