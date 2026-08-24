//! 编排源码执行、编译、反编译、回编译与收敛检查；依赖 toolchain 和专题断言，不负责解析 case 清单；例如执行 unit/regression 的完整往返流水线。

use super::*;

/// 使用 vendored 的 `lua` 直接执行某个仓库内 Lua case。
pub(crate) fn run_lua_case(
    dialect_label: &str,
    source_relative: &str,
) -> Result<LuaCommandOutput, String> {
    let source = repo_root().join(source_relative);
    run_lua_file(dialect_label, &source)
}

/// 使用 vendored 的 `lua` 执行一个已经落盘的 Lua 源码或 chunk 文件。
pub(crate) fn run_lua_file(
    dialect_label: &str,
    input_path: &Path,
) -> Result<LuaCommandOutput, String> {
    let toolchain = lua_toolchain(dialect_label)?;
    let runtime = lua_tool_path(dialect_label, toolchain.runtime_name)?;
    run_command(&runtime, [input_path.as_os_str()], toolchain.runtime_name)
}

pub(super) fn run_lua_file_with_args(
    dialect_label: &str,
    input_path: &Path,
    args: &[&str],
) -> Result<LuaCommandOutput, String> {
    let toolchain = lua_toolchain(dialect_label)?;
    let runtime = lua_tool_path(dialect_label, toolchain.runtime_name)?;
    run_command(
        &runtime,
        std::iter::once(input_path.as_os_str()).chain(args.iter().map(OsStr::new)),
        toolchain.runtime_name,
    )
}

/// 使用 vendored 的 `luac` 把一个仓库内 case 编译到 health suite 的稳定产物路径。
pub(crate) fn compile_lua_case_to_suite_artifact(
    entry: &LuaCaseManifestEntry,
    suite_label: &str,
    artifact_label: &str,
    strip_debug: bool,
) -> Result<(PathBuf, LuaCommandOutput), String> {
    let dialect_label = <&'static str>::from(entry.dialect);
    let toolchain = lua_toolchain(dialect_label)?;
    let source = repo_root().join(entry.path);
    let output = suite_artifact_path(
        suite_label,
        dialect_label,
        entry.variant,
        artifact_label,
        entry.path,
        toolchain.chunk_extension,
    );
    let command_output =
        compile_lua_file_to_path(dialect_label, &source, &output, strip_debug, entry.options)?;
    Ok((output, command_output))
}

/// 把反编译得到的源码落到稳定产物路径，便于后续编译、执行和排错。
pub(crate) fn write_generated_case_source(
    entry: &LuaCaseManifestEntry,
    suite_label: &str,
    generated_source: &str,
) -> Result<PathBuf, String> {
    let dialect_label = <&'static str>::from(entry.dialect);
    let output = suite_artifact_path(
        suite_label,
        dialect_label,
        entry.variant,
        "generated-source",
        entry.path,
        "lua",
    );
    write_output_file(&output, generated_source.as_bytes())?;
    Ok(output)
}

/// 执行源码与官方编译产物，得到后续反编译验证可以复用的基线输出。
pub(crate) fn build_case_baseline(
    entry: &case_manifest::LuaCaseManifestEntry,
    suite_label: &str,
) -> Result<CaseBaseline, TestFailure> {
    let dialect_label = <&'static str>::from(entry.dialect);
    let toolchain = lua_toolchain(dialect_label).map_err(|error| {
        TestFailure::new(
            FailureKind::RunSourceFailed,
            "unknown test dialect",
            format!("unknown test dialect {dialect_label}: {error}"),
        )
    })?;
    let source_output = run_lua_case(dialect_label, entry.path).map_err(|error| {
        TestFailure::new(
            FailureKind::RunSourceFailed,
            "run source failed",
            format!("run source failed: {error}"),
        )
    })?;
    if !source_output.success() {
        let reason = primary_command_reason(&source_output)
            .map(|reason| format!(": {reason}"))
            .unwrap_or_default();
        let summary = format!(
            "source execution failed{reason} (status: {})",
            render_status_code(source_output.status_code)
        );
        return Err(TestFailure::new(
            FailureKind::SourceExecutionFailed,
            summary.clone(),
            format!("{summary}\n{}", source_output.render()),
        ));
    }

    let (compiled_path, compile_output) = compile_lua_case_to_suite_artifact(
        entry,
        suite_label,
        "compiled-source",
        !entry.options.retain_debug,
    )
    .map_err(|error| {
        TestFailure::new(
            FailureKind::CompileSourceFailed,
            "compile source failed",
            format!("compile source failed: {error}"),
        )
    })?;
    if !compile_output.success() {
        let reason = primary_command_reason(&compile_output)
            .map(|reason| format!(": {reason}"))
            .unwrap_or_default();
        let summary = format!(
            "source compilation failed{reason} (artifact: {}, status: {})",
            repo_relative_display(&compiled_path),
            render_status_code(compile_output.status_code)
        );
        return Err(TestFailure::new(
            FailureKind::SourceCompilationFailed,
            summary.clone(),
            format!("{summary}\n{}", compile_output.render()),
        ));
    }

    if !toolchain.can_run_compiled_chunks {
        return Ok(CaseBaseline { source_output });
    }

    let chunk_output = run_lua_file(dialect_label, &compiled_path).map_err(|error| {
        TestFailure::new(
            FailureKind::RunCompiledChunkFailed,
            "run compiled chunk failed",
            format!("run compiled chunk failed: {error}"),
        )
    })?;
    if !chunk_output.success() {
        let reason = primary_command_reason(&chunk_output)
            .map(|reason| format!(": {reason}"))
            .unwrap_or_default();
        let summary = format!(
            "compiled chunk execution failed{reason} (artifact: {}, status: {})",
            repo_relative_display(&compiled_path),
            render_status_code(chunk_output.status_code)
        );
        return Err(TestFailure::new(
            FailureKind::CompiledChunkExecutionFailed,
            summary.clone(),
            format!("{summary}\n{}", chunk_output.render()),
        ));
    }

    if let Some(diff) =
        diff_command_outputs("source", &source_output, "compiled-chunk", &chunk_output)
    {
        let summary = format!(
            "source/chunk output mismatch (artifact: {})",
            repo_relative_display(&compiled_path),
        );
        return Err(TestFailure::new(
            FailureKind::SourceChunkOutputMismatch,
            summary.clone(),
            format!("{summary}\n{diff}"),
        ));
    }

    Ok(CaseBaseline { source_output })
}

pub(crate) fn run_pipeline_case(
    suite: UnitSuite,
    entry: &LuaCaseManifestEntry,
) -> Result<TestSuccess, TestFailure> {
    if entry.expectation == LuaCaseExpectation::TableSetListResidual {
        return run_table_set_list_residual_contract(suite, entry);
    }
    if let LuaCaseExpectation::UnsupportedIsland { jump_pc, target_pc } = entry.expectation {
        return run_unsupported_island_contract(entry, jump_pc, target_pc);
    }
    let dialect_label = <&'static str>::from(entry.dialect);
    let suite_label = suite.label();
    let toolchain = lua_toolchain(dialect_label).map_err(|error| {
        TestFailure::new(
            FailureKind::RunGeneratedChunkFailed,
            "unknown test dialect",
            format!("unknown test dialect {dialect_label}: {error}"),
        )
    })?;
    let assertions = read_readability_assertions(entry.path)?;
    let baseline = build_case_baseline(entry, suite_label).map_err(|failure| {
        TestFailure::new(
            FailureKind::BaselineFailed,
            format!("baseline failed first: {}", failure.summary()),
            format!("baseline failed first\n{}", failure.detail()),
        )
    })?;
    let expected_dialect = entry.dialect.decompile_dialect();

    let chunk = compile_manifest_case(entry);
    let result = decompile(&chunk, decompile_options(entry)).map_err(|error| {
        TestFailure::new(
            FailureKind::DecompileFailed,
            format!("decompile failed: {error}"),
            format!("decompile failed: {error}"),
        )
    })?;
    assert_auto_dialect(
        "generated",
        result.state.dialect,
        expected_dialect,
        entry.path,
    )?;
    assert_structure_contracts(entry, result.state.structure_facts.as_ref())?;

    let generated = result.state.generated.as_ref().ok_or_else(|| {
        TestFailure::new(
            FailureKind::GenerateWithoutSource,
            "generate stage finished without source",
            format!("generate stage finished without source for {}", entry.path),
        )
    })?;
    assert_source_chunk("generated", generated.kind, entry.path)?;
    assert_readability("generated", &generated.source, &assertions, true)?;
    let generated_source_path = write_generated_case_source(entry, suite_label, &generated.source)
        .map_err(|error| {
            TestFailure::new(
                FailureKind::WriteGeneratedSourceFailed,
                "write generated source failed",
                format!("write generated source failed: {error}"),
            )
        })?;

    let (generated_chunk_path, compile_output) = compile_generated_source_to_suite_artifact(
        entry,
        suite_label,
        &generated_source_path,
        !entry.options.retain_debug,
    )
    .map_err(|error| {
        TestFailure::new(
            FailureKind::CompileGeneratedSourceFailed,
            "compile generated source failed",
            format!("compile generated source failed: {error}"),
        )
    })?;
    if !compile_output.success() {
        let reason = primary_command_reason(&compile_output)
            .map(|reason| format!(": {reason}"))
            .unwrap_or_default();
        let summary = format!(
            "generated source compilation failed{reason} (status: {})",
            compile_output.status_code.unwrap_or_default(),
        );
        return Err(TestFailure::new(
            FailureKind::GeneratedSourceCompilationFailed,
            summary.clone(),
            format!(
                "{summary}\nsource artifact: {}\nchunk artifact: {}\n{}\ngenerated source:\n{}",
                repo_relative_display(&generated_source_path),
                repo_relative_display(&generated_chunk_path),
                compile_output.render(),
                generated.source
            ),
        ));
    }

    let generated_runtime_path = if toolchain.can_run_compiled_chunks {
        &generated_chunk_path
    } else {
        &generated_source_path
    };
    let generated_output =
        run_lua_file(dialect_label, generated_runtime_path).map_err(|error| {
            TestFailure::new(
                FailureKind::RunGeneratedChunkFailed,
                "run generated artifact failed",
                format!("run generated artifact failed: {error}"),
            )
        })?;
    if !generated_output.success() {
        let reason = primary_command_reason(&generated_output)
            .map(|reason| format!(": {reason}"))
            .unwrap_or_default();
        let summary = format!(
            "generated artifact execution failed{reason} (runtime artifact: {}, status: {})",
            repo_relative_display(generated_runtime_path),
            generated_output.status_code.unwrap_or_default(),
        );
        return Err(TestFailure::new(
            FailureKind::GeneratedChunkExecutionFailed,
            summary.clone(),
            format!(
                "{summary}\nsource artifact: {}\nchunk artifact: {}\nruntime artifact: {}\n{}\ngenerated source:\n{}",
                repo_relative_display(&generated_source_path),
                repo_relative_display(&generated_chunk_path),
                repo_relative_display(generated_runtime_path),
                generated_output.render(),
                generated.source
            ),
        ));
    }

    if let Some(diff) = diff_command_outputs(
        "expected-source",
        &baseline.source_output,
        "generated-artifact",
        &generated_output,
    ) {
        let proto_count = count_output_tags(&baseline.source_output.stdout);
        let failed_tags =
            diff_output_tags(&baseline.source_output.stdout, &generated_output.stdout);
        let summary = format!(
            "generated output mismatch (runtime artifact: {})",
            repo_relative_display(generated_runtime_path),
        );
        return Err(TestFailure::new(
            FailureKind::GeneratedOutputMismatch,
            summary.clone(),
            format!(
                "{summary}\nsource artifact: {}\nchunk artifact: {}\nruntime artifact: {}\n{diff}\ngenerated source:\n{}",
                repo_relative_display(&generated_source_path),
                repo_relative_display(&generated_chunk_path),
                repo_relative_display(generated_runtime_path),
                generated.source
            ),
        ).with_proto_stats(proto_count, failed_tags));
    }

    // 重编译轮次：拿上一轮生成的源码，再走一遍 compile → decompile → compile → run → 对比 baseline，
    // 同时做前后两轮生成源码的文本收敛检查。
    let rounds = entry
        .options
        .recompile_rounds
        .unwrap_or_else(recompile_rounds);
    let require_convergence = entry
        .options
        .recompile_rounds
        .is_some_and(|rounds| rounds > 0);
    let mut prev_generated_source = generated.source.clone();
    for round in 1..=rounds {
        let round_label = format!("recompile-round-{round}");

        // 把上一轮生成的源码编译成 chunk
        let prev_source_path = write_generated_case_source(
            entry,
            &format!("{suite_label}/{round_label}"),
            &prev_generated_source,
        )
        .map_err(|error| {
            TestFailure::new(
                FailureKind::WriteGeneratedSourceFailed,
                format!("[{round_label}] write generated source failed"),
                format!("[{round_label}] write generated source failed: {error}"),
            )
        })?;
        let (prev_chunk_path, prev_compile_output) = compile_generated_source_to_suite_artifact(
            entry,
            &format!("{suite_label}/{round_label}"),
            &prev_source_path,
            !entry.options.retain_debug,
        )
        .map_err(|error| {
            TestFailure::new(
                FailureKind::RecompileGeneratedSourceCompilationFailed,
                format!("[{round_label}] compile generated source failed"),
                format!("[{round_label}] compile generated source failed: {error}"),
            )
        })?;
        if !prev_compile_output.success() {
            let reason = primary_command_reason(&prev_compile_output)
                .map(|reason| format!(": {reason}"))
                .unwrap_or_default();
            let summary = format!(
                "[{round_label}] generated source compilation failed{reason} (status: {})",
                prev_compile_output.status_code.unwrap_or_default(),
            );
            return Err(TestFailure::new(
                FailureKind::RecompileGeneratedSourceCompilationFailed,
                summary.clone(),
                format!(
                    "{summary}\nsource artifact: {}\nchunk artifact: {}\n{}\ngenerated source:\n{}",
                    repo_relative_display(&prev_source_path),
                    repo_relative_display(&prev_chunk_path),
                    prev_compile_output.render(),
                    prev_generated_source,
                ),
            ));
        }

        // 反编译 chunk
        let prev_chunk_bytes = fs::read(&prev_chunk_path).map_err(|error| {
            TestFailure::new(
                FailureKind::RecompileDecompileFailed,
                format!("[{round_label}] read recompiled chunk failed"),
                format!(
                    "[{round_label}] read recompiled chunk {}: {error}",
                    repo_relative_display(&prev_chunk_path)
                ),
            )
        })?;
        let recompile_result =
            decompile(&prev_chunk_bytes, decompile_options(entry)).map_err(|error| {
                TestFailure::new(
                    FailureKind::RecompileDecompileFailed,
                    format!("[{round_label}] decompile failed: {error}"),
                    format!("[{round_label}] decompile failed: {error}"),
                )
            })?;
        assert_auto_dialect(
            &round_label,
            recompile_result.state.dialect,
            expected_dialect,
            entry.path,
        )?;
        let recompile_generated = recompile_result.state.generated.as_ref().ok_or_else(|| {
            TestFailure::new(
                FailureKind::RecompileDecompileFailed,
                format!("[{round_label}] generate stage finished without source"),
                format!(
                    "[{round_label}] generate stage finished without source for {}",
                    entry.path
                ),
            )
        })?;
        assert_source_chunk(&round_label, recompile_generated.kind, entry.path)?;
        // 正向 shape 只约束原始 bytecode 的首次恢复；目标编译器可能把合法的
        // `break`/`while true` 等价规范化成 `return`/`repeat`。安全型负向约束仍需
        // 在每个 roundtrip 重验，防止 goto、unresolved 或诊断源码回流。
        assert_readability(
            &round_label,
            &recompile_generated.source,
            &assertions,
            false,
        )?;

        // 写出、编译、执行再次生成的源码
        let regen_source_path = write_generated_case_source(
            entry,
            &format!("{suite_label}/{round_label}-regen"),
            &recompile_generated.source,
        )
        .map_err(|error| {
            TestFailure::new(
                FailureKind::WriteGeneratedSourceFailed,
                format!("[{round_label}] write regen source failed"),
                format!("[{round_label}] write regen source failed: {error}"),
            )
        })?;
        let (regen_chunk_path, regen_compile_output) = compile_generated_source_to_suite_artifact(
            entry,
            &format!("{suite_label}/{round_label}-regen"),
            &regen_source_path,
            !entry.options.retain_debug,
        )
        .map_err(|error| {
            TestFailure::new(
                FailureKind::RecompileGeneratedSourceCompilationFailed,
                format!("[{round_label}] compile regen source failed"),
                format!("[{round_label}] compile regen source failed: {error}"),
            )
        })?;
        if !regen_compile_output.success() {
            let reason = primary_command_reason(&regen_compile_output)
                .map(|reason| format!(": {reason}"))
                .unwrap_or_default();
            let summary = format!(
                "[{round_label}] regen source compilation failed{reason} (status: {})",
                regen_compile_output.status_code.unwrap_or_default(),
            );
            return Err(TestFailure::new(
                FailureKind::RecompileGeneratedSourceCompilationFailed,
                summary.clone(),
                format!(
                    "{summary}\nsource artifact: {}\nchunk artifact: {}\n{}\ngenerated source:\n{}",
                    repo_relative_display(&regen_source_path),
                    repo_relative_display(&regen_chunk_path),
                    regen_compile_output.render(),
                    recompile_generated.source,
                ),
            ));
        }

        let regen_runtime_path = if toolchain.can_run_compiled_chunks {
            &regen_chunk_path
        } else {
            &regen_source_path
        };
        let regen_output = run_lua_file(dialect_label, regen_runtime_path).map_err(|error| {
            TestFailure::new(
                FailureKind::RecompileGeneratedChunkExecutionFailed,
                format!("[{round_label}] run regen artifact failed"),
                format!("[{round_label}] run regen artifact failed: {error}"),
            )
        })?;
        if !regen_output.success() {
            let reason = primary_command_reason(&regen_output)
                .map(|reason| format!(": {reason}"))
                .unwrap_or_default();
            let summary = format!(
                "[{round_label}] regen artifact execution failed{reason} (status: {})",
                regen_output.status_code.unwrap_or_default(),
            );
            return Err(TestFailure::new(
                FailureKind::RecompileGeneratedChunkExecutionFailed,
                summary.clone(),
                format!(
                    "{summary}\nruntime artifact: {}\n{}\ngenerated source:\n{}",
                    repo_relative_display(regen_runtime_path),
                    regen_output.render(),
                    recompile_generated.source,
                ),
            ));
        }

        // 语义检查：执行输出应与 baseline 一致
        if let Some(diff) = diff_command_outputs(
            "expected-source",
            &baseline.source_output,
            &format!("{round_label}-regen"),
            &regen_output,
        ) {
            let proto_count = count_output_tags(&baseline.source_output.stdout);
            let failed_tags =
                diff_output_tags(&baseline.source_output.stdout, &regen_output.stdout);
            let summary = format!(
                "[{round_label}] regen output mismatch (runtime artifact: {})",
                repo_relative_display(regen_runtime_path),
            );
            return Err(TestFailure::new(
                FailureKind::RecompileGeneratedOutputMismatch,
                summary.clone(),
                format!(
                    "{summary}\n{diff}\ngenerated source:\n{}",
                    recompile_generated.source,
                ),
            )
            .with_proto_stats(proto_count, failed_tags));
        }

        if prev_generated_source == recompile_generated.source {
            if require_convergence {
                break;
            }
        } else if require_convergence && round == rounds {
            let summary = format!("[{round_label}] generated source did not converge");
            return Err(TestFailure::new(
                FailureKind::RecompileConvergenceMismatch,
                summary.clone(),
                format!(
                    "{summary}\nprevious source:\n{}\ncurrent source:\n{}",
                    prev_generated_source, recompile_generated.source,
                ),
            ));
        }

        prev_generated_source = recompile_generated.source.clone();
    }

    match entry.expectation {
        LuaCaseExpectation::InvalidDebugStillRejected => {
            assert_ignore_debug_keeps_parser_validation(entry)?;
        }
        LuaCaseExpectation::LuaJitBuiltinTableRemove => {
            assert_luajit_table_remove_contract(entry, suite_label)?;
        }
        LuaCaseExpectation::LuaJitMethodProtocol => {
            assert_luajit_method_protocol_contract(entry, suite_label)?;
        }
        LuaCaseExpectation::Source
        | LuaCaseExpectation::TableSetListResidual
        | LuaCaseExpectation::UnsupportedIsland { .. } => {}
    }

    let proto_count = count_output_tags(&baseline.source_output.stdout);
    Ok(TestSuccess { proto_count })
}

fn run_table_set_list_residual_contract(
    suite: UnitSuite,
    entry: &LuaCaseManifestEntry,
) -> Result<TestSuccess, TestFailure> {
    let baseline = build_case_baseline(entry, suite.label()).map_err(|failure| {
        TestFailure::new(
            FailureKind::BaselineFailed,
            format!("baseline failed first: {}", failure.summary()),
            format!("baseline failed first\n{}", failure.detail()),
        )
    })?;
    let chunk = compile_manifest_case(entry);

    let mut strict_options = decompile_options(entry);
    strict_options.generate.mode = GenerateMode::Strict;
    match decompile(&chunk, strict_options) {
        Err(DecompileError::Ast(AstLowerError::ResidualHir {
            kind: "table-set-list",
            ..
        })) => {}
        Err(error) => {
            return Err(table_set_list_residual_contract_failure(
                entry,
                format!("strict mode returned the wrong error: {error}"),
            ));
        }
        Ok(_) => {
            return Err(table_set_list_residual_contract_failure(
                entry,
                "strict mode accepted an unrepresentable table-set-list",
            ));
        }
    }

    let mut permissive_options = decompile_options(entry);
    permissive_options.generate.mode = GenerateMode::Permissive;
    let permissive = decompile(&chunk, permissive_options).map_err(|error| {
        table_set_list_residual_contract_failure(
            entry,
            format!("permissive mode rejected table-set-list: {error}"),
        )
    })?;
    assert_auto_dialect(
        "table-set-list residual",
        permissive.state.dialect,
        entry.dialect.decompile_dialect(),
        entry.path,
    )?;
    let generated = permissive.state.generated.as_ref().ok_or_else(|| {
        table_set_list_residual_contract_failure(
            entry,
            "permissive mode returned no generated chunk",
        )
    })?;
    if generated.kind != GeneratedChunkKind::DiagnosticPseudocode
        || !generated
            .source
            .contains("-- [unluac error] diagnostic pseudocode:")
        || !generated.source.contains("residual table-set-list")
    {
        return Err(table_set_list_residual_contract_failure(
            entry,
            format!(
                "permissive mode did not preserve the table-set-list diagnostic: kind={:?}\n{}",
                generated.kind, generated.source
            ),
        ));
    }

    Ok(TestSuccess {
        proto_count: count_output_tags(&baseline.source_output.stdout),
    })
}

fn table_set_list_residual_contract_failure(
    entry: &LuaCaseManifestEntry,
    detail: impl Into<String>,
) -> TestFailure {
    TestFailure::new(
        FailureKind::ResidualContractAssertionFailed,
        "table-set-list residual contract failed",
        format!(
            "table-set-list residual contract failed for {}: {}",
            entry.path,
            detail.into()
        ),
    )
}
