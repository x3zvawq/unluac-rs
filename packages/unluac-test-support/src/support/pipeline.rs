//! 编排源码执行、编译、反编译、回编译与收敛检查；依赖 toolchain 和专题断言，不负责解析 case 清单；例如对主题源码执行完整往返验证。
//!
//! 每份生成源码在本轮完成编译与运行验证后，把同一 chunk 交给下一轮反编译。
//! 编译选项在 case 内固定；不为改变轮次路径重复编译已验证源码，新生成结果仍完整验证。

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

/// 执行实际编译产物；Luau CLI 只读源码，不能用重新编译源码代替原优化档的 chunk。
fn run_compiled_lua_file(
    dialect_label: &str,
    input_path: &Path,
    observer: Option<&runtime_observer::RuntimeObserver>,
) -> Result<LuaCommandOutput, String> {
    let toolchain = lua_toolchain(dialect_label)?;
    let runtime = lua_tool_path(dialect_label, toolchain.compiled_runtime_name)?;
    let output = run_command(
        &runtime,
        [input_path.as_os_str()],
        toolchain.compiled_runtime_name,
    )?;
    if output.success()
        && let Some(observer) = observer
    {
        observer.check_chunk(input_path)?;
    }
    Ok(output)
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
        entry,
        artifact_label,
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
    let output = suite_artifact_path(suite_label, entry, "generated-source", "lua");
    write_output_file(&output, generated_source.as_bytes())?;
    Ok(output)
}

/// 执行源码与官方编译产物，得到后续反编译验证可以复用的基线输出。
pub(crate) fn build_case_baseline(
    entry: &case_manifest::LuaCaseManifestEntry,
    suite_label: &str,
) -> Result<CaseBaseline, TestFailure> {
    let dialect_label = <&'static str>::from(entry.dialect);
    let source_output = (if dialect_label == "luau" {
        let optimization = format!("-O{}", entry.options.luau_optimization_level.unwrap_or(1));
        run_lua_file_with_args(
            dialect_label,
            &repo_root().join(entry.path),
            &[&optimization],
        )
    } else {
        run_lua_case(dialect_label, entry.path)
    })
    .map_err(|error| {
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

    let runtime_observer =
        runtime_observer::RuntimeObserver::prepare(entry, suite_label).map_err(|error| {
            TestFailure::new(
                FailureKind::RunSourceFailed,
                "prepare runtime observer failed",
                error,
            )
        })?;
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

    let chunk_output =
        run_compiled_lua_file(dialect_label, &compiled_path, runtime_observer.as_ref()).map_err(
            |error| {
                TestFailure::new(
                    FailureKind::RunCompiledChunkFailed,
                    "run compiled chunk failed",
                    format!("run compiled chunk failed: {error}"),
                )
            },
        )?;
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

    // 初次反编译消费实际运行过的同一 chunk，避免按相同选项再次调用编译器。
    let compiled_chunk = fs::read(&compiled_path).map_err(|error| {
        TestFailure::new(
            FailureKind::CompileSourceFailed,
            "read compiled baseline failed",
            format!(
                "read {} failed: {error}",
                repo_relative_display(&compiled_path)
            ),
        )
    })?;
    Ok(CaseBaseline {
        source_output,
        compiled_chunk,
        runtime_observer,
    })
}

pub(crate) fn run_pipeline_case(entry: &LuaCaseManifestEntry) -> Result<TestSuccess, TestFailure> {
    if entry.expectation == LuaCaseExpectation::GlobalDeclResidual {
        return run_global_decl_residual_contract(entry);
    }
    if let LuaCaseExpectation::UnsupportedIsland { jump_pc, target_pc } = entry.expectation {
        return run_unsupported_island_contract(entry, jump_pc, target_pc);
    }
    if entry.expectation == LuaCaseExpectation::ProtoFailureRecovery {
        return run_proto_failure_recovery_contract(entry);
    }
    let dialect_label = <&'static str>::from(entry.dialect);
    let suite_label = "cases";
    let toolchain = lua_toolchain(dialect_label).map_err(|error| {
        TestFailure::new(
            FailureKind::RunGeneratedChunkFailed,
            "unknown test dialect",
            format!("unknown test dialect {dialect_label}: {error}"),
        )
    })?;
    let assertions = read_readability_assertions(entry.path)?;
    let mut baseline = build_case_baseline(entry, suite_label).map_err(|failure| {
        TestFailure::new(
            FailureKind::BaselineFailed,
            format!("baseline failed first: {}", failure.summary()),
            format!("baseline failed first\n{}", failure.detail()),
        )
    })?;
    let expected_dialect = entry.dialect.decompile_dialect();

    let mut chunk = baseline.compiled_chunk;
    if let LuaCaseExpectation::LuauSelfValueCaptureCarrier {
        closure_pc,
        save_pc,
        overwrite_pc,
        target_reg,
    } = entry.expectation
    {
        patch_luau_self_value_capture_carrier(
            &mut chunk,
            closure_pc,
            save_pc,
            overwrite_pc,
            target_reg,
        )
        .map_err(|detail| {
            TestFailure::new(
                FailureKind::CompileSourceFailed,
                "patch Luau self-value carrier failed",
                detail,
            )
        })?;
        let carrier_path = suite_artifact_path(
            suite_label,
            entry,
            "patched-self-value-carrier",
            toolchain.chunk_extension,
        );
        write_output_file(&carrier_path, &chunk).map_err(|detail| {
            TestFailure::new(
                FailureKind::CompileSourceFailed,
                "write patched Luau self-value carrier failed",
                detail,
            )
        })?;
        let runner = lua_tool_path("luau", "luau-bytecode-runner").map_err(|detail| {
            TestFailure::new(
                FailureKind::RunCompiledChunkFailed,
                "locate Luau bytecode runner failed",
                detail,
            )
        })?;
        let carrier_output =
            run_command(&runner, [carrier_path.as_os_str()], "luau-bytecode-runner").map_err(
                |detail| {
                    TestFailure::new(
                        FailureKind::RunCompiledChunkFailed,
                        "run patched Luau self-value carrier failed",
                        detail,
                    )
                },
            )?;
        if !carrier_output.success() {
            let summary = format!(
                "patched Luau self-value carrier execution failed (artifact: {}, status: {})",
                repo_relative_display(&carrier_path),
                render_status_code(carrier_output.status_code),
            );
            return Err(TestFailure::new(
                FailureKind::CompiledChunkExecutionFailed,
                summary.clone(),
                format!("{summary}\n{}", carrier_output.render()),
            ));
        }
        if let Some(diff) = diff_command_outputs(
            "source",
            &baseline.source_output,
            "patched-chunk",
            &carrier_output,
        ) {
            let summary = format!(
                "source/patched Luau carrier output mismatch (artifact: {})",
                repo_relative_display(&carrier_path),
            );
            return Err(TestFailure::new(
                FailureKind::SourceChunkOutputMismatch,
                summary.clone(),
                format!("{summary}\n{diff}"),
            ));
        }
        baseline.source_output = carrier_output;
    }
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
    assert_instruction_contracts(
        "original",
        result
            .state
            .lowered
            .as_ref()
            .expect("Generate includes Transformer"),
        entry,
        &assertions,
    )?;

    let generated = result.state.generated.as_ref().ok_or_else(|| {
        TestFailure::new(
            FailureKind::GenerateWithoutSource,
            "generate stage finished without source",
            format!("generate stage finished without source for {}", entry.path),
        )
    })?;
    assert_source_chunk("generated", generated.kind, entry.path)?;
    // 形状合同失败也需要保留实际输出，才能按批次审查断言与证明缺口。
    let generated_source_path = write_generated_case_source(entry, suite_label, &generated.source)
        .map_err(|error| {
            TestFailure::new(
                FailureKind::WriteGeneratedSourceFailed,
                "write generated source failed",
                format!("write generated source failed: {error}"),
            )
        })?;
    assert_readability(
        "generated",
        &generated.source,
        result.state.readability.as_ref(),
        result.state.naming.as_ref(),
        entry,
        &assertions,
        true,
    )?;

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

    assert_compiled_instruction_contracts("generated", &generated_chunk_path, entry, &assertions)?;
    let generated_runtime_path = &generated_chunk_path;
    let generated_output = run_compiled_lua_file(
        dialect_label,
        generated_runtime_path,
        baseline.runtime_observer.as_ref(),
    )
    .map_err(|error| {
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

    // 上一轮源码已经编译并通过运行比较；直接消费同一 chunk，再生成后仍须 compile → run。
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
    let mut prev_chunk_path = generated_chunk_path;
    for round in 1..=rounds {
        let round_label = format!("recompile-round-{round}");

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
        // 先保留本轮输出，包括随后被安全型形状合同拒绝的源码。
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
        // 正向 shape 只约束原始 bytecode 的首次恢复；目标编译器可能把合法的
        // `break`/`while true` 等价规范化成 `return`/`repeat`。安全型负向约束仍需
        // 在每个 roundtrip 重验，防止 goto、unresolved 或诊断源码回流。
        assert_readability(
            &round_label,
            &recompile_generated.source,
            recompile_result.state.readability.as_ref(),
            recompile_result.state.naming.as_ref(),
            entry,
            &assertions,
            false,
        )?;
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

        assert_compiled_instruction_contracts(&round_label, &regen_chunk_path, entry, &assertions)?;
        let regen_runtime_path = &regen_chunk_path;
        let regen_output = run_compiled_lua_file(
            dialect_label,
            regen_runtime_path,
            baseline.runtime_observer.as_ref(),
        )
        .map_err(|error| {
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
        prev_chunk_path = regen_chunk_path;
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
        LuaCaseExpectation::ProtoFailureRecovery => {
            return Err(proto_failure_contract_failure(
                entry,
                "proto failure contract unexpectedly entered the normal pipeline",
            ));
        }
        LuaCaseExpectation::Source
        | LuaCaseExpectation::GlobalDeclResidual
        | LuaCaseExpectation::LuauSelfValueCaptureCarrier { .. }
        | LuaCaseExpectation::UnsupportedIsland { .. } => {}
    }

    let proto_count = count_output_tags(&baseline.source_output.stdout);
    Ok(TestSuccess { proto_count })
}

fn run_global_decl_residual_contract(
    entry: &LuaCaseManifestEntry,
) -> Result<TestSuccess, TestFailure> {
    let baseline = build_case_baseline(entry, "cases").map_err(|failure| {
        TestFailure::new(
            FailureKind::BaselineFailed,
            format!("baseline failed first: {}", failure.summary()),
            format!("baseline failed first\n{}", failure.detail()),
        )
    })?;
    let chunk = baseline.compiled_chunk;

    let mut hir_options = decompile_options(entry);
    hir_options.target_stage = DecompileStage::Hir;
    hir_options.generate.mode = GenerateMode::Permissive;
    let hir_result = decompile(&chunk, hir_options).map_err(|error| {
        global_decl_residual_contract_failure(entry, format!("HIR lowering failed: {error}"))
    })?;
    let module = hir_result.state.hir.ok_or_else(|| {
        global_decl_residual_contract_failure(entry, "HIR lowering returned no module")
    })?;
    let root = module.protos.get(module.entry.index()).ok_or_else(|| {
        global_decl_residual_contract_failure(entry, "HIR entry references a missing proto")
    })?;
    if hir_block_contains_global_decl(&root.body) {
        return Err(global_decl_residual_contract_failure(
            entry,
            "mixed RHS was partially claimed as a global declaration",
        ));
    }

    let mut strict_options = decompile_options(entry);
    strict_options.generate.mode = GenerateMode::Strict;
    match decompile(&chunk, strict_options) {
        Err(DecompileError::Ast(AstLowerError::InvalidGlobalDeclPattern { proto: 0 })) => {}
        Err(error) => {
            return Err(global_decl_residual_contract_failure(
                entry,
                format!("strict mode returned the wrong error: {error}"),
            ));
        }
        Ok(_) => {
            return Err(global_decl_residual_contract_failure(
                entry,
                "strict mode accepted a partially recoverable global declaration",
            ));
        }
    }

    let mut permissive_options = decompile_options(entry);
    permissive_options.generate.mode = GenerateMode::Permissive;
    let permissive = decompile(&chunk, permissive_options).map_err(|error| {
        global_decl_residual_contract_failure(
            entry,
            format!("permissive mode rejected mixed global declaration: {error}"),
        )
    })?;
    let generated = permissive.state.generated.as_ref().ok_or_else(|| {
        global_decl_residual_contract_failure(entry, "permissive mode returned no generated chunk")
    })?;
    if generated.kind != GeneratedChunkKind::DiagnosticPseudocode
        || !generated.source.contains("err-nnil")
    {
        return Err(global_decl_residual_contract_failure(
            entry,
            format!(
                "permissive mode lost the global declaration diagnostic: kind={:?}\n{}",
                generated.kind, generated.source
            ),
        ));
    }
    let assertions = read_readability_assertions(entry.path)?;
    assert_readability(
        "permissive",
        &generated.source,
        permissive.state.readability.as_ref(),
        permissive.state.naming.as_ref(),
        entry,
        &assertions,
        true,
    )?;

    Ok(TestSuccess {
        proto_count: count_output_tags(&baseline.source_output.stdout),
    })
}

fn hir_block_contains_global_decl(block: &unluac::hir::HirBlock) -> bool {
    use unluac::hir::HirStmt;

    block.stmts.iter().any(|stmt| match stmt {
        HirStmt::GlobalDecl(_) => true,
        HirStmt::If(if_stmt) => {
            hir_block_contains_global_decl(&if_stmt.then_block)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(hir_block_contains_global_decl)
        }
        HirStmt::While(while_stmt) => hir_block_contains_global_decl(&while_stmt.body),
        HirStmt::Repeat(repeat_stmt) => hir_block_contains_global_decl(&repeat_stmt.body),
        HirStmt::NumericFor(for_stmt) => hir_block_contains_global_decl(&for_stmt.body),
        HirStmt::GenericFor(for_stmt) => hir_block_contains_global_decl(&for_stmt.body),
        HirStmt::Block(block) => hir_block_contains_global_decl(block),
        HirStmt::LocalDecl(_)
        | HirStmt::LocalRootRelease(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    })
}

fn global_decl_residual_contract_failure(
    entry: &LuaCaseManifestEntry,
    detail: impl Into<String>,
) -> TestFailure {
    TestFailure::new(
        FailureKind::ResidualContractAssertionFailed,
        "global declaration residual contract failed",
        format!(
            "global declaration residual contract failed for {}: {}",
            entry.path,
            detail.into()
        ),
    )
}

fn run_proto_failure_recovery_contract(
    entry: &LuaCaseManifestEntry,
) -> Result<TestSuccess, TestFailure> {
    use unluac::ast::{AstExpr, AstStmt, AstTargetDialect, lower_ast};
    use unluac::hir::{HirBlock, LocalId};
    use unluac::recovery::{ProtoArtifactStage, ProtoFailure};

    let source_entry = LuaCaseManifestEntry {
        expectation: LuaCaseExpectation::Source,
        ..*entry
    };
    let baseline = run_pipeline_case(&source_entry)?;
    let chunk = compile_manifest_case(entry);
    let mut options = decompile_options(entry);
    options.target_stage = DecompileStage::Hir;
    options.generate.mode = GenerateMode::Permissive;
    let result = decompile(&chunk, options).map_err(|error| {
        proto_failure_contract_failure(entry, format!("HIR baseline failed: {error}"))
    })?;
    let mut module = result
        .state
        .hir
        .ok_or_else(|| proto_failure_contract_failure(entry, "HIR baseline returned no module"))?;
    verify_proto_body_preparation_contract(entry, &module)?;
    let entry_ref = module.entry;
    let root = module.protos.get_mut(entry_ref.index()).ok_or_else(|| {
        proto_failure_contract_failure(entry, "HIR entry references a missing proto")
    })?;
    let children = root.children.clone();
    if children.len() < 2 {
        return Err(proto_failure_contract_failure(
            entry,
            format!(
                "fixture must produce at least two direct child protos, got {}",
                children.len()
            ),
        ));
    }
    let first_recovery_local = root.local_count;
    root.detached_children = children
        .iter()
        .enumerate()
        .map(|(index, child)| (LocalId(first_recovery_local + index), *child))
        .collect();
    root.local_count += root.detached_children.len();
    for (local, _) in &root.detached_children {
        root.local_debug_hints
            .push(Some(format!("unluac_proto_{}", local.index())));
    }
    root.body = HirBlock::default();
    root.failure = Some(ProtoFailure {
        proto: 0,
        failed_stage: ProtoArtifactStage::Structure,
        last_completed_stage: ProtoArtifactStage::Dataflow,
        error: "forced recovery contract".into(),
        last_completed_dump: "dataflow proto#0\n  @000 return".into(),
    });

    let target = AstTargetDialect::new(entry.dialect.decompile_dialect());
    match lower_ast(&module, target, GenerateMode::Strict) {
        Err(AstLowerError::ResidualHir {
            proto: 0,
            kind: "proto recovery failure",
        }) => {}
        Err(error) => {
            return Err(proto_failure_contract_failure(
                entry,
                format!("strict mode returned the wrong error: {error}"),
            ));
        }
        Ok(_) => {
            return Err(proto_failure_contract_failure(
                entry,
                "strict mode accepted a failed proto",
            ));
        }
    }

    let ast = lower_ast(&module, target, GenerateMode::Permissive).map_err(|error| {
        proto_failure_contract_failure(entry, format!("permissive lowering failed: {error}"))
    })?;
    let expected_stmt_count = children.len() + 2;
    if ast.body.stmts.len() != expected_stmt_count {
        return Err(proto_failure_contract_failure(
            entry,
            format!(
                "permissive root has {} statements, expected {expected_stmt_count}",
                ast.body.stmts.len()
            ),
        ));
    }
    let Some(AstStmt::Error(failure)) = ast.body.stmts.first() else {
        return Err(proto_failure_contract_failure(
            entry,
            "permissive root does not start with a failure diagnostic",
        ));
    };
    if !failure.contains("proto#0 failed during structure")
        || !failure.contains("last completed stage: dataflow")
        || !failure.contains("\n  @000 return")
    {
        return Err(proto_failure_contract_failure(
            entry,
            format!("failure diagnostic lost stage or dump details: {failure}"),
        ));
    }
    if !matches!(
        ast.body.stmts.get(1),
        Some(AstStmt::Error(message)) if message.contains("detached diagnostic functions")
    ) {
        return Err(proto_failure_contract_failure(
            entry,
            "permissive root does not explain detached child placement",
        ));
    }
    if !ast.body.stmts[2..].iter().all(|stmt| {
        matches!(
            stmt,
            AstStmt::LocalDecl(decl)
                if matches!(decl.values.as_slice(), [AstExpr::FunctionExpr(_)])
        )
    }) {
        return Err(proto_failure_contract_failure(
            entry,
            "permissive root did not preserve every child as a diagnostic function",
        ));
    }

    Ok(baseline)
}

/// 从同一官方源码的 HIR 检查准备阶段与 occurrence 消费阶段的边界；错误不得因预分析而提前。
fn verify_proto_body_preparation_contract(
    entry: &LuaCaseManifestEntry,
    original: &unluac::hir::HirModule,
) -> Result<(), TestFailure> {
    use unluac::ast::{AstExpr, AstStmt, AstTargetDialect, lower_ast};
    use unluac::hir::{
        HirBlock, HirClosureExpr, HirExitRequirement, HirExpr, HirProtoRef, HirReturn, HirStmt,
        HirTableSetList, HirValuePack,
    };

    let fail = |detail: String| proto_failure_contract_failure(entry, detail);
    let target = AstTargetDialect::new(entry.dialect.decompile_dialect());
    let expect_error = |module: &unluac::hir::HirModule, expected: AstLowerError| match lower_ast(
        module,
        target,
        GenerateMode::Strict,
    ) {
        Err(actual)
            if std::mem::discriminant(&actual) == std::mem::discriminant(&expected)
                && actual.to_string() == expected.to_string() =>
        {
            Ok(())
        }
        actual => Err(fail(format!(
            "body preparation expected {expected:?}, got {actual:?}"
        ))),
    };
    let root = original.entry.index();
    let child = original
        .protos
        .get(root)
        .and_then(|proto| proto.children.first())
        .copied()
        .ok_or_else(|| fail("body preparation fixture needs a direct child".into()))?;
    let missing = HirProtoRef(original.protos.len());
    let closure = |proto| HirExpr::Closure(Box::new(HirClosureExpr::synthetic(proto, Vec::new())));
    let return_values =
        |values| HirStmt::Return(Box::new(HirReturn::synthetic(HirValuePack::fixed(values))));
    let residual = || {
        HirStmt::TableSetList(Box::new(HirTableSetList::synthetic(
            HirExpr::Nil,
            1,
            HirValuePack::fixed(Vec::new()),
        )))
    };
    let residual_error = |proto| AstLowerError::ResidualHir {
        proto,
        kind: "table-set-list",
    };

    let mut module = original.clone();
    module.protos[root].body.stmts = vec![residual(), return_values(vec![closure(missing)])];
    expect_error(&module, residual_error(root))?;
    module.protos[root].body.stmts.remove(0);
    expect_error(
        &module,
        AstLowerError::MissingChildProto {
            proto: root,
            child: missing.index(),
        },
    )?;

    module.protos[root].body.stmts = vec![return_values(vec![closure(child)])];
    let child_proto = &mut module.protos[child.index()];
    child_proto.body.stmts = vec![residual()];
    child_proto.signature.has_vararg_param_reg = true;
    child_proto.signature.legacy_arg_slot = false;
    child_proto.vararg_param_local = None;
    expect_error(&module, residual_error(child.index()))?;
    module.protos[child.index()].body = HirBlock::default();
    expect_error(
        &module,
        AstLowerError::MissingNamedVarargBinding {
            proto: child.index(),
        },
    )?;

    // 不可达 body 的坏节点和缺失入口绑定不发布；全模块 exit requirements 仍必须先行。
    module.protos[root].body.stmts = vec![return_values(vec![HirExpr::Nil])];
    module.protos[child.index()].body.stmts =
        vec![residual(), return_values(vec![closure(missing)])];
    lower_ast(&module, target, GenerateMode::Strict)
        .map_err(|error| fail(format!("unreachable bad body leaked an error: {error}")))?;
    module.protos[child.index()]
        .exit_requirements
        .push(HirExitRequirement::UnresolvedValue {
            source_proto: child.index(),
            phi: 17,
            block: 23,
            register: 5,
        });
    module.protos[root].body.stmts.insert(0, residual());
    expect_error(
        &module,
        AstLowerError::UnresolvedHirValue {
            proto: child.index(),
            phi: 17,
            block: 23,
            register: 5,
        },
    )?;

    // 同一个真实 child 的两次引用必须得到完整、各自拥有的 AST body。
    let mut module = original.clone();
    module.protos[root].body.stmts = vec![return_values(vec![closure(child)])];
    let single = lower_ast(&module, target, GenerateMode::Strict)
        .map_err(|error| fail(format!("single child lowering failed: {error}")))?;
    let [AstStmt::Return(single_return)] = single.body.stmts.as_slice() else {
        return Err(fail(
            "single child fixture did not lower to one return".into(),
        ));
    };
    let [AstExpr::FunctionExpr(expected)] = single_return.values.as_slice() else {
        return Err(fail(
            "single child fixture lost its function expression".into(),
        ));
    };
    if expected.body.stmts.is_empty() {
        return Err(fail(
            "shared child fixture must have a nonempty body".into(),
        ));
    }
    module.protos[root].body.stmts = vec![return_values(vec![closure(child), closure(child)])];
    let mut shared = lower_ast(&module, target, GenerateMode::Strict)
        .map_err(|error| fail(format!("repeated child lowering failed: {error}")))?;
    let [AstStmt::Return(shared_return)] = shared.body.stmts.as_mut_slice() else {
        return Err(fail(
            "repeated child fixture did not lower to one return".into(),
        ));
    };
    let [AstExpr::FunctionExpr(first), AstExpr::FunctionExpr(second)] =
        shared_return.values.as_mut_slice()
    else {
        return Err(fail(
            "repeated child fixture lost a function occurrence".into(),
        ));
    };
    if first.as_ref() != expected.as_ref() || second.as_ref() != expected.as_ref() {
        return Err(fail(
            "repeated child bodies differ from independent lowering".into(),
        ));
    }
    first.body.stmts.clear();
    if second.as_ref() != expected.as_ref() {
        return Err(fail(
            "mutating one child body changed another occurrence".into(),
        ));
    }
    Ok(())
}

fn proto_failure_contract_failure(
    entry: &LuaCaseManifestEntry,
    detail: impl Into<String>,
) -> TestFailure {
    TestFailure::new(
        FailureKind::ResidualContractAssertionFailed,
        "proto failure recovery contract failed",
        format!(
            "proto failure recovery contract failed for {}: {}",
            entry.path,
            detail.into()
        ),
    )
}
