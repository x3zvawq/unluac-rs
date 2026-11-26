//! 校验 LuaJIT 内建与方法调用协议及特殊 island 合同；原始编码边界读取 RawProto，运行协议读取 LoweredProto。
//! 例如大键方法样例先证明原 KGC 池跨过 8bit 边界，再检查归一化调用签名，不把字面量池长度当成 KGC 数量。

use super::*;
use unluac::parser::{RawChunk, RawProto};

pub(super) fn assert_ignore_debug_keeps_parser_validation(
    entry: &LuaCaseManifestEntry,
) -> Result<(), TestFailure> {
    let mut truncated = compile_manifest_case(entry);
    truncated.pop().ok_or_else(|| {
        TestFailure::new(
            FailureKind::DecompileFailed,
            "debug validation contract produced an empty chunk",
            "debug validation contract produced an empty chunk",
        )
    })?;

    for ignore_debug in [false, true] {
        let mut options = decompile_options(entry);
        options.parse.mode = ParseMode::Strict;
        options.parse.ignore_debug = ignore_debug;
        match decompile(&truncated, options) {
            Err(DecompileError::Parse(_)) => {}
            Err(error) => {
                return Err(TestFailure::new(
                    FailureKind::DecompileFailed,
                    "truncated debug layout escaped the parser error boundary",
                    format!("ignore_debug={ignore_debug} should fail in Parser, got: {error}"),
                ));
            }
            Ok(_) => {
                return Err(TestFailure::new(
                    FailureKind::DecompileFailed,
                    "truncated debug layout was accepted",
                    format!("ignore_debug={ignore_debug} accepted a truncated debug layout"),
                ));
            }
        }
    }
    Ok(())
}

pub(super) fn assert_luajit_table_remove_contract(
    entry: &LuaCaseManifestEntry,
    suite_label: &str,
) -> Result<(), TestFailure> {
    if entry.dialect != LuaCaseDialect::Luajit {
        return Err(luajit_builtin_contract_failure(
            entry,
            "table.remove contract requires the LuaJIT dialect",
        ));
    }

    let source = repo_root().join(entry.path);
    let artifact = suite_artifact_path(suite_label, entry, "toolchain-fixture", "luajit");
    let raw_dump = artifact.with_extension("raw.luajit");
    ensure_parent_dir(&raw_dump).map_err(|error| luajit_builtin_contract_failure(entry, error))?;
    let raw_dump_arg = raw_dump.to_string_lossy().into_owned();
    let command_output = run_lua_file_with_args(
        "luajit",
        &source,
        &["--dump-table-remove", raw_dump_arg.as_str()],
    )
    .map_err(|error| luajit_builtin_contract_failure(entry, error))?;
    if !command_output.success() {
        return Err(luajit_builtin_contract_failure(
            entry,
            format!(
                "official runtime failed to dump table.remove\n{}",
                command_output.render()
            ),
        ));
    }
    let dump_bytes = fs::read(&raw_dump).map_err(|error| {
        luajit_builtin_contract_failure(
            entry,
            format!("read {} failed: {error}", repo_relative_display(&raw_dump)),
        )
    })?;
    write_output_file(&artifact, &dump_bytes).map_err(|error| {
        luajit_builtin_contract_failure(
            entry,
            format!("write {} failed: {error}", repo_relative_display(&artifact)),
        )
    })?;

    let mut options = decompile_options(entry);
    options.generate.mode = GenerateMode::Permissive;
    let result = decompile(&dump_bytes, options).map_err(|error| {
        luajit_builtin_contract_failure(
            entry,
            format!(
                "decompile {} failed: {error}",
                repo_relative_display(&artifact)
            ),
        )
    })?;
    assert_auto_dialect(
        "LuaJIT table.remove fixture",
        result.state.dialect,
        DecompileDialect::Luajit,
        entry.path,
    )?;

    let lowered = result.state.lowered.as_ref().ok_or_else(|| {
        luajit_builtin_contract_failure(entry, "generate stage returned no lowered chunk")
    })?;
    let generated = result.state.generated.as_ref().ok_or_else(|| {
        luajit_builtin_contract_failure(entry, "generate stage returned no generated chunk")
    })?;

    let mut guards = Vec::new();
    let mut raw_gets = Vec::new();
    let mut raw_sets = Vec::new();
    for instr in &lowered.main.instrs {
        match instr {
            LowInstr::TypeGuard(instr) => guards.push((instr.subject, instr.kind)),
            LowInstr::GetTable(instr) if instr.kind == GetTableKind::Raw => {
                raw_gets.push((instr.dst, instr.base, instr.key));
            }
            LowInstr::SetTable(instr) if instr.kind == SetTableKind::Raw => {
                raw_sets.push((instr.base, instr.key, instr.value));
            }
            _ => {}
        }
    }

    let guards_match = matches!(
        guards.as_slice(),
        [
            (Reg(0), TypeGuardKind::Table),
            (Reg(1), TypeGuardKind::Integer | TypeGuardKind::Number)
        ]
    );
    let expected_raw_gets = [
        (Reg(3), AccessBase::Reg(Reg(0)), AccessKey::Reg(Reg(2))),
        (Reg(3), AccessBase::Reg(Reg(0)), AccessKey::Reg(Reg(1))),
        (Reg(9), AccessBase::Reg(Reg(0)), AccessKey::Reg(Reg(7))),
    ];
    let expected_raw_sets = [
        (
            AccessBase::Reg(Reg(0)),
            AccessKey::Reg(Reg(2)),
            ValueOperand::Reg(Reg(4)),
        ),
        (
            AccessBase::Reg(Reg(0)),
            AccessKey::Reg(Reg(8)),
            ValueOperand::Reg(Reg(9)),
        ),
        (
            AccessBase::Reg(Reg(0)),
            AccessKey::Reg(Reg(2)),
            ValueOperand::Reg(Reg(4)),
        ),
    ];
    if !guards_match || raw_gets != expected_raw_gets || raw_sets != expected_raw_sets {
        let lir = lowered
            .main
            .instrs
            .iter()
            .map(format_low_instr)
            .collect::<Vec<_>>()
            .join("\n");
        return Err(luajit_builtin_contract_failure(
            entry,
            format!(
                "typed LIR contract mismatch in {}\nguards={guards:?}\nraw_gets={raw_gets:?}\nraw_sets={raw_sets:?}\nlow-ir:\n{lir}",
                repo_relative_display(&artifact)
            ),
        ));
    }

    const RAW_READ_DIAGNOSTIC: &str = "LuaJIT raw table read has no exact Lua source form";
    const RAW_WRITE_DIAGNOSTIC: &str = "LuaJIT raw table write has no exact Lua source form";
    let read_diagnostics = generated.source.matches(RAW_READ_DIAGNOSTIC).count();
    let write_diagnostics = generated.source.matches(RAW_WRITE_DIAGNOSTIC).count();
    if generated.kind != GeneratedChunkKind::DiagnosticPseudocode
        || read_diagnostics != 3
        || write_diagnostics != 3
    {
        return Err(luajit_builtin_contract_failure(
            entry,
            format!(
                "raw access diagnostic contract mismatch in {}: kind={:?}, reads={read_diagnostics}, writes={write_diagnostics}\n{}",
                repo_relative_display(&artifact),
                generated.kind,
                generated.source
            ),
        ));
    }

    const TYPE_GUARD_PREFIX: &str = "LuaJIT builtin ";
    const TYPE_GUARD_LOCATION: &str = "type guard at block #";
    const TYPE_GUARD_SPELLING: &str = "has no exact Lua source spelling;";
    let type_guard_diagnostics = generated.source.matches(TYPE_GUARD_PREFIX).count();
    if type_guard_diagnostics != guards.len()
        || !generated.source.contains(TYPE_GUARD_LOCATION)
        || !generated.source.contains(TYPE_GUARD_SPELLING)
    {
        return Err(luajit_builtin_contract_failure(
            entry,
            format!(
                "type-guard diagnostic contract mismatch in {}: expected={}, found={type_guard_diagnostics}\n{}",
                repo_relative_display(&artifact),
                guards.len(),
                generated.source
            ),
        ));
    }

    Ok(())
}

pub(super) fn assert_luajit_method_protocol_contract(
    entry: &LuaCaseManifestEntry,
    suite_label: &str,
) -> Result<(), TestFailure> {
    if entry.dialect != LuaCaseDialect::Luajit {
        return Err(luajit_method_contract_failure(
            entry,
            "method protocol contract requires the LuaJIT dialect",
        ));
    }

    let (raw, lowered) = lower_luajit_method_fixture(
        entry,
        suite_label,
        "large-method-fixture",
        "--dump-large-method",
    )?;

    let signatures = lowered
        .main
        .children
        .iter()
        .enumerate()
        .map(|(index, proto)| {
            raw.main
                .common
                .children
                .get(index)
                .and_then(|raw_proto| large_method_signature(raw_proto, proto))
        })
        .collect::<Vec<_>>();
    if signatures.len() != 2
        || !signatures.contains(&Some(LargeMethodSignature::Method))
        || !signatures.contains(&Some(LargeMethodSignature::Dot))
    {
        return Err(luajit_method_contract_failure(
            entry,
            format!("large-key method/dot LIR signatures mismatch: {signatures:?}"),
        ));
    }
    let (_, bypassed) = lower_luajit_method_fixture(
        entry,
        suite_label,
        "bypassed-method-fixture",
        "--dump-bypassed-method",
    )?;
    if !bypassed_method_signature(&bypassed.main) {
        return Err(luajit_method_contract_failure(
            entry,
            "external entry into split setup was not kept as a normal call",
        ));
    }
    Ok(())
}

pub(super) fn lower_luajit_method_fixture(
    entry: &LuaCaseManifestEntry,
    suite_label: &str,
    artifact_label: &str,
    argument: &str,
) -> Result<(RawChunk, LoweredChunk), TestFailure> {
    let source = repo_root().join(entry.path);
    let artifact = suite_artifact_path(suite_label, entry, artifact_label, "luajit");
    let raw_dump = artifact.with_extension("raw.luajit");
    ensure_parent_dir(&raw_dump).map_err(|error| luajit_method_contract_failure(entry, error))?;
    let raw_dump_arg = raw_dump.to_string_lossy().into_owned();
    let command_output =
        run_lua_file_with_args("luajit", &source, &[argument, raw_dump_arg.as_str()])
            .map_err(|error| luajit_method_contract_failure(entry, error))?;
    if !command_output.success() {
        return Err(luajit_method_contract_failure(
            entry,
            command_output.render(),
        ));
    }
    let dump = fs::read(&raw_dump).map_err(|error| {
        luajit_method_contract_failure(
            entry,
            format!("read {} failed: {error}", repo_relative_display(&raw_dump)),
        )
    })?;
    write_output_file(&artifact, &dump).map_err(|error| {
        luajit_method_contract_failure(
            entry,
            format!("write {} failed: {error}", repo_relative_display(&artifact)),
        )
    })?;
    let mut options = decompile_options(entry);
    options.target_stage = DecompileStage::Transformer;
    let state = decompile(&dump, options)
        .map_err(|error| luajit_method_contract_failure(entry, error.to_string()))?
        .state;
    let raw = state.raw_chunk.ok_or_else(|| {
        luajit_method_contract_failure(entry, "method fixture produced no raw chunk")
    })?;
    let lowered = state.lowered.ok_or_else(|| {
        luajit_method_contract_failure(entry, "method fixture produced no lowered chunk")
    })?;
    Ok((raw, lowered))
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) enum LargeMethodSignature {
    Method,
    Dot,
}

pub(super) fn large_method_signature(
    raw: &RawProto,
    proto: &LoweredProto,
) -> Option<LargeMethodSignature> {
    let DialectConstPoolExtra::LuaJit(constants) = &raw.common.constants.extra else {
        return None;
    };
    if constants.kgc_entries.len() <= u8::MAX as usize {
        return None;
    }

    if let [
        ..,
        LowInstr::Move(snapshot),
        LowInstr::LoadConst(key),
        LowInstr::GetTable(get),
        LowInstr::TailCall(call),
    ] = proto.instrs.as_slice()
    {
        let method_args = matches!(call.args, ValuePack::Fixed(args) if args.start == snapshot.dst && args.len == 1);
        if snapshot.src == Reg(0)
            && key.dst.index() == snapshot.dst.index() + 1
            && get.dst == call.callee
            && get.base == AccessBase::Reg(snapshot.dst)
            && get.key == AccessKey::Const(key.value)
            && get.kind == GetTableKind::Method
            && call.kind == CallKind::Method
            && call.method_name.map(|hint| hint.const_ref) == Some(key.value)
            && method_args
        {
            return Some(LargeMethodSignature::Method);
        }
    }

    if let [
        ..,
        LowInstr::LoadConst(key),
        LowInstr::GetTable(get),
        LowInstr::Move(arg),
        LowInstr::TailCall(call),
    ] = proto.instrs.as_slice()
    {
        let explicit_arg =
            matches!(call.args, ValuePack::Fixed(args) if args.start == arg.dst && args.len == 1);
        if arg.src == Reg(0)
            && get.dst == call.callee
            && get.base == AccessBase::Reg(arg.src)
            && get.key == AccessKey::Reg(key.dst)
            && get.kind == GetTableKind::Normal
            && call.kind == CallKind::Normal
            && call.method_name.is_none()
            && explicit_arg
        {
            return Some(LargeMethodSignature::Dot);
        }
    }
    None
}

pub(super) fn bypassed_method_signature(proto: &LoweredProto) -> bool {
    let [
        ..,
        LowInstr::Move(snapshot),
        LowInstr::GetTable(get),
        LowInstr::TailCall(call),
    ] = proto.instrs.as_slice()
    else {
        return false;
    };
    matches!(call.args, ValuePack::Fixed(args) if args.start == snapshot.dst && args.len == 1)
        && snapshot.src == Reg(0)
        && get.dst == call.callee
        && get.base == AccessBase::Reg(snapshot.src)
        && matches!(get.key, AccessKey::Const(_))
        && get.kind == GetTableKind::Normal
        && call.kind == CallKind::Normal
        && call.method_name.is_none()
}

pub(super) fn luajit_builtin_contract_failure(
    entry: &LuaCaseManifestEntry,
    detail: impl Into<String>,
) -> TestFailure {
    let detail = detail.into();
    TestFailure::new(
        FailureKind::LuaJitBuiltinContractAssertionFailed,
        "LuaJIT builtin contract failed",
        format!(
            "LuaJIT builtin contract failed for {}: {detail}",
            entry.path
        ),
    )
}

pub(super) fn luajit_method_contract_failure(
    entry: &LuaCaseManifestEntry,
    detail: impl Into<String>,
) -> TestFailure {
    TestFailure::new(
        FailureKind::LuaJitMethodProtocolContractAssertionFailed,
        "LuaJIT method protocol contract failed",
        format!(
            "LuaJIT method protocol contract failed for {}: {}",
            entry.path,
            detail.into()
        ),
    )
}

pub(super) fn run_unsupported_island_contract(
    entry: &LuaCaseManifestEntry,
    jump_pc: usize,
    target_pc: usize,
) -> Result<TestSuccess, TestFailure> {
    let mut chunk = compile_manifest_case(entry);
    patch_lua51_main_jump(&mut chunk, jump_pc, target_pc).map_err(|detail| {
        TestFailure::new(
            FailureKind::StructureContractAssertionFailed,
            "prepare irreducible Lua 5.1 fixture failed",
            detail,
        )
    })?;

    // 契约：Lua 5.1 面对真正不可规约多入口图，使用局部状态机兜底，
    // 绝不向 Lua 5.1 源码注入非法 goto/::label::，且在 Strict 模式下也能产出合法源码。
    let mut strict_options = decompile_options(entry);
    strict_options.generate.mode = GenerateMode::Strict;
    let strict = decompile(&chunk, strict_options).map_err(|error| {
        structure_contract_failure(format!(
            "Lua 5.1 irreducible state-machine fallback failed under Strict mode: {error}"
        ))
    })?;
    let generated = strict.state.generated.as_ref().ok_or_else(|| {
        structure_contract_failure("strict mode returned no generated chunk for irreducible graph")
    })?;
    if generated.kind != GeneratedChunkKind::Source {
        return Err(structure_contract_failure(format!(
            "expected valid Lua 5.1 Source via state-machine fallback, got {:?}",
            generated.kind
        )));
    }
    if generated.source.contains("goto ") || generated.source.contains("::") {
        return Err(structure_contract_failure(format!(
            "Lua 5.1 output leaked illegal goto/label:\n{}",
            generated.source
        )));
    }
    let state_machine_total: usize = strict
        .state
        .ast
        .as_ref()
        .map(|ast| ast.protos.iter().map(|p| p.state_machine_count).sum())
        .unwrap_or(0);
    if state_machine_total == 0 {
        return Err(structure_contract_failure(format!(
            "expected irreducible Lua 5.1 fixture to trigger state-machine fallback, got 0:\n{}",
            generated.source
        )));
    }
    let patched_chunk_path = suite_artifact_path("irreducible", entry, "patched-chunk", "luac");
    write_output_file(&patched_chunk_path, &chunk).map_err(structure_contract_failure)?;
    let generated_source_path = write_generated_case_source(entry, "irreducible", &generated.source)
        .map_err(structure_contract_failure)?;
    let (compiled_path, compile_output) = compile_generated_source_to_suite_artifact(
        entry,
        "irreducible",
        &generated_source_path,
        true,
    )
    .map_err(structure_contract_failure)?;
    if !compile_output.success() {
        return Err(structure_contract_failure(format!(
            "generated Lua 5.1 state-machine source failed to compile:\n{}\n{}",
            compile_output.render(),
            generated.source
        )));
    }

    // 验证状态机产出的字节码在两个入口分支（enter_body=nil / true）上与原始 patched chunk 运行输出一致。
    let runtime = lua_tool_path("lua5.1", "lua").map_err(structure_contract_failure)?;
    for (case_label, enter_body) in [("enter_body=nil", false), ("enter_body=true", true)] {
        let run_chunk = |path: &Path| -> Result<LuaCommandOutput, TestFailure> {
            if enter_body {
                run_command(
                    &runtime,
                    [
                        OsStr::new("-e"),
                        OsStr::new("enter_body = true"),
                        path.as_os_str(),
                    ],
                    "lua",
                )
                .map_err(structure_contract_failure)
            } else {
                run_lua_file("lua5.1", path).map_err(structure_contract_failure)
            }
        };
        let expected_output = run_chunk(&patched_chunk_path)?;
        if !expected_output.success() {
            return Err(structure_contract_failure(format!(
                "patched irreducible chunk failed to run ({case_label}):\n{}",
                expected_output.render()
            )));
        }
        let actual_output = run_chunk(&compiled_path)?;
        if !actual_output.success() {
            return Err(structure_contract_failure(format!(
                "generated Lua 5.1 state-machine artifact failed to run ({case_label}):\n{}\n{}",
                actual_output.render(),
                generated.source
            )));
        }
        if let Some(diff) = diff_command_outputs(
            "patched-chunk",
            &expected_output,
            "state-machine-artifact",
            &actual_output,
        ) {
            return Err(structure_contract_failure(format!(
                "Lua 5.1 state-machine output mismatch ({case_label}):\n{diff}\n{}",
                generated.source
            )));
        }
    }

    Ok(TestSuccess { proto_count: 1 })
}

pub(super) fn structure_contract_failure(detail: impl Into<String>) -> TestFailure {
    TestFailure::new(
        FailureKind::StructureContractAssertionFailed,
        "irreducible Lua 5.1 state-machine contract failed",
        detail,
    )
}
