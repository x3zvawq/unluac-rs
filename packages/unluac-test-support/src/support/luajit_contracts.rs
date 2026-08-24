//! 校验 LuaJIT 内建与方法调用协议及特殊 island 合同；依赖 lowered proto，不负责通用反编译断言；例如识别大参数方法调用是否绕过错误 lowering。

use super::*;

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
    let dump = run_lua_file_with_args("luajit", &source, &["--dump-table-remove"])
        .map_err(|error| luajit_builtin_contract_failure(entry, error))?;
    if !dump.success() {
        return Err(luajit_builtin_contract_failure(
            entry,
            format!(
                "official runtime failed to dump table.remove\n{}",
                dump.render()
            ),
        ));
    }

    let artifact = suite_artifact_path(
        suite_label,
        "luajit",
        entry.variant,
        "toolchain-fixture",
        entry.path,
        "luajit",
    );
    write_output_file(&artifact, &dump.stdout).map_err(|error| {
        luajit_builtin_contract_failure(
            entry,
            format!("write {} failed: {error}", repo_relative_display(&artifact)),
        )
    })?;

    let mut options = decompile_options(entry);
    options.generate.mode = GenerateMode::Permissive;
    let result = decompile(&dump.stdout, options).map_err(|error| {
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

    let lowered = lower_luajit_method_fixture(
        entry,
        suite_label,
        "large-method-fixture",
        "--dump-large-method",
    )?;

    let signatures = lowered
        .main
        .children
        .iter()
        .map(|proto| large_method_signature(proto))
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
    let bypassed = lower_luajit_method_fixture(
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
) -> Result<LoweredChunk, TestFailure> {
    let source = repo_root().join(entry.path);
    let dump = run_lua_file_with_args("luajit", &source, &[argument])
        .map_err(|error| luajit_method_contract_failure(entry, error))?;
    if !dump.success() {
        return Err(luajit_method_contract_failure(entry, dump.render()));
    }
    let artifact = suite_artifact_path(
        suite_label,
        "luajit",
        entry.variant,
        artifact_label,
        entry.path,
        "luajit",
    );
    write_output_file(&artifact, &dump.stdout).map_err(|error| {
        luajit_method_contract_failure(
            entry,
            format!("write {} failed: {error}", repo_relative_display(&artifact)),
        )
    })?;
    let mut options = decompile_options(entry);
    options.target_stage = DecompileStage::Transformer;
    decompile(&dump.stdout, options)
        .map_err(|error| luajit_method_contract_failure(entry, error.to_string()))?
        .state
        .lowered
        .ok_or_else(|| {
            luajit_method_contract_failure(entry, "method fixture produced no lowered chunk")
        })
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) enum LargeMethodSignature {
    Method,
    Dot,
}

pub(super) fn large_method_signature(proto: &LoweredProto) -> Option<LargeMethodSignature> {
    let DialectConstPoolExtra::LuaJit(constants) = &proto.constants.extra else {
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
            "prepare unsupported island fixture failed",
            detail,
        )
    })?;

    let mut structure_options = decompile_options(entry);
    structure_options.target_stage = DecompileStage::Structure;
    let structure = decompile(&chunk, structure_options).map_err(|error| {
        structure_contract_failure(format!(
            "unsupported island fixture failed before the frozen StructurePlan: {error}"
        ))
    })?;
    let facts =
        structure.state.structure_facts.as_ref().ok_or_else(|| {
            structure_contract_failure("structure stage returned no StructureFacts")
        })?;
    let has_island = facts
        .plan()
        .regions()
        .any(|(_, region)| matches!(region, RegionPlan::Unstructured { .. }));
    let requires_goto = facts
        .plan()
        .requirements()
        .unavailable_features()
        .contains(&ControlFlowFeature::GotoLabel);
    if !has_island || !requires_goto {
        return Err(structure_contract_failure(format!(
            "mutated Lua 5.1 fixture did not freeze an unavailable goto island: island={has_island}, requires_goto={requires_goto}"
        )));
    }

    let mut strict_options = decompile_options(entry);
    strict_options.generate.mode = GenerateMode::Strict;
    match decompile(&chunk, strict_options) {
        Err(DecompileError::Ast(AstLowerError::UnsupportedFeature {
            dialect: DecompileDialect::Lua51,
            feature: "goto/label",
            context: "StructurePlan",
        })) => {}
        Err(error) => {
            return Err(structure_contract_failure(format!(
                "strict mode returned the wrong unsupported-island error: {error}"
            )));
        }
        Ok(_) => {
            return Err(structure_contract_failure(
                "strict mode accepted an unavailable goto island",
            ));
        }
    }

    let mut permissive_options = decompile_options(entry);
    permissive_options.generate.mode = GenerateMode::Permissive;
    let permissive = decompile(&chunk, permissive_options).map_err(|error| {
        structure_contract_failure(format!(
            "permissive mode rejected an unsupported island: {error}"
        ))
    })?;
    let generated =
        permissive.state.generated.as_ref().ok_or_else(|| {
            structure_contract_failure("permissive mode returned no generated chunk")
        })?;
    if generated.kind != GeneratedChunkKind::DiagnosticPseudocode
        || !generated
            .source
            .contains("-- [unluac error] diagnostic pseudocode:")
        || !generated.source.contains("StructurePlan requirements:")
    {
        return Err(structure_contract_failure(format!(
            "permissive mode did not preserve the plan diagnostic contract: kind={:?}\n{}",
            generated.kind, generated.source
        )));
    }

    Ok(TestSuccess { proto_count: 1 })
}

pub(super) fn structure_contract_failure(detail: impl Into<String>) -> TestFailure {
    TestFailure::new(
        FailureKind::StructureContractAssertionFailed,
        "StructurePlan strict/permissive contract failed",
        detail,
    )
}
