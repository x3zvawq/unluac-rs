//! 这个子模块负责把固定 operand、常量池项和表访问骨架降成基础 HIR 表达式。
//!
//! 它依赖 Transformer 已经给好的 operand 形状、Dataflow 的 use/def 事实和常量池，不会
//! 越权去恢复短路结构或 merge 来源。
//! 例如：`GETTABLE r0, r1, "x"` 会先在这里变成 `r1["x"]` 对应的访问
//! 表达式骨架；已证明的 `_ENV[key]` 则无论 key 能否写成裸标识符，都保留为
//! raw-byte `HirGlobalRef`，并保留原读取来源供物理帧查询；目标语法合法性留给 AST 验证。

use super::*;

pub(crate) fn expr_for_value_operand(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    operand: ValueOperand,
) -> HirExpr {
    match operand {
        ValueOperand::Reg(reg) => expr_for_reg_use(lowering, block, instr_ref, reg),
        ValueOperand::Const(const_ref) => expr_for_const(lowering.proto, const_ref),
        ValueOperand::Integer(value) => HirExpr::Integer(value),
        ValueOperand::Nil => HirExpr::Nil,
        ValueOperand::Boolean(value) => HirExpr::Boolean(value),
    }
}

pub(crate) fn expr_for_value_operand_single_eval_pure_operand(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    operand: ValueOperand,
) -> HirExpr {
    match operand {
        ValueOperand::Reg(reg) => {
            expr_for_reg_use_single_eval_with_call_policy(lowering, block, instr_ref, reg, true)
        }
        ValueOperand::Const(const_ref) => expr_for_const(lowering.proto, const_ref),
        ValueOperand::Integer(value) => HirExpr::Integer(value),
        ValueOperand::Nil => HirExpr::Nil,
        ValueOperand::Boolean(value) => HirExpr::Boolean(value),
    }
}

pub(crate) fn expr_for_const(proto: &LoweredProto, const_ref: ConstRef) -> HirExpr {
    match proto.constants.get(const_ref.index()) {
        Some(RawLiteralConst::Nil) => HirExpr::Nil,
        Some(RawLiteralConst::Boolean(value)) => HirExpr::Boolean(*value),
        Some(RawLiteralConst::Integer(value)) => HirExpr::Integer(*value),
        Some(RawLiteralConst::Number(value)) => HirExpr::Number(*value),
        Some(RawLiteralConst::String(value)) => HirExpr::String(raw_lua_string(value)),
        Some(RawLiteralConst::Int64(value)) => HirExpr::Int64(*value),
        Some(RawLiteralConst::UInt64(value)) => HirExpr::UInt64(*value),
        Some(RawLiteralConst::Complex { real, imag }) => HirExpr::Complex {
            real: *real,
            imag: *imag,
        },
        Some(RawLiteralConst::Vector(vector)) => HirExpr::Vector(*vector),
        None => unresolved_expr(format!("const k{}", const_ref.index())),
    }
}

pub(crate) fn lower_table_access_expr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> HirExpr {
    if let Some(key) = global_key_for_access(lowering, block, instr_ref, base, key) {
        return global_read(lowering, instr_ref, key);
    }

    HirExpr::TableAccess(Box::new(HirTableAccess {
        sources: crate::hir::common::HirOperationSources::Single(
            crate::hir::common::HirSourceSite {
                proto: lowering.id,
                instr: instr_ref,
            },
        ),
        metamethod_free: lowering.dataflow.plain_table_reads[instr_ref.index()],
        base: lower_access_base_expr(lowering, block, instr_ref, base),
        key: lower_access_key_expr(lowering, block, instr_ref, key),
        method_setup_protocol: lowering
            .promotion_facts
            .method_setup_protocol_for_get(instr_ref),
    }))
}

pub(crate) fn lower_raw_table_get_expr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> HirExpr {
    // LuaJIT raw opcode 绕过元方法；可覆盖的全局 `rawget` 也不是精确 VM 合同。
    // 保留为 effectful residual 才能让严格模式拒绝改义、宽松模式显示诊断。
    raw_table_get_expr(
        lower_access_base_expr(lowering, block, instr_ref, base),
        lower_access_key_expr(lowering, block, instr_ref, key),
    )
}

pub(crate) fn lower_raw_table_set_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
    value: ValueOperand,
) -> HirCallExpr {
    // 同 raw read，不把 VM primitive 伪装成会触发 `__newindex` 的普通赋值。
    HirCallExpr {
        source_site: None,
        argument_roots: Vec::new(),
        frame_root_ends: Vec::new(),
        callee: unresolved_expr("LuaJIT raw table write has no exact Lua source form"),
        args: vec![
            lower_access_base_expr(lowering, block, instr_ref, base),
            lower_access_key_expr(lowering, block, instr_ref, key),
            expr_for_value_operand(lowering, block, instr_ref, value),
        ]
        .into(),
        method: false.into(),
        fastcall: None,
        method_key: None,
        callee_root_handoff: None,
        method_rewrite_transaction: None,
        plain_method_syntax: false,
    }
}

pub(crate) fn lower_table_access_target(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> HirLValue {
    if let Some(key) = global_key_for_access(lowering, block, instr_ref, base, key) {
        return HirLValue::Global(HirGlobalRef {
            sources: Default::default(),
            key,
        });
    }

    HirLValue::TableAccess(Box::new(HirTableAccess {
        sources: crate::hir::common::HirOperationSources::Single(
            crate::hir::common::HirSourceSite {
                proto: lowering.id,
                instr: instr_ref,
            },
        ),
        metamethod_free: false,
        base: lower_access_base_expr(lowering, block, instr_ref, base),
        key: lower_access_key_expr(lowering, block, instr_ref, key),
        method_setup_protocol: None,
    }))
}

pub(crate) fn lower_table_access_expr_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> HirExpr {
    if let Some(key) = global_key_for_access(lowering, block, instr_ref, base, key) {
        return global_read(lowering, instr_ref, key);
    }

    HirExpr::TableAccess(Box::new(HirTableAccess {
        sources: crate::hir::common::HirOperationSources::Single(
            crate::hir::common::HirSourceSite {
                proto: lowering.id,
                instr: instr_ref,
            },
        ),
        metamethod_free: lowering.dataflow.plain_table_reads[instr_ref.index()],
        base: lower_access_base_expr_inline(lowering, block, instr_ref, base),
        key: lower_access_key_expr_inline(lowering, block, instr_ref, key),
        method_setup_protocol: lowering
            .promotion_facts
            .method_setup_protocol_for_get(instr_ref),
    }))
}

pub(crate) fn lower_raw_table_get_expr_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> HirExpr {
    raw_table_get_expr(
        lower_access_base_expr_inline(lowering, block, instr_ref, base),
        lower_access_key_expr_inline(lowering, block, instr_ref, key),
    )
}

fn lower_access_base_expr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
) -> HirExpr {
    match base {
        AccessBase::Reg(reg) => expr_for_reg_use(lowering, block, instr_ref, reg),
        AccessBase::Env => unresolved_expr("implicit environment has no source-level value"),
        AccessBase::EnvironmentUpvalue(upvalue) => {
            lower_upvalue_operand_expr(lowering, UpvalueOperand::Env(upvalue))
        }
        AccessBase::Upvalue(upvalue) => {
            lower_upvalue_operand_expr(lowering, UpvalueOperand::Upvalue(upvalue))
        }
    }
}

fn lower_access_base_expr_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
) -> HirExpr {
    match base {
        AccessBase::Reg(reg) => expr_for_reg_use_inline(lowering, block, instr_ref, reg),
        AccessBase::Env => unresolved_expr("implicit environment has no source-level value"),
        AccessBase::EnvironmentUpvalue(upvalue) => {
            lower_upvalue_operand_expr(lowering, UpvalueOperand::Env(upvalue))
        }
        AccessBase::Upvalue(upvalue) => {
            lower_upvalue_operand_expr(lowering, UpvalueOperand::Upvalue(upvalue))
        }
    }
}

pub(in crate::hir::analyze) fn lower_upvalue_operand_expr(
    lowering: &ProtoLowering<'_>,
    operand: UpvalueOperand,
) -> HirExpr {
    let upvalue = match operand {
        UpvalueOperand::Env(upvalue) | UpvalueOperand::Upvalue(upvalue) => upvalue,
    };
    HirExpr::UpvalueRef(lowering.bindings.upvalues[upvalue.index()])
}

pub(in crate::hir::analyze) fn lower_upvalue_operand_target(
    lowering: &ProtoLowering<'_>,
    operand: UpvalueOperand,
) -> HirLValue {
    let upvalue = match operand {
        UpvalueOperand::Env(upvalue) | UpvalueOperand::Upvalue(upvalue) => upvalue,
    };
    HirLValue::Upvalue(lowering.bindings.upvalues[upvalue.index()])
}

pub(crate) fn lower_table_access_expr_single_eval(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> HirExpr {
    if let Some(key) = global_key_for_access(lowering, block, instr_ref, base, key) {
        return global_read(lowering, instr_ref, key);
    }

    HirExpr::TableAccess(Box::new(HirTableAccess {
        sources: crate::hir::common::HirOperationSources::Single(
            crate::hir::common::HirSourceSite {
                proto: lowering.id,
                instr: instr_ref,
            },
        ),
        metamethod_free: lowering.dataflow.plain_table_reads[instr_ref.index()],
        base: lower_access_base_expr_single_eval(lowering, block, instr_ref, base),
        key: lower_access_key_expr_single_eval(lowering, block, instr_ref, key),
        method_setup_protocol: lowering
            .promotion_facts
            .method_setup_protocol_for_get(instr_ref),
    }))
}

pub(crate) fn lower_raw_table_get_expr_single_eval(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> HirExpr {
    raw_table_get_expr(
        lower_access_base_expr_single_eval(lowering, block, instr_ref, base),
        lower_access_key_expr_single_eval(lowering, block, instr_ref, key),
    )
}

fn raw_table_get_expr(base: HirExpr, key: HirExpr) -> HirExpr {
    HirExpr::Call(Box::new(HirCallExpr {
        source_site: None,
        argument_roots: Vec::new(),
        frame_root_ends: Vec::new(),
        callee: unresolved_expr("LuaJIT raw table read has no exact Lua source form"),
        args: vec![base, key].into(),
        method: false.into(),
        fastcall: None,
        method_key: None,
        callee_root_handoff: None,
        method_rewrite_transaction: None,
        plain_method_syntax: false,
    }))
}

fn lower_access_base_expr_single_eval(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
) -> HirExpr {
    match base {
        AccessBase::Reg(reg) => {
            let expr = expr_for_reg_use_single_eval_with_call_policy(
                lowering, block, instr_ref, reg, false,
            );
            // NewTable def 返回空 `{}`，但实际运行时这个寄存器持有的是被后续
            // SetTable/SetList 填充过的完整表。作为 GetTable 的 base，空表会
            // 丢掉所有条目的语义，因此退回到安全的 inline 模式。
            if matches!(&expr, HirExpr::TableConstructor(tc) if tc.fields.is_empty() && tc.trailing_multivalue.is_none())
            {
                return expr_for_reg_use_inline(lowering, block, instr_ref, reg);
            }
            expr
        }
        AccessBase::Env => unresolved_expr("implicit environment has no source-level value"),
        AccessBase::EnvironmentUpvalue(upvalue) => {
            HirExpr::UpvalueRef(lowering.bindings.upvalues[upvalue.index()])
        }
        AccessBase::Upvalue(upvalue) => {
            HirExpr::UpvalueRef(lowering.bindings.upvalues[upvalue.index()])
        }
    }
}

fn lower_access_key_expr_single_eval(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    key: AccessKey,
) -> HirExpr {
    match key {
        AccessKey::Reg(reg) => {
            expr_for_reg_use_single_eval_with_call_policy(lowering, block, instr_ref, reg, false)
        }
        AccessKey::Const(const_ref) => expr_for_const(lowering.proto, const_ref),
        AccessKey::Integer(value) => HirExpr::Integer(value),
    }
}

fn lower_access_key_expr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    key: AccessKey,
) -> HirExpr {
    match key {
        AccessKey::Reg(reg) => expr_for_reg_use(lowering, block, instr_ref, reg),
        AccessKey::Const(const_ref) => expr_for_const(lowering.proto, const_ref),
        AccessKey::Integer(value) => HirExpr::Integer(value),
    }
}

fn lower_access_key_expr_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    key: AccessKey,
) -> HirExpr {
    match key {
        AccessKey::Reg(reg) => expr_for_reg_use_inline(lowering, block, instr_ref, reg),
        AccessKey::Const(const_ref) => expr_for_const(lowering.proto, const_ref),
        AccessKey::Integer(value) => HirExpr::Integer(value),
    }
}

fn global_read(lowering: &ProtoLowering<'_>, instr: InstrRef, key: crate::LuaString) -> HirExpr {
    HirExpr::GlobalRef(HirGlobalRef {
        sources: crate::hir::common::HirOperationSources::Single(
            crate::hir::common::HirSourceSite {
                proto: lowering.id,
                instr,
            },
        ),
        key,
    })
}

pub(crate) fn global_key_for_access(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> Option<crate::LuaString> {
    let key = global_key_from_access_key(lowering, block, instr_ref, key)?;
    access_base_is_env(lowering, instr_ref, base, &key).then_some(key)
}

fn access_base_is_env(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    base: AccessBase,
    key: &crate::LuaString,
) -> bool {
    match base {
        AccessBase::Env | AccessBase::EnvironmentUpvalue(_) => true,
        AccessBase::Reg(reg) => reg_use_is_env(lowering, instr_ref, reg, key),
        AccessBase::Upvalue(_) => false,
    }
}

fn reg_use_is_env(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    reg: Reg,
    key: &crate::LuaString,
) -> bool {
    let Some(SsaValue::Def(def)) = lowering
        .dataflow
        .canonical_move_value(lowering.dataflow.use_value(instr_ref, reg))
    else {
        return false;
    };
    // SSA 定义支配其 use；根与最终访问同块时，中间 Move 块同时支配和被支配于
    // 此块，因此也必同块。只消费共享值根，跨事件延后读取的证明仍独立保留。
    if lowering.dataflow.def_block(def) != lowering.cfg.instr_to_block[instr_ref.index()] {
        return false;
    }
    let def_instr = lowering.dataflow.def_instr(def);
    let LowInstr::GetUpvalue(get_upvalue) = &lowering.proto.instrs[def_instr.index()] else {
        return false;
    };
    matches!(get_upvalue.src, UpvalueOperand::Env(_))
        && def_instr.index() < instr_ref.index()
        && (((def_instr.index() + 1)..instr_ref.index())
            .all(|index| !lowering.dataflow.effect_summaries[index].has_effect_tags())
            || access_is_global_decl(lowering, instr_ref, key))
}

fn access_is_global_decl(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    key: &crate::LuaString,
) -> bool {
    let Some(previous) = instr_ref.index().checked_sub(1) else {
        return false;
    };
    let (LowInstr::SetTable(_), LowInstr::ErrNil(err_nil)) = (
        &lowering.proto.instrs[instr_ref.index()],
        &lowering.proto.instrs[previous],
    ) else {
        return false;
    };
    let Some(RawLiteralConst::String(raw_name)) = err_nil
        .name
        .and_then(|const_ref| lowering.proto.constants.get(const_ref.index()))
    else {
        return false;
    };
    if crate::LuaString::from_raw(raw_name) != *key {
        return false;
    }

    let SsaValue::Def(probe_def) = lowering
        .dataflow
        .use_value(InstrRef(previous), err_nil.subject)
    else {
        return false;
    };
    let probe_instr = lowering.dataflow.def_instr(probe_def);
    let LowInstr::GetTable(probe) = &lowering.proto.instrs[probe_instr.index()] else {
        return false;
    };
    let probe_block = lowering.cfg.instr_to_block[probe_instr.index()];
    global_key_for_access(lowering, probe_block, probe_instr, probe.base, probe.key)
        .is_some_and(|probe_key| probe_key == *key)
}

fn global_key_from_access_key(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    key: AccessKey,
) -> Option<crate::LuaString> {
    match key {
        AccessKey::Const(const_ref) => {
            let RawLiteralConst::String(value) = lowering.proto.constants.get(const_ref.index())?
            else {
                return None;
            };
            Some(crate::LuaString::from_raw(value))
        }
        AccessKey::Reg(reg) => {
            let HirExpr::String(value) = expr_for_reg_use_inline(lowering, block, instr_ref, reg)
            else {
                return None;
            };
            Some(value)
        }
        AccessKey::Integer(_) => None,
    }
}
