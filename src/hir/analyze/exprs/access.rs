//! 这个子模块负责把固定 operand、常量池项和表访问骨架降成基础 HIR 表达式。
//!
//! 它依赖 Transformer 已经给好的 operand 形状、Dataflow 的 use/def 事实和常量池，不会
//! 越权去恢复短路结构或 merge 来源。
//! 例如：`GETTABLE r0, r1, "x"` 会先在这里变成 `r1.x` 对应的访问表达式骨架；
//! `_ENV["end"]` 这类非法裸标识符仍保留表访问，不会伪装成 global。

use std::collections::BTreeSet;

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
    match proto.constants.common.literals.get(const_ref.index()) {
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
    if let Some(name) = global_name_for_access(lowering, block, instr_ref, base, key) {
        return HirExpr::GlobalRef(HirGlobalRef { name });
    }

    HirExpr::TableAccess(Box::new(HirTableAccess {
        base: lower_access_base_expr(lowering, block, instr_ref, base),
        key: lower_access_key_expr(lowering, block, instr_ref, key),
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
        callee: unresolved_expr("LuaJIT raw table write has no exact Lua source form"),
        args: vec![
            lower_access_base_expr(lowering, block, instr_ref, base),
            lower_access_key_expr(lowering, block, instr_ref, key),
            expr_for_value_operand(lowering, block, instr_ref, value),
        ]
        .into(),
        method: false,
        method_name: None,
    }
}

pub(crate) fn lower_table_access_target(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> HirLValue {
    if let Some(name) = global_name_for_access(lowering, block, instr_ref, base, key) {
        return HirLValue::Global(HirGlobalRef { name });
    }

    HirLValue::TableAccess(Box::new(HirTableAccess {
        base: lower_access_base_expr(lowering, block, instr_ref, base),
        key: lower_access_key_expr(lowering, block, instr_ref, key),
    }))
}

pub(crate) fn lower_table_access_expr_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> HirExpr {
    if let Some(name) = global_name_for_access(lowering, block, instr_ref, base, key) {
        return HirExpr::GlobalRef(HirGlobalRef { name });
    }

    HirExpr::TableAccess(Box::new(HirTableAccess {
        base: lower_access_base_expr_inline(lowering, block, instr_ref, base),
        key: lower_access_key_expr_inline(lowering, block, instr_ref, key),
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
        AccessBase::Env => lower_upvalue_operand_expr(lowering, UpvalueOperand::Env),
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
        AccessBase::Env => lower_upvalue_operand_expr(lowering, UpvalueOperand::Env),
        AccessBase::Upvalue(upvalue) => {
            lower_upvalue_operand_expr(lowering, UpvalueOperand::Upvalue(upvalue))
        }
    }
}

pub(in crate::hir::analyze) fn lower_upvalue_operand_expr(
    lowering: &ProtoLowering<'_>,
    operand: UpvalueOperand,
) -> HirExpr {
    match operand {
        UpvalueOperand::Env => HirExpr::GlobalRef(HirGlobalRef {
            name: "_ENV".to_owned(),
        }),
        UpvalueOperand::Upvalue(upvalue) => {
            HirExpr::UpvalueRef(lowering.bindings.upvalues[upvalue.index()])
        }
    }
}

pub(in crate::hir::analyze) fn lower_upvalue_operand_target(
    lowering: &ProtoLowering<'_>,
    operand: UpvalueOperand,
) -> HirLValue {
    match operand {
        UpvalueOperand::Env => HirLValue::Global(HirGlobalRef {
            name: "_ENV".to_owned(),
        }),
        UpvalueOperand::Upvalue(upvalue) => {
            HirLValue::Upvalue(lowering.bindings.upvalues[upvalue.index()])
        }
    }
}

pub(crate) fn lower_table_access_expr_single_eval(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> HirExpr {
    if let Some(name) = global_name_for_access(lowering, block, instr_ref, base, key) {
        return HirExpr::GlobalRef(HirGlobalRef { name });
    }

    HirExpr::TableAccess(Box::new(HirTableAccess {
        base: lower_access_base_expr_single_eval(lowering, block, instr_ref, base),
        key: lower_access_key_expr_single_eval(lowering, block, instr_ref, key),
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
        callee: unresolved_expr("LuaJIT raw table read has no exact Lua source form"),
        args: vec![base, key].into(),
        method: false,
        method_name: None,
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
        AccessBase::Env => HirExpr::GlobalRef(HirGlobalRef {
            name: "_ENV".to_owned(),
        }),
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

pub(crate) fn global_name_for_access(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> Option<String> {
    let name = global_name_from_key(lowering, block, instr_ref, key)?;
    access_base_is_env(lowering, instr_ref, base, &name).then_some(name)
}

fn access_base_is_env(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    base: AccessBase,
    name: &str,
) -> bool {
    match base {
        AccessBase::Env => true,
        AccessBase::Reg(reg) => reg_use_is_env(lowering, instr_ref, reg, name),
        AccessBase::Upvalue(_) => false,
    }
}

fn reg_use_is_env(lowering: &ProtoLowering<'_>, instr_ref: InstrRef, reg: Reg, name: &str) -> bool {
    let access_block = lowering.cfg.instr_to_block[instr_ref.index()];
    let mut value = lowering.dataflow.use_value(instr_ref, reg);
    let mut seen = BTreeSet::new();
    while let SsaValue::Def(def) = value {
        if !seen.insert(def) || lowering.dataflow.def_block(def) != access_block {
            return false;
        }
        let def_instr = lowering.dataflow.def_instr(def);
        match &lowering.proto.instrs[def_instr.index()] {
            LowInstr::GetUpvalue(get_upvalue) => {
                return matches!(get_upvalue.src, UpvalueOperand::Env)
                    && def_instr.index() < instr_ref.index()
                    && (((def_instr.index() + 1)..instr_ref.index())
                        .all(|index| lowering.dataflow.effect_summaries[index].tags.is_empty())
                        || access_is_global_decl(lowering, instr_ref, name));
            }
            LowInstr::Move(move_instr) => {
                value = lowering.dataflow.use_value(def_instr, move_instr.src);
            }
            _ => return false,
        }
    }
    false
}

fn access_is_global_decl(lowering: &ProtoLowering<'_>, instr_ref: InstrRef, name: &str) -> bool {
    let Some(previous) = instr_ref.index().checked_sub(1) else {
        return false;
    };
    let (LowInstr::SetTable(_), LowInstr::ErrNil(err_nil)) = (
        &lowering.proto.instrs[instr_ref.index()],
        &lowering.proto.instrs[previous],
    ) else {
        return false;
    };
    let Some(RawLiteralConst::String(raw_name)) = err_nil.name.and_then(|const_ref| {
        lowering
            .proto
            .constants
            .common
            .literals
            .get(const_ref.index())
    }) else {
        return false;
    };
    decode_raw_string(raw_name) == name
}

fn global_name_from_key(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    key: AccessKey,
) -> Option<String> {
    let name = match key {
        AccessKey::Const(const_ref) => {
            let RawLiteralConst::String(value) = lowering
                .proto
                .constants
                .common
                .literals
                .get(const_ref.index())?
            else {
                return None;
            };
            decode_raw_string(value)
        }
        AccessKey::Reg(reg) => {
            let HirExpr::String(value) = expr_for_reg_use_inline(lowering, block, instr_ref, reg)
            else {
                return None;
            };
            value
                .preferred_text()
                .or_else(|| value.as_utf8())?
                .to_owned()
        }
        AccessKey::Integer(_) => return None,
    };
    is_lua_identifier_name(&name, lowering.target.version).then_some(name)
}
