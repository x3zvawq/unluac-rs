//! 这个子模块负责把固定 operand、常量池项和表访问骨架降成基础 HIR 表达式。
//!
//! 它依赖 Transformer 已经给好的 operand 形状、Dataflow 的 use/def 事实和常量池，不会
//! 越权去恢复短路结构或 merge 来源。
//! 例如：`GETTABLE r0, r1, "x"` 会先在这里变成 `r1.x` 对应的访问表达式骨架。

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
    }
}

pub(crate) fn expr_for_value_operand_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    operand: ValueOperand,
) -> HirExpr {
    match operand {
        ValueOperand::Reg(reg) => expr_for_reg_use_inline(lowering, block, instr_ref, reg),
        ValueOperand::Const(const_ref) => expr_for_const(lowering.proto, const_ref),
        ValueOperand::Integer(value) => HirExpr::Integer(value),
    }
}

pub(crate) fn expr_for_const(proto: &LoweredProto, const_ref: ConstRef) -> HirExpr {
    match proto.constants.common.literals.get(const_ref.index()) {
        Some(RawLiteralConst::Nil) => HirExpr::Nil,
        Some(RawLiteralConst::Boolean(value)) => HirExpr::Boolean(*value),
        Some(RawLiteralConst::Integer(value)) => HirExpr::Integer(*value),
        Some(RawLiteralConst::Number(value)) => HirExpr::Number(*value),
        Some(RawLiteralConst::String(value)) => HirExpr::String(decode_raw_string(value)),
        Some(RawLiteralConst::Int64(value)) => HirExpr::Int64(*value),
        Some(RawLiteralConst::UInt64(value)) => HirExpr::UInt64(*value),
        Some(RawLiteralConst::Complex { real, imag }) => HirExpr::Complex {
            real: *real,
            imag: *imag,
        },
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
    if matches!(base, AccessBase::Env)
        && let Some(name) = global_name_from_key(lowering.proto, key)
    {
        return HirExpr::GlobalRef(HirGlobalRef { name });
    }

    HirExpr::TableAccess(Box::new(HirTableAccess {
        base: lower_access_base_expr(lowering, block, instr_ref, base),
        key: lower_access_key_expr(lowering, block, instr_ref, key),
    }))
}

pub(crate) fn lower_table_access_target(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> HirLValue {
    if matches!(base, AccessBase::Env)
        && let Some(name) = global_name_from_key(lowering.proto, key)
    {
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
    if access_base_is_named_env(lowering.proto, base)
        && let Some(name) = global_name_from_key(lowering.proto, key)
    {
        return HirExpr::GlobalRef(HirGlobalRef { name });
    }

    HirExpr::TableAccess(Box::new(HirTableAccess {
        base: lower_access_base_expr_inline(lowering, block, instr_ref, base),
        key: lower_access_key_expr_inline(lowering, block, instr_ref, key),
    }))
}

fn lower_access_base_expr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    base: AccessBase,
) -> HirExpr {
    match base {
        AccessBase::Reg(reg) => expr_for_reg_use(lowering, block, instr_ref, reg),
        AccessBase::Env => HirExpr::GlobalRef(HirGlobalRef {
            name: "_ENV".to_owned(),
        }),
        AccessBase::Upvalue(upvalue) => {
            HirExpr::UpvalueRef(lowering.bindings.upvalues[upvalue.index()])
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
        AccessBase::Env => HirExpr::GlobalRef(HirGlobalRef {
            name: "_ENV".to_owned(),
        }),
        AccessBase::Upvalue(upvalue) => {
            HirExpr::UpvalueRef(lowering.bindings.upvalues[upvalue.index()])
        }
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

fn access_base_is_named_env(proto: &LoweredProto, base: AccessBase) -> bool {
    match base {
        AccessBase::Env => true,
        AccessBase::Upvalue(upvalue) => proto
            .debug_info
            .common
            .upvalue_names
            .get(upvalue.index())
            .is_some_and(|name| decode_raw_string(name) == "_ENV"),
        AccessBase::Reg(_) => false,
    }
}

fn global_name_from_key(proto: &LoweredProto, key: AccessKey) -> Option<String> {
    let AccessKey::Const(const_ref) = key else {
        return None;
    };
    match proto.constants.common.literals.get(const_ref.index()) {
        Some(RawLiteralConst::String(value)) => Some(decode_raw_string(value)),
        _ => None,
    }
}
