//! 这个文件集中处理 low-ir 到 HIR 表达式世界的映射。
//!
//! HIR 的主流程需要频繁把寄存器、常量、表访问和分支条件翻译成表达式节点，如果
//! 这些逻辑散落在主 lowering 里，后面做短路恢复、临时变量消解时会很难判断修改边界。
//! 因此这里专门承载“值如何解释”的规则，让 `analyze.rs` 更多只关心语句和控制流骨架。

use crate::cfg::BlockRef;
use crate::cfg::{DefId, SsaValue};
use crate::hir::common::{
    HirBinaryExpr, HirBinaryOpKind, HirCallExpr, HirCapture, HirClosureExpr, HirExpr, HirGlobalRef,
    HirLValue, HirTableAccess, HirUnaryExpr, HirUnaryOpKind, UpvalueId,
};
use crate::parser::RawLiteralConst;
use crate::transformer::{
    AccessBase, AccessKey, BinaryOpKind, BranchCond, BranchOperands, BranchPredicate, CallKind,
    CondOperand, ConstRef, InstrRef, LowInstr, LoweredProto, Reg, ResultPack, UnaryOpKind,
    ValueOperand,
};

use super::ProtoLowering;
use super::helpers::{decode_raw_string, unresolved_expr};

pub(super) fn expr_for_reg_use(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    reg: Reg,
) -> HirExpr {
    if let Some(local) = loop_local_for_reg(lowering, block, reg) {
        return HirExpr::LocalRef(local);
    }
    let Some(values) = lowering.dataflow.use_values[instr_ref.index()]
        .fixed
        .get(reg)
    else {
        return entry_reg_expr(lowering, reg);
    };

    if values.is_empty() {
        return entry_reg_expr(lowering, reg);
    }

    if values.len() == 1 {
        let value = values
            .iter()
            .next()
            .expect("len checked above, exactly one SSA-like value exists");
        return match value {
            SsaValue::Def(def) => HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()]),
            SsaValue::Phi(phi) => HirExpr::TempRef(lowering.bindings.phi_temps[phi.index()]),
        };
    }

    unresolved_expr(format!(
        "multi-value use r{} @{}",
        reg.index(),
        instr_ref.index()
    ))
}

pub(super) fn expr_for_closure_capture(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    dst: Reg,
    source: crate::transformer::CaptureSource,
) -> HirExpr {
    match source {
        crate::transformer::CaptureSource::Reg(reg) if reg == dst => {
            let self_temp = lowering.bindings.instr_fixed_defs[instr_ref.index()]
                .first()
                .copied()
                .expect("closure writes exactly one fixed target");
            HirExpr::TempRef(self_temp)
        }
        crate::transformer::CaptureSource::Reg(reg) => {
            expr_for_reg_use(lowering, block, instr_ref, reg)
        }
        crate::transformer::CaptureSource::Upvalue(upvalue) => {
            HirExpr::UpvalueRef(UpvalueId(upvalue.index()))
        }
    }
}

/// 某些结构恢复需要读取“进入 block 时这个寄存器代表哪个稳定值”，而不是某条真实 use。
///
/// 例如值短路被恢复成 `if + assign` 后，leaf block 可能根本没有再次显式读取结果寄存器，
/// 但我们仍然需要知道“走到这个 leaf 时 merge 值应该取谁”。
pub(super) fn expr_for_reg_at_block_entry(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    reg: Reg,
) -> HirExpr {
    if let Some(local) = loop_local_for_reg(lowering, block, reg) {
        return HirExpr::LocalRef(local);
    }
    let range = lowering.cfg.blocks[block.index()].instrs;
    if range.is_empty() {
        return entry_reg_expr(lowering, reg);
    }

    let Some(values) = lowering.dataflow.reaching_values[range.start.index()]
        .fixed
        .get(reg)
    else {
        return entry_reg_expr(lowering, reg);
    };

    if values.is_empty() {
        return entry_reg_expr(lowering, reg);
    }

    if values.len() == 1 {
        let value = values
            .iter()
            .next()
            .expect("len checked above, exactly one SSA-like value exists");
        return match value {
            SsaValue::Def(def) => HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()]),
            SsaValue::Phi(phi) => HirExpr::TempRef(lowering.bindings.phi_temps[phi.index()]),
        };
    }

    unresolved_expr(format!(
        "multi-value entry r{} block#{}",
        reg.index(),
        block.index()
    ))
}

/// 某些 `goto + label` 形状需要读取“离开 block 时这个寄存器的稳定值”。
///
/// 这和普通 `expr_for_reg_use` 不同：phi edge copy 不一定对应某条真实 use，
/// 也不能只看 `incoming.defs`，否则像“从 inner loop header 直接跳回 outer header”
/// 这种边会把 block 入口 phi 的稳定值丢掉。
pub(super) fn expr_for_reg_at_block_exit(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    reg: Reg,
) -> HirExpr {
    if let Some(local) = loop_local_for_reg(lowering, block, reg) {
        return HirExpr::LocalRef(local);
    }

    let range = lowering.cfg.blocks[block.index()].instrs;
    let Some(last_instr_ref) = range.last() else {
        return entry_reg_expr(lowering, reg);
    };

    let effect = &lowering.dataflow.instr_effects[last_instr_ref.index()];
    if effect.fixed_must_defs.contains(&reg) {
        let Some(def) = fixed_def_for_reg(lowering, last_instr_ref, reg) else {
            return unresolved_expr(format!(
                "missing block-exit def r{} block#{}",
                reg.index(),
                block.index()
            ));
        };
        return HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()]);
    }

    let mut values = lowering.dataflow.reaching_values[last_instr_ref.index()]
        .fixed
        .get(reg)
        .cloned()
        .unwrap_or_default();
    if effect.fixed_may_defs.contains(&reg) {
        let Some(def) = fixed_def_for_reg(lowering, last_instr_ref, reg) else {
            return unresolved_expr(format!(
                "missing block-exit may-def r{} block#{}",
                reg.index(),
                block.index()
            ));
        };
        values.insert(SsaValue::Def(def));
    }

    if values.is_empty() {
        return entry_reg_expr(lowering, reg);
    }

    if values.len() == 1 {
        let value = values
            .iter()
            .next()
            .expect("len checked above, exactly one SSA-like value exists");
        return match value {
            SsaValue::Def(def) => HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()]),
            SsaValue::Phi(phi) => HirExpr::TempRef(lowering.bindings.phi_temps[phi.index()]),
        };
    }

    unresolved_expr(format!(
        "multi-value exit r{} block#{}",
        reg.index(),
        block.index()
    ))
}

/// 当值恢复跨过被整体吸收的 branch 区域时，内部 leaf/node block 可能不会单独物化。
///
/// 这里允许沿着单一 `DefId` 继续下钻，但只展开“可以安全重复求值”的定义。
/// 像 `call/newtable/gettable` 这类一旦重复展开就可能改写求值次数或对象身份的值，
/// 仍然退回已有 temp，避免 HIR 先天带入错误语义。
fn expr_for_reg_use_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    reg: Reg,
) -> HirExpr {
    if let Some(local) = loop_local_for_reg(lowering, block, reg) {
        return HirExpr::LocalRef(local);
    }
    let Some(values) = lowering.dataflow.use_values[instr_ref.index()]
        .fixed
        .get(reg)
    else {
        return entry_reg_expr(lowering, reg);
    };

    if values.is_empty() {
        return entry_reg_expr(lowering, reg);
    }

    if values.len() == 1 {
        let value = values
            .iter()
            .next()
            .expect("len checked above, exactly one SSA-like value exists");
        return match value {
            SsaValue::Def(def) => expr_for_dup_safe_fixed_def(lowering, *def)
                .unwrap_or_else(|| HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()])),
            SsaValue::Phi(phi) => HirExpr::TempRef(lowering.bindings.phi_temps[phi.index()]),
        };
    }

    unresolved_expr(format!(
        "multi-value use r{} @{}",
        reg.index(),
        instr_ref.index()
    ))
}

pub(super) fn expr_for_value_operand(
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

fn expr_for_value_operand_inline(
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

pub(super) fn expr_for_const(proto: &LoweredProto, const_ref: ConstRef) -> HirExpr {
    match proto.constants.common.literals.get(const_ref.index()) {
        Some(RawLiteralConst::Nil) => HirExpr::Nil,
        Some(RawLiteralConst::Boolean(value)) => HirExpr::Boolean(*value),
        Some(RawLiteralConst::Integer(value)) => HirExpr::Integer(*value),
        Some(RawLiteralConst::Number(value)) => HirExpr::Number(*value),
        Some(RawLiteralConst::String(value)) => HirExpr::String(decode_raw_string(value)),
        None => unresolved_expr(format!("const k{}", const_ref.index())),
    }
}

pub(super) fn lower_table_access_expr(
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

pub(super) fn lower_table_access_target(
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

pub(super) fn lower_branch_cond(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    cond: BranchCond,
) -> HirExpr {
    let expr = lower_branch_subject(lowering, block, instr_ref, cond);

    if cond.negated {
        HirExpr::Unary(Box::new(HirUnaryExpr {
            op: HirUnaryOpKind::Not,
            expr,
        }))
    } else {
        expr
    }
}

/// 这里返回“被分支拿来判断 truthiness/比较关系的原始值”，不附带控制流反转。
///
/// `a and b` / `a or b` 这种值级短路要保留操作数本身，而不是把 `negated`
/// 包进去，所以需要和 `lower_branch_cond` 分开。
pub(super) fn lower_branch_subject(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    cond: BranchCond,
) -> HirExpr {
    match cond.operands {
        BranchOperands::Unary(operand) => match cond.predicate {
            BranchPredicate::Truthy => lower_cond_operand(lowering, block, instr_ref, operand),
            _ => unresolved_expr("unsupported unary branch predicate"),
        },
        BranchOperands::Binary(lhs, rhs) => HirExpr::Binary(Box::new(HirBinaryExpr {
            op: match cond.predicate {
                BranchPredicate::Eq => HirBinaryOpKind::Eq,
                BranchPredicate::Lt => HirBinaryOpKind::Lt,
                BranchPredicate::Le => HirBinaryOpKind::Le,
                BranchPredicate::Truthy => {
                    return unresolved_expr("unsupported truthy binary branch");
                }
            },
            lhs: lower_cond_operand(lowering, block, instr_ref, lhs),
            rhs: lower_cond_operand(lowering, block, instr_ref, rhs),
        })),
    }
}

pub(super) fn lower_branch_subject_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    cond: BranchCond,
) -> HirExpr {
    match cond.operands {
        BranchOperands::Unary(operand) => match cond.predicate {
            BranchPredicate::Truthy => {
                lower_cond_operand_inline(lowering, block, instr_ref, operand)
            }
            _ => unresolved_expr("unsupported unary branch predicate"),
        },
        BranchOperands::Binary(lhs, rhs) => HirExpr::Binary(Box::new(HirBinaryExpr {
            op: match cond.predicate {
                BranchPredicate::Eq => HirBinaryOpKind::Eq,
                BranchPredicate::Lt => HirBinaryOpKind::Lt,
                BranchPredicate::Le => HirBinaryOpKind::Le,
                BranchPredicate::Truthy => {
                    return unresolved_expr("unsupported truthy binary branch");
                }
            },
            lhs: lower_cond_operand_inline(lowering, block, instr_ref, lhs),
            rhs: lower_cond_operand_inline(lowering, block, instr_ref, rhs),
        })),
    }
}

pub(super) fn lower_unary_op(op: UnaryOpKind) -> HirUnaryOpKind {
    match op {
        UnaryOpKind::Not => HirUnaryOpKind::Not,
        UnaryOpKind::Neg => HirUnaryOpKind::Neg,
        UnaryOpKind::BitNot => HirUnaryOpKind::BitNot,
        UnaryOpKind::Length => HirUnaryOpKind::Length,
    }
}

pub(super) fn lower_binary_op(op: BinaryOpKind) -> HirBinaryOpKind {
    match op {
        BinaryOpKind::Add => HirBinaryOpKind::Add,
        BinaryOpKind::Sub => HirBinaryOpKind::Sub,
        BinaryOpKind::Mul => HirBinaryOpKind::Mul,
        BinaryOpKind::Div => HirBinaryOpKind::Div,
        BinaryOpKind::FloorDiv => HirBinaryOpKind::FloorDiv,
        BinaryOpKind::Mod => HirBinaryOpKind::Mod,
        BinaryOpKind::Pow => HirBinaryOpKind::Pow,
        BinaryOpKind::BitAnd => HirBinaryOpKind::BitAnd,
        BinaryOpKind::BitOr => HirBinaryOpKind::BitOr,
        BinaryOpKind::BitXor => HirBinaryOpKind::BitXor,
        BinaryOpKind::Shl => HirBinaryOpKind::Shl,
        BinaryOpKind::Shr => HirBinaryOpKind::Shr,
    }
}

pub(super) fn is_multiret_results(results: crate::transformer::ResultPack) -> bool {
    matches!(results, crate::transformer::ResultPack::Open(_))
}

/// 尝试把一个固定定义直接解释成 HIR 表达式。
///
/// 这主要服务 merge 点上的值恢复。我们只在“一个 def 能稳定对应一个值表达式”时
/// 返回 `Some`，否则宁可交回上层继续保守退化，也不在这里伪造来源。
pub(super) fn expr_for_fixed_def(lowering: &ProtoLowering<'_>, def_id: DefId) -> Option<HirExpr> {
    if let Some(expr) = expr_for_dup_safe_fixed_def(lowering, def_id) {
        return Some(expr);
    }

    let def = lowering.dataflow.defs.get(def_id.index())?;
    let instr = lowering.proto.instrs.get(def.instr.index())?;

    match instr {
        LowInstr::GetTable(get_table) if get_table.dst == def.reg => {
            Some(lower_table_access_expr_inline(
                lowering,
                def.block,
                def.instr,
                get_table.base,
                get_table.key,
            ))
        }
        LowInstr::NewTable(new_table) if new_table.dst == def.reg => {
            Some(HirExpr::TableConstructor(Box::default()))
        }
        LowInstr::Call(call) => expr_for_fixed_call(lowering, def.block, def.instr, call, def.reg),
        LowInstr::VarArg(vararg) => expr_for_fixed_vararg(vararg.results, def.reg),
        LowInstr::Closure(closure) if closure.dst == def.reg => {
            Some(HirExpr::Closure(Box::new(HirClosureExpr {
                proto: lowering.child_refs[closure.proto.index()],
                captures: closure
                    .captures
                    .iter()
                    .map(|capture| HirCapture {
                        value: match capture.source {
                            crate::transformer::CaptureSource::Reg(reg) if reg == closure.dst => {
                                HirExpr::TempRef(lowering.bindings.fixed_temps[def_id.index()])
                            }
                            crate::transformer::CaptureSource::Reg(reg) => {
                                expr_for_reg_use_inline(lowering, def.block, def.instr, reg)
                            }
                            crate::transformer::CaptureSource::Upvalue(upvalue) => {
                                HirExpr::UpvalueRef(UpvalueId(upvalue.index()))
                            }
                        },
                    })
                    .collect(),
            })))
        }
        LowInstr::GenericForCall(for_call) => expr_for_generic_for_call(for_call.results, def.reg),
        LowInstr::SetUpvalue(_)
        | LowInstr::SetTable(_)
        | LowInstr::SetList(_)
        | LowInstr::TailCall(_)
        | LowInstr::Return(_)
        | LowInstr::Close(_)
        | LowInstr::NumericForInit(_)
        | LowInstr::NumericForLoop(_)
        | LowInstr::GenericForLoop(_)
        | LowInstr::Jump(_)
        | LowInstr::Branch(_) => None,
        _ => None,
    }
}

/// 这类定义可以安全地在表达式里重复展开，不会额外增加副作用，也不会改变
/// `newtable/closure/call` 这类“每次求值都不一样”的语义。
pub(super) fn expr_for_dup_safe_fixed_def(
    lowering: &ProtoLowering<'_>,
    def_id: DefId,
) -> Option<HirExpr> {
    let def = lowering.dataflow.defs.get(def_id.index())?;
    let instr = lowering.proto.instrs.get(def.instr.index())?;

    match instr {
        LowInstr::Move(move_instr) if move_instr.dst == def.reg => Some(expr_for_reg_use_inline(
            lowering,
            def.block,
            def.instr,
            move_instr.src,
        )),
        LowInstr::LoadNil(load_nil) if reg_in_range(load_nil.dst, def.reg) => Some(HirExpr::Nil),
        LowInstr::LoadBool(load_bool) if load_bool.dst == def.reg => {
            Some(HirExpr::Boolean(load_bool.value))
        }
        LowInstr::LoadConst(load_const) if load_const.dst == def.reg => {
            Some(expr_for_const(lowering.proto, load_const.value))
        }
        LowInstr::LoadInteger(load_integer) if load_integer.dst == def.reg => {
            Some(HirExpr::Integer(load_integer.value))
        }
        LowInstr::LoadNumber(load_number) if load_number.dst == def.reg => {
            Some(HirExpr::Number(load_number.value))
        }
        LowInstr::UnaryOp(unary) if unary.dst == def.reg => {
            Some(HirExpr::Unary(Box::new(HirUnaryExpr {
                op: lower_unary_op(unary.op),
                expr: expr_for_reg_use_inline(lowering, def.block, def.instr, unary.src),
            })))
        }
        LowInstr::BinaryOp(binary) if binary.dst == def.reg => {
            Some(HirExpr::Binary(Box::new(HirBinaryExpr {
                op: lower_binary_op(binary.op),
                lhs: expr_for_value_operand_inline(lowering, def.block, def.instr, binary.lhs),
                rhs: expr_for_value_operand_inline(lowering, def.block, def.instr, binary.rhs),
            })))
        }
        LowInstr::Concat(concat) if concat.dst == def.reg => {
            let value = (0..concat.src.len)
                .map(|offset| {
                    expr_for_reg_use_inline(
                        lowering,
                        def.block,
                        def.instr,
                        Reg(concat.src.start.index() + offset),
                    )
                })
                .reduce(|lhs, rhs| {
                    HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Concat,
                        lhs,
                        rhs,
                    }))
                })
                .unwrap_or_else(|| unresolved_expr("concat empty source"));
            Some(value)
        }
        LowInstr::GetUpvalue(get_upvalue) if get_upvalue.dst == def.reg => {
            Some(HirExpr::UpvalueRef(UpvalueId(get_upvalue.src.index())))
        }
        _ => None,
    }
}

/// `Open(start)` 不是“只有一个开放尾值”，而是“从 start 到 top 的整段值包”。
///
/// 因此这里会先找出真正的开放尾部起点：若 open def 从更晚的寄存器开始，那么
/// `start..tail_start-1` 这一段仍然要按固定值逐个吐出来，最后再接上 open tail。
fn resolve_open_pack_tail(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    start_reg: Reg,
) -> Option<(Reg, HirExpr)> {
    let defs = &lowering.dataflow.open_use_defs[instr_ref.index()];
    if defs.len() == 1 {
        let def = defs
            .iter()
            .next()
            .expect("len checked above, exactly one reaching open def exists");
        let open_def = lowering.dataflow.open_defs.get(def.index())?;
        if open_def.start_reg.index() < start_reg.index() {
            return None;
        }
        return Some((
            open_def.start_reg,
            HirExpr::TempRef(lowering.bindings.open_temps[def.index()]),
        ));
    }

    if defs.is_empty()
        && lowering.proto.signature.is_vararg
        && start_reg.index() == usize::from(lowering.proto.signature.num_params)
    {
        return Some((start_reg, HirExpr::VarArg));
    }

    None
}

fn lower_open_value_pack<F>(
    lowering: &ProtoLowering<'_>,
    start_reg: Reg,
    instr_ref: InstrRef,
    mut lower_reg: F,
) -> Vec<HirExpr>
where
    F: FnMut(Reg) -> HirExpr,
{
    let Some((tail_start, tail_expr)) = resolve_open_pack_tail(lowering, instr_ref, start_reg)
    else {
        return vec![unresolved_expr(format!(
            "open-pack r{} @{}",
            start_reg.index(),
            instr_ref.index()
        ))];
    };

    let mut values = (start_reg.index()..tail_start.index())
        .map(|index| lower_reg(Reg(index)))
        .collect::<Vec<_>>();
    values.push(tail_expr);
    values
}

fn entry_reg_expr(lowering: &ProtoLowering<'_>, reg: Reg) -> HirExpr {
    if reg.index() < lowering.bindings.params.len() {
        HirExpr::ParamRef(lowering.bindings.params[reg.index()])
    } else {
        unresolved_expr(format!("entry-reg r{}", reg.index()))
    }
}

fn loop_local_for_reg(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    reg: Reg,
) -> Option<crate::hir::common::LocalId> {
    lowering
        .bindings
        .block_local_regs
        .get(&block)
        .and_then(|locals| locals.get(&reg))
        .copied()
}

fn fixed_def_for_reg(lowering: &ProtoLowering<'_>, instr_ref: InstrRef, reg: Reg) -> Option<DefId> {
    lowering.dataflow.instr_defs[instr_ref.index()]
        .iter()
        .copied()
        .find(|def_id| lowering.dataflow.defs[def_id.index()].reg == reg)
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

fn lower_table_access_expr_inline(
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

fn lower_cond_operand(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    operand: CondOperand,
) -> HirExpr {
    match operand {
        CondOperand::Reg(reg) => expr_for_reg_use(lowering, block, instr_ref, reg),
        CondOperand::Const(const_ref) => expr_for_const(lowering.proto, const_ref),
        CondOperand::Integer(value) => HirExpr::Integer(value),
        CondOperand::Number(value) => HirExpr::Number(value.to_f64()),
    }
}

fn lower_cond_operand_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    operand: CondOperand,
) -> HirExpr {
    match operand {
        CondOperand::Reg(reg) => expr_for_reg_use_inline(lowering, block, instr_ref, reg),
        CondOperand::Const(const_ref) => expr_for_const(lowering.proto, const_ref),
        CondOperand::Integer(value) => HirExpr::Integer(value),
        CondOperand::Number(value) => HirExpr::Number(value.to_f64()),
    }
}

fn expr_for_fixed_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    call: &crate::transformer::CallInstr,
    reg: Reg,
) -> Option<HirExpr> {
    let ResultPack::Fixed(results) = call.results else {
        return None;
    };
    if results.len != 1 || results.start != reg {
        return None;
    }

    Some(HirExpr::Call(Box::new(HirCallExpr {
        callee: expr_for_reg_use_inline(lowering, block, instr_ref, call.callee),
        args: lower_value_pack_inline(lowering, block, instr_ref, call.args),
        multiret: false,
        method: matches!(call.kind, CallKind::Method),
    })))
}

fn expr_for_fixed_vararg(results: ResultPack, reg: Reg) -> Option<HirExpr> {
    let ResultPack::Fixed(range) = results else {
        return None;
    };
    if range.len == 1 && range.start == reg {
        Some(HirExpr::VarArg)
    } else {
        None
    }
}

fn expr_for_generic_for_call(results: ResultPack, reg: Reg) -> Option<HirExpr> {
    let ResultPack::Fixed(range) = results else {
        return None;
    };
    if range.len == 1 && range.start == reg {
        Some(unresolved_expr("generic-for-call"))
    } else {
        None
    }
}

fn reg_in_range(range: crate::transformer::RegRange, reg: Reg) -> bool {
    reg.index() >= range.start.index() && reg.index() < range.start.index() + range.len
}

pub(super) fn lower_value_pack(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    pack: crate::transformer::ValuePack,
) -> Vec<HirExpr> {
    let (mut values, trailing_multivalue) =
        lower_value_pack_components(lowering, block, instr_ref, pack);
    if let Some(trailing) = trailing_multivalue {
        values.push(trailing);
    }
    values
}

pub(super) fn lower_value_pack_components(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    pack: crate::transformer::ValuePack,
) -> (Vec<HirExpr>, Option<HirExpr>) {
    match pack {
        crate::transformer::ValuePack::Fixed(range) => (
            (0..range.len)
                .map(|offset| {
                    expr_for_reg_use(
                        lowering,
                        block,
                        instr_ref,
                        Reg(range.start.index() + offset),
                    )
                })
                .collect(),
            None,
        ),
        crate::transformer::ValuePack::Open(reg) => {
            lower_open_value_pack_components(lowering, reg, instr_ref, |reg| {
                expr_for_reg_use(lowering, block, instr_ref, reg)
            })
        }
    }
}

fn lower_value_pack_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    pack: crate::transformer::ValuePack,
) -> Vec<HirExpr> {
    match pack {
        crate::transformer::ValuePack::Fixed(range) => (0..range.len)
            .map(|offset| {
                expr_for_reg_use_inline(
                    lowering,
                    block,
                    instr_ref,
                    Reg(range.start.index() + offset),
                )
            })
            .collect(),
        crate::transformer::ValuePack::Open(reg) => {
            lower_open_value_pack(lowering, reg, instr_ref, |reg| {
                expr_for_reg_use_inline(lowering, block, instr_ref, reg)
            })
        }
    }
}

fn lower_open_value_pack_components<F>(
    lowering: &ProtoLowering<'_>,
    start_reg: Reg,
    instr_ref: InstrRef,
    mut lower_reg: F,
) -> (Vec<HirExpr>, Option<HirExpr>)
where
    F: FnMut(Reg) -> HirExpr,
{
    let Some((tail_start, tail_expr)) = resolve_open_pack_tail(lowering, instr_ref, start_reg)
    else {
        return (
            vec![unresolved_expr(format!(
                "open-pack r{} @{}",
                start_reg.index(),
                instr_ref.index()
            ))],
            None,
        );
    };

    let values = (start_reg.index()..tail_start.index())
        .map(|index| lower_reg(Reg(index)))
        .collect::<Vec<_>>();
    (values, Some(tail_expr))
}
