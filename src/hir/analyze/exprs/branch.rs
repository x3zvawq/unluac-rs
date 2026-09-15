//! 这个子模块负责把 branch terminator 的谓词和操作数降成 HIR 条件表达式。
//!
//! 它依赖 Transformer 已经解析好的 `BranchCond`，只回答“条件本身长什么样”，不会在这里
//! 决定 if/while/短路结构应该怎么组织。
//! 例如：`if not r0 then ...` 会先在这里得到 `not r0` 的表达式形式。
//! Subject 同时签发原 operand / 合成 predicate 来源：比较结果虽为 Boolean，
//! 条件跳转本身并不证明发生过 Boolean 值写回，后续 Decision 不能混用这两种事实。
//! 原右侧快照早于左侧 CALL 时，使用显式 Gt/Ge 保存准备顺序。例如原 `global > f()`
//! 的 VM 谓词是 LT(call_result, global_snapshot)；HIR 不能强制留下占槽到分支内的别名。

use super::*;
use crate::hir::common::{HirSourceSite, TempId};

pub(crate) fn lower_branch_cond(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    cond: BranchCond,
) -> HirExpr {
    let (expr, _) = lower_branch_subject(lowering, block, instr_ref, cond);

    if cond.negated {
        HirExpr::Unary(Box::new(HirUnaryExpr {
            source_site: None,
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
pub(crate) fn lower_branch_subject(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    cond: BranchCond,
) -> (HirExpr, crate::hir::HirDecisionTestSource) {
    lower_branch_subject_with(
        HirSourceSite {
            proto: lowering.id,
            instr: instr_ref,
        },
        cond,
        comparison_reads_right_first(lowering, instr_ref, cond),
        |operand| lower_cond_operand(lowering, block, instr_ref, operand),
    )
}

/// 值型短路恢复需要的是“当前这一跳可以直接表达”的 subject，而不是“可任意复制”的值。
///
/// 例如 `mark("a", x)` 这种调用不能走 dup-safe inline，因为复制它会改变求值次数；
/// 但当它正好就是当前短路节点那一次 truthiness test 时，仍然应该把它恢复成源码里的
/// 操作数表达式，而不是先退回 temp，再被结构层保守地降成 `if` 壳。
pub(crate) fn lower_branch_subject_single_eval(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    cond: BranchCond,
) -> (HirExpr, crate::hir::HirDecisionTestSource) {
    lower_branch_subject_with(
        HirSourceSite {
            proto: lowering.id,
            instr: instr_ref,
        },
        cond,
        comparison_reads_right_first(lowering, instr_ref, cond),
        |operand| lower_cond_operand_single_eval(lowering, block, instr_ref, operand),
    )
}

/// 只为当前测试的 direct CALL epoch 消费已冻结的原 home 覆盖证明。
/// 调用表达式展开后仍须由调用方匹配此测试；不能沿 MOVE 借另一个槽的旧 producer。
pub(in crate::hir::analyze) fn branch_call_result_ending_after_test(
    lowering: &ProtoLowering<'_>,
    instr: InstrRef,
    frontiers: &crate::structure::RootOverwriteFrontiers,
) -> Option<DefId> {
    let LowInstr::Branch(branch) = &lowering.proto.instrs[instr.index()] else {
        return None;
    };
    let BranchSubject::Truthy(CondOperand::Reg(reg)) = branch.cond.subject else {
        return None;
    };
    let SsaValue::Def(def) = lowering.dataflow.use_value(instr, reg) else {
        return None;
    };
    let uses = &lowering.dataflow.def_uses[def.index()];
    (matches!(
        lowering.proto.instrs[lowering.dataflow.def_instr(def).index()],
        LowInstr::Call(_)
    ) && uses.len() == 1
        && uses[0].instr == instr
        && (frontiers
            .for_def(def)
            .is_some_and(|frontier| frontier.home() == reg)
            || lowering
                .promotion_facts
                .call_result_root_ends_after_value_use(lowering.bindings.fixed_temps[def.index()])))
    .then_some(def)
}

/// 原内嵌字面量不占准备槽，可以右置；其余只恢复同块、单用且无开放引用的读取
/// 快照→CALL。已有源码 local、Phi、MOVE 或跨块值不靠指令号排序；方向改变不删除
/// producer，后续内联仍消费原事件与根事务。
fn comparison_reads_right_first(
    lowering: &ProtoLowering<'_>,
    instr: InstrRef,
    cond: BranchCond,
) -> bool {
    let BranchSubject::Compare {
        predicate: BranchPredicate::Lt | BranchPredicate::Le,
        lhs,
        rhs: CondOperand::Reg(rhs),
    } = cond.subject
    else {
        return false;
    };
    let CondOperand::Reg(lhs) = lhs else {
        return match lhs {
            CondOperand::Integer(_) | CondOperand::Number(_) => true,
            CondOperand::Const(key) => matches!(
                lowering.proto.constants.get(key.index()),
                Some(
                    RawLiteralConst::Integer(_)
                        | RawLiteralConst::Number(_)
                        | RawLiteralConst::String(_)
                )
            ),
            _ => false,
        };
    };
    let block = lowering.cfg.instr_to_block[instr.index()];
    let anonymous_single_use = |def: DefId| {
        let temp = lowering.bindings.fixed_temps[def.index()];
        let uses = &lowering.dataflow.def_uses[def.index()];
        temp == TempId(def.index())
            && matches!(lowering.bindings.expr_for_temp(temp), HirExpr::TempRef(_))
            && lowering.bindings.temp_debug_locals[temp.index()].is_none()
            && uses.len() == 1
            && uses[0].instr == instr
            && lowering.dataflow.def_phi_uses[def.index()].is_empty()
    };
    let literal_load = |site: InstrRef| match &lowering.proto.instrs[site.index()] {
        LowInstr::LoadInteger(_) | LowInstr::LoadNumber(_) => true,
        LowInstr::LoadConst(load) => matches!(
            lowering.proto.constants.get(load.value.index()),
            Some(
                RawLiteralConst::Integer(_)
                    | RawLiteralConst::Number(_)
                    | RawLiteralConst::String(_)
            )
        ),
        _ => false,
    };
    let direct_home = |reg| {
        let value = lowering.dataflow.use_value(instr, reg);
        let expression = if let Some(local) = lowering.bindings.local_for_reg_in_block(block, reg) {
            HirExpr::LocalRef(local)
        } else {
            match value {
                SsaValue::Def(def) => lowering
                    .bindings
                    .expr_for_temp(lowering.bindings.fixed_temps[def.index()]),
                SsaValue::Phi(phi) => lowering.bindings.expr_for_phi(phi),
                SsaValue::Entry(_) => {
                    HirExpr::ParamRef(*lowering.bindings.params.get(reg.index())?)
                }
            }
        };
        match expression {
            HirExpr::LocalRef(local) => lowering.promotion_facts.trusted_local_home_slot(local),
            HirExpr::ParamRef(param) => lowering.promotion_facts.trusted_param_home_slot(param),
            HirExpr::TempRef(temp)
                if match value {
                    // Phi/carried 身份及已有其它消费者的值不是一次新 operand 准备。
                    // 它们可能到 AST 才物化；原共享绑定身份不依赖 HIR locals pass 的时点。
                    SsaValue::Phi(_) => true,
                    SsaValue::Def(def) => {
                        temp != TempId(def.index())
                            || lowering.dataflow.def_uses[def.index()].len() > 1
                            || !lowering.dataflow.def_phi_uses[def.index()].is_empty()
                    }
                    SsaValue::Entry(_) => false,
                } =>
            {
                lowering.promotion_facts.trusted_temp_home_slot(temp)
            }
            _ => None,
        }
        .filter(|home| home.slot() == reg.index())
    };
    let Some(layout) = lowering
        .promotion_facts
        .native_binary_layout_at(HirSourceSite {
            proto: lowering.id,
            instr,
        })
    else {
        return false;
    };
    let left_value = lowering.dataflow.use_value(instr, lhs);
    let right_value = lowering.dataflow.use_value(instr, rhs);
    let available_before = |value, preparation: InstrRef| match value {
        SsaValue::Def(def) => {
            lowering.dataflow.def_block(def) != block
                || lowering.dataflow.def_instr(def).index() < preparation.index()
        }
        SsaValue::Phi(_) | SsaValue::Entry(_) => true,
    };
    // 既有低槽引用不复制到 scratch。常量输入或 Length 结果仍在原高槽准备，
    // 因此可按 `value > constant` / `#value >= index` 发射，且不改变任何准备写。
    if let SsaValue::Def(left) = left_value
        && lowering.dataflow.def_block(left) == block
        && anonymous_single_use(left)
        && literal_load(lowering.dataflow.def_instr(left))
        && available_before(right_value, lowering.dataflow.def_instr(left))
        && let Some(right) = direct_home(rhs)
        && layout.rhs == Some(right)
        && layout.lhs.is_some_and(|left| right.slot() < left.slot())
    {
        return true;
    }
    if let SsaValue::Def(right) = right_value
        && lowering.dataflow.def_block(right) == block
        && anonymous_single_use(right)
        && available_before(left_value, lowering.dataflow.def_instr(right))
        && matches!(&lowering.proto.instrs[lowering.dataflow.def_instr(right).index()],
            LowInstr::UnaryOp(unary) if unary.op == UnaryOpKind::Length)
        && let Some(left) = direct_home(lhs)
        && layout.lhs == Some(left)
        && layout.rhs.is_some_and(|right| left.slot() < right.slot())
    {
        return true;
    }
    let (SsaValue::Def(left), SsaValue::Def(right)) = (left_value, right_value) else {
        return false;
    };
    let left_site = lowering.dataflow.def_instr(left);
    let right_site = lowering.dataflow.def_instr(right);
    if lowering.dataflow.def_block(right) != block || lowering.dataflow.def_block(left) != block {
        return false;
    }
    // `f() > 1000` 的 LOADK 在 CALL 之后；打印成 `1000 < f()` 会把该物理准备
    // 移到调用前。此处保留原方向，不能因为常量值可重排就忽略它原来占用的槽。
    if right_site.index() < left_site.index()
        && matches!(lowering.proto.instrs[right_site.index()], LowInstr::Call(_))
        && anonymous_single_use(left)
        && anonymous_single_use(right)
        && literal_load(left_site)
    {
        return true;
    }
    right_site.index() < left_site.index()
        && anonymous_single_use(right)
        && matches!(lowering.proto.instrs[left_site.index()], LowInstr::Call(_))
        && matches!(
            lowering.proto.instrs[right_site.index()],
            LowInstr::GetTable(_)
        )
        && lowering
            .promotion_facts
            .operation_result_reference_unaliased(HirSourceSite {
                proto: lowering.id,
                instr: right_site,
            })
}

fn lower_branch_subject_with(
    source: HirSourceSite,
    cond: BranchCond,
    reads_right_first: bool,
    mut lower_operand: impl FnMut(CondOperand) -> HirExpr,
) -> (HirExpr, crate::hir::HirDecisionTestSource) {
    use crate::hir::HirDecisionTestSource;
    match cond.subject {
        BranchSubject::Truthy(operand) => (lower_operand(operand), HirDecisionTestSource::Value),
        BranchSubject::Compare {
            predicate,
            lhs,
            rhs,
        } => {
            let (op, lhs, rhs) = if reads_right_first {
                (
                    match predicate {
                        BranchPredicate::Lt => HirBinaryOpKind::Gt,
                        BranchPredicate::Le => HirBinaryOpKind::Ge,
                        BranchPredicate::Eq => unreachable!("equality has no reversed ordering"),
                    },
                    rhs,
                    lhs,
                )
            } else {
                (
                    match predicate {
                        BranchPredicate::Eq => HirBinaryOpKind::Eq,
                        BranchPredicate::Lt => HirBinaryOpKind::Lt,
                        BranchPredicate::Le => HirBinaryOpKind::Le,
                    },
                    lhs,
                    rhs,
                )
            };
            (
                HirExpr::Binary(Box::new(HirBinaryExpr {
                    source_site: Some(source),
                    op,
                    lhs: lower_operand(lhs),
                    rhs: lower_operand(rhs),
                })),
                HirDecisionTestSource::Predicate,
            )
        }
    }
}

pub(crate) fn lower_unary_op(op: UnaryOpKind) -> HirUnaryOpKind {
    match op {
        UnaryOpKind::Not => HirUnaryOpKind::Not,
        UnaryOpKind::Neg => HirUnaryOpKind::Neg,
        UnaryOpKind::BitNot => HirUnaryOpKind::BitNot,
        UnaryOpKind::Length => HirUnaryOpKind::Length,
    }
}

pub(crate) fn lower_binary_op(op: BinaryOpKind) -> HirBinaryOpKind {
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

fn lower_cond_operand(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    operand: CondOperand,
) -> HirExpr {
    match operand {
        CondOperand::Reg(reg) => expr_for_reg_use(lowering, block, instr_ref, reg),
        CondOperand::Const(const_ref) => expr_for_const(lowering.proto, const_ref),
        CondOperand::Nil => HirExpr::Nil,
        CondOperand::Boolean(value) => HirExpr::Boolean(value),
        CondOperand::Integer(value) => HirExpr::Integer(value),
        CondOperand::Number(value) => HirExpr::Number(value.to_f64()),
    }
}

fn lower_cond_operand_single_eval(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    operand: CondOperand,
) -> HirExpr {
    match operand {
        CondOperand::Reg(reg) => {
            expr_for_reg_use_single_eval_with_call_policy(lowering, block, instr_ref, reg, false)
        }
        CondOperand::Const(const_ref) => expr_for_const(lowering.proto, const_ref),
        CondOperand::Nil => HirExpr::Nil,
        CondOperand::Boolean(value) => HirExpr::Boolean(value),
        CondOperand::Integer(value) => HirExpr::Integer(value),
        CondOperand::Number(value) => HirExpr::Number(value.to_f64()),
    }
}
