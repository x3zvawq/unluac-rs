//! 这个子模块负责把 branch terminator 的谓词和操作数降成 HIR 条件表达式。
//!
//! 它依赖 Transformer 已经解析好的 `BranchCond`，只回答“条件本身长什么样”，不会在这里
//! 决定 if/while/短路结构应该怎么组织。
//! 例如：`if not r0 then ...` 会先在这里得到 `not r0` 的表达式形式。
//! Subject 同时签发原 operand / 合成 predicate 来源：比较结果虽为 Boolean，
//! 条件跳转本身并不证明发生过 Boolean 值写回，后续 Decision 不能混用这两种事实。

use super::*;
use crate::hir::common::HirSourceSite;

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
        |operand| lower_cond_operand_single_eval(lowering, block, instr_ref, operand),
    )
}

/// 只为当前测试的 direct CALL epoch 消费已冻结的原 home 覆盖证明。
/// 调用表达式展开后仍须由调用方匹配此测试；不能沿 MOVE 借另一个槽的旧 producer。
pub(in crate::hir::analyze) fn branch_call_result_root_ends_after_test(
    lowering: &ProtoLowering<'_>,
    instr: InstrRef,
    frontiers: &crate::structure::RootOverwriteFrontiers,
) -> bool {
    let LowInstr::Branch(branch) = &lowering.proto.instrs[instr.index()] else {
        return false;
    };
    let BranchSubject::Truthy(CondOperand::Reg(reg)) = branch.cond.subject else {
        return false;
    };
    let SsaValue::Def(def) = lowering.dataflow.use_value(instr, reg) else {
        return false;
    };
    let uses = &lowering.dataflow.def_uses[def.index()];
    matches!(
        lowering.proto.instrs[lowering.dataflow.def_instr(def).index()],
        LowInstr::Call(_)
    ) && uses.len() == 1
        && uses[0].instr == instr
        && (frontiers
            .for_def(def)
            .is_some_and(|frontier| frontier.home() == reg)
            || lowering
                .promotion_facts
                .call_result_root_ends_after_value_use(lowering.bindings.fixed_temps[def.index()]))
}

fn lower_branch_subject_with(
    source: HirSourceSite,
    cond: BranchCond,
    mut lower_operand: impl FnMut(CondOperand) -> HirExpr,
) -> (HirExpr, crate::hir::HirDecisionTestSource) {
    use crate::hir::HirDecisionTestSource;
    match cond.subject {
        BranchSubject::Truthy(operand) => (lower_operand(operand), HirDecisionTestSource::Value),
        BranchSubject::Compare {
            predicate,
            lhs,
            rhs,
        } => (
            HirExpr::Binary(Box::new(HirBinaryExpr {
                source_site: Some(source),
                op: match predicate {
                    BranchPredicate::Eq => HirBinaryOpKind::Eq,
                    BranchPredicate::Lt => HirBinaryOpKind::Lt,
                    BranchPredicate::Le => HirBinaryOpKind::Le,
                },
                lhs: lower_operand(lhs),
                rhs: lower_operand(rhs),
            })),
            HirDecisionTestSource::Predicate,
        ),
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
