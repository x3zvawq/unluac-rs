//! 这个子模块负责把 branch terminator 的谓词和操作数降成 HIR 条件表达式。
//!
//! 它依赖 Transformer 已经解析好的 `BranchCond`，只回答“条件本身长什么样”，不会在这里
//! 决定 if/while/短路结构应该怎么组织。
//! 例如：`if not r0 then ...` 会先在这里得到 `not r0` 的表达式形式。

use super::*;

pub(crate) fn lower_branch_cond(
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
pub(crate) fn lower_branch_subject(
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

pub(crate) fn lower_branch_subject_inline(
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
) -> HirExpr {
    match cond.operands {
        BranchOperands::Unary(operand) => match cond.predicate {
            BranchPredicate::Truthy => {
                lower_cond_operand_single_eval(lowering, block, instr_ref, operand)
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
            lhs: lower_cond_operand_single_eval(lowering, block, instr_ref, lhs),
            rhs: lower_cond_operand_single_eval(lowering, block, instr_ref, rhs),
        })),
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

fn lower_cond_operand_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    operand: CondOperand,
) -> HirExpr {
    match operand {
        CondOperand::Reg(reg) => expr_for_reg_use_inline(lowering, block, instr_ref, reg),
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
        CondOperand::Reg(reg) => expr_for_reg_use_single_eval(lowering, block, instr_ref, reg),
        CondOperand::Const(const_ref) => expr_for_const(lowering.proto, const_ref),
        CondOperand::Nil => HirExpr::Nil,
        CondOperand::Boolean(value) => HirExpr::Boolean(value),
        CondOperand::Integer(value) => HirExpr::Integer(value),
        CondOperand::Number(value) => HirExpr::Number(value.to_f64()),
    }
}
