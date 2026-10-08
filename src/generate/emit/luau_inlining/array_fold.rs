//! 核对数组遍历的最终函数体和双结果调用合同。
//! 比较完整 HIR 模板，复用 pinned 编译成本；实参不得引入额外的常量专化或参数槽复用。

use super::*;
use crate::hir::HirBinaryOpKind;
use crate::hir::luau_inlining::{ArrayFoldTemplate, array_fold_template};

fn operation(op: AstBinaryOpKind) -> Option<HirBinaryOpKind> {
    Some(match op {
        AstBinaryOpKind::Add => HirBinaryOpKind::Add,
        AstBinaryOpKind::Sub => HirBinaryOpKind::Sub,
        AstBinaryOpKind::Eq => HirBinaryOpKind::Eq,
        AstBinaryOpKind::Lt => HirBinaryOpKind::Lt,
        AstBinaryOpKind::Le => HirBinaryOpKind::Le,
        AstBinaryOpKind::Gt => HirBinaryOpKind::Gt,
        AstBinaryOpKind::Ge => HirBinaryOpKind::Ge,
        _ => return None,
    })
}

fn shape(func: &AstFunctionExpr) -> Option<ArrayFoldTemplate> {
    let mut initializers = Vec::new();
    let mut count = 0;
    for stmt in &func.body.stmts {
        let AstStmt::LocalDecl(decl) = stmt else {
            break;
        };
        if decl.bindings.len() != decl.values.len() {
            return None;
        }
        initializers.extend(decl.bindings.iter().zip(&decl.values));
        count += 1;
    }
    let [(selected, initial), (state, value)] = initializers.as_slice() else {
        return None;
    };
    let [AstStmt::NumericFor(loop_), AstStmt::Return(ret)] = &func.body.stmts[count..] else {
        return None;
    };
    let selected = selected.id.to_name_ref();
    let state = state.id.to_name_ref();
    let param = |index| AstExpr::Var(AstNameRef::Param(func.params[index]));
    let AstExpr::Unary(limit) = &loop_.limit else {
        return None;
    };
    let [
        AstStmt::Assign(index),
        AstStmt::If(exit),
        AstStmt::Assign(update),
    ] = loop_.body.stmts.as_slice()
    else {
        return None;
    };
    let AstExpr::Binary(compare) = &exit.cond else {
        return None;
    };
    let [AstExpr::Binary(binary)] = update.values.as_slice() else {
        return None;
    };
    let lookup = |expr: &AstExpr| {
        matches!(expr, AstExpr::IndexAccess(access)
            if access.base == param(0)
                && access.index == AstExpr::Var(loop_.binding.to_name_ref()))
    };
    if **value != param(1)
        || limit.op != AstUnaryOpKind::Length
        || limit.expr != param(0)
        || index.targets.as_slice() != [AstLValue::Name(selected.clone())]
        || index.values.as_slice() != [AstExpr::Var(loop_.binding.to_name_ref())]
        || !lookup(&compare.lhs)
        || compare.rhs != AstExpr::Var(state.clone())
        || !compare.original_operation
        || !matches!(exit.then_block.stmts.as_slice(), [AstStmt::Break])
        || exit
            .else_block
            .as_ref()
            .is_some_and(|other| !other.stmts.is_empty())
        || update.targets.as_slice() != [AstLValue::Name(state.clone())]
        || binary.lhs != AstExpr::Var(state.clone())
        || !lookup(&binary.rhs)
        || !binary.original_operation
        || ret.values.as_slice() != [AstExpr::Var(selected), AstExpr::Var(state)]
    {
        return None;
    }
    Some(ArrayFoldTemplate {
        initial: counter_repeat::integer(initial)?,
        start: counter_repeat::integer(&loop_.start)?,
        step: counter_repeat::integer(&loop_.step)?,
        comparison: operation(compare.op)?,
        update: operation(binary.op)?,
    })
}

pub(super) fn body(func: &AstFunctionExpr, proto: &crate::hir::HirProto) -> bool {
    func.function == proto.id
        && func.params.len() == 2
        && array_fold_template(proto)
            .is_some_and(|expected| shape(func).as_ref() == Some(&expected))
        && constant_control::CostAnalysis::new(func)
            .cost(None)
            .is_some_and(|cost| cost.permits_inline(cost))
}

pub(super) fn arguments(args: &[AstExpr]) -> bool {
    args.len() == 2
        && args
            .iter()
            .all(|arg| matches!(arg, AstExpr::IndexAccess(_) | AstExpr::FieldAccess(_)))
}
