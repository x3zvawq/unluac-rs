//! 在最终 AST 核对数值 repeat 模板及各参数配置的内联、循环展开合同。
//! 更新与索引控制逐项对照 HIR；成本消费共用的 pinned Luau 模型。

use super::counter_repeat::integer;
use super::*;
use crate::hir::luau_inlining::{NumericRepeatTemplate, numeric_repeat_template};

fn update(stmt: &AstStmt, state: &AstNameRef) -> Option<i64> {
    let AstStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([AstLValue::Name(target)], [AstExpr::Binary(binary)]) =
        (assign.targets.as_slice(), assign.values.as_slice())
    else {
        return None;
    };
    if target != state
        || binary.op != AstBinaryOpKind::Add
        || !binary.original_operation
        || binary.lhs != AstExpr::Var(state.clone())
    {
        return None;
    }
    integer(&binary.rhs)
}

fn shape(func: &AstFunctionExpr) -> Option<(NumericRepeatTemplate, &AstNumericFor)> {
    let [
        AstStmt::LocalDecl(decl),
        AstStmt::NumericFor(loop_),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return None;
    };
    let ([binding], [initial]) = (decl.bindings.as_slice(), decl.values.as_slice()) else {
        return None;
    };
    let state = binding.id.to_name_ref();
    let param = |index| AstExpr::Var(AstNameRef::Param(func.params[index]));
    let [first, AstStmt::Repeat(repeat)] = loop_.body.stmts.as_slice() else {
        return None;
    };
    let [AstStmt::If(guard), tail] = repeat.body.stmts.as_slice() else {
        return None;
    };
    if repeat.cond != param(1)
        || guard.cond != param(0)
        || binding.id == loop_.binding
        || ret.values.as_slice() != [AstExpr::Var(state.clone())]
        || guard
            .else_block
            .as_ref()
            .is_some_and(|block| !block.stmts.is_empty())
    {
        return None;
    }
    let (lookup, continued, rejected) = match guard.then_block.stmts.as_slice() {
        [AstStmt::If(lookup), AstStmt::If(continued)] => {
            let [rejected] = continued.else_block.as_ref()?.stmts.as_slice() else {
                return None;
            };
            (lookup, continued, rejected)
        }
        [AstStmt::If(lookup), AstStmt::If(continued), rejected]
            if continued
                .else_block
                .as_ref()
                .is_none_or(|block| block.stmts.is_empty()) =>
        {
            (lookup, continued, rejected)
        }
        _ => return None,
    };
    let AstExpr::IndexAccess(access) = &lookup.cond else {
        return None;
    };
    if access.base != param(2)
        || access.index != AstExpr::Var(state.clone())
        || !matches!(lookup.then_block.stmts.as_slice(), [AstStmt::Break])
        || lookup
            .else_block
            .as_ref()
            .is_some_and(|block| !block.stmts.is_empty())
        || continued.cond != param(0)
        || !matches!(continued.then_block.stmts.as_slice(), [AstStmt::Continue])
    {
        return None;
    }
    Some((
        NumericRepeatTemplate {
            initial: integer(initial)?,
            start: integer(&loop_.start)?,
            limit: integer(&loop_.limit)?,
            step: integer(&loop_.step)?,
            increment: update(first, &state)?,
            rejected_increment: update(rejected, &state)?,
            tail_increment: update(tail, &state)?,
        },
        loop_,
    ))
}

pub(super) fn body(func: &AstFunctionExpr, proto: &crate::hir::HirProto) -> bool {
    if func.function != proto.id
        || func.params.len() != 3
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let Some(expected) = numeric_repeat_template(proto) else {
        return false;
    };
    let Some((actual, loop_)) = shape(func) else {
        return false;
    };
    if actual != expected {
        return false;
    }
    let Some(baseline) = constant_control::cost(func, None) else {
        return false;
    };
    if baseline.permits_inline(baseline) {
        return false;
    }
    // 参数1只用作 repeat 的裸条件；CostModel 对常量和动态 local 都收取0。
    // 分别验证两种常量值，也约束同一模板的动态条件配置；循环不得另读索引变量。
    for mask in [1, 2, 3] {
        let Some(cost) = constant_control::cost(func, Some(mask)) else {
            return false;
        };
        let Some(loop_cost) = constant_control::block_cost(func, &loop_.body, Some(mask)) else {
            return false;
        };
        if !cost.permits_inline(baseline)
            || loop_cost.blocks_unroll(actual.start, actual.limit, actual.step) != (mask & 1 != 0)
        {
            return false;
        }
    }
    true
}

pub(super) fn arguments(args: &[AstExpr], nonconstant: &BTreeSet<crate::hir::LocalId>) -> bool {
    match args {
        [
            AstExpr::Boolean(false),
            AstExpr::Boolean(true),
            AstExpr::Nil | AstExpr::TableConstructor(_),
        ] => true,
        [
            AstExpr::Boolean(true),
            condition,
            AstExpr::Var(AstNameRef::Local(_)) | AstExpr::TableConstructor(_),
        ] => {
            matches!(condition, AstExpr::Boolean(_))
                || matches!(condition, AstExpr::Var(AstNameRef::Local(local)) if nonconstant.contains(local))
        }
        _ => false,
    }
}

pub(super) fn retained(args: &[AstExpr], nonconstant: &BTreeSet<crate::hir::LocalId>) -> bool {
    // 未知的首参数不取得分支折扣；函数体检查已经证明基线不会额外内联。
    matches!(args, [AstExpr::Var(AstNameRef::Local(local)), _, _] if nonconstant.contains(local))
}
