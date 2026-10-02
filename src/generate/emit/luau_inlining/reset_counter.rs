//! 核对可写 Boolean 参数清零循环的最终函数体和固定参数调用。
//! 原循环、运算与参数更新均须保留，复用 pinned 成本模型验证必需内联。

use super::*;
use crate::hir::luau_inlining::{ResetCounterTemplate, reset_counter_template};

fn shape(func: &AstFunctionExpr) -> Option<ResetCounterTemplate> {
    let [
        AstStmt::LocalDecl(decl),
        AstStmt::While(loop_),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return None;
    };
    let ([binding], [initial]) = (decl.bindings.as_slice(), decl.values.as_slice()) else {
        return None;
    };
    let state = binding.id.to_name_ref();
    let param = |i| AstExpr::Var(AstNameRef::Param(func.params[i]));
    let AstExpr::LogicalAnd(and) = &loop_.cond else {
        return None;
    };
    let AstExpr::LogicalOr(or) = &and.lhs else {
        return None;
    };
    let [
        AstStmt::Assign(update),
        AstStmt::Assign(left),
        AstStmt::Assign(right),
    ] = loop_.body.stmts.as_slice()
    else {
        return None;
    };
    let [AstExpr::Binary(add)] = update.values.as_slice() else {
        return None;
    };
    let reset = |assign: &AstAssign, i| {
        assign.targets.as_slice() == [AstLValue::Name(AstNameRef::Param(func.params[i]))]
            && assign.values.as_slice() == [AstExpr::Boolean(false)]
    };
    if or.lhs != param(0)
        || or.rhs != param(1)
        || and.rhs != param(2)
        || update.targets.as_slice() != [AstLValue::Name(state.clone())]
        || add.op != AstBinaryOpKind::Add
        || add.lhs != AstExpr::Var(state.clone())
        || !add.original_operation
        || !reset(left, 0)
        || !reset(right, 1)
        || ret.values.as_slice() != [AstExpr::Var(state)]
    {
        return None;
    }
    Some(ResetCounterTemplate {
        initial: counter_repeat::integer(initial)?,
        increment: counter_repeat::integer(&add.rhs)?,
    })
}

pub(super) fn body(func: &AstFunctionExpr, proto: &crate::hir::HirProto) -> bool {
    func.function == proto.id && func.params.len() == 3 && !func.is_vararg
        && func.named_vararg.is_none() && func.captured_bindings.is_empty() && func.captured_params.is_empty()
        && func.capture_write_names.is_empty()
        && reset_counter_template(proto).is_some_and(|template| shape(func) == Some(template))
        // 前两参数有写入，常量实参不会专化其读取；末参数在条件树中的成本掩码与可写参数相交为空。
        && constant_control::cost(func, None).is_some_and(|cost| cost.permits_inline(cost))
}

pub(super) fn arguments(args: &[AstExpr]) -> bool {
    matches!(
        args,
        [
            AstExpr::Boolean(_),
            AstExpr::Boolean(_),
            AstExpr::Boolean(_)
        ]
    )
}
