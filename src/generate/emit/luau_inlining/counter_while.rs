//! 验证计数 while 的最终函数体、常量路径及保留 CALL 的编译成本。

use super::*;

fn integer(expr: &AstExpr) -> Option<i64> {
    match expr {
        AstExpr::Integer(value) if i16::try_from(*value).is_ok() => Some(*value),
        AstExpr::Number(value)
            if value.fract() == 0.0
                && (-32768.0..=32767.0).contains(value)
                && value.to_bits() != (-0.0f64).to_bits() =>
        {
            Some(*value as i64)
        }
        _ => None,
    }
}

fn simple_exit(branch: &AstIf, condition: &AstExpr, continued: bool) -> bool {
    branch.cond == *condition
        && branch.else_block.is_none()
        && if continued {
            matches!(branch.then_block.stmts.as_slice(), [AstStmt::Continue])
        } else {
            matches!(branch.then_block.stmts.as_slice(), [AstStmt::Break])
        }
}

pub(super) fn body(
    func: &AstFunctionExpr,
    template: usize,
    initial: i64,
    increment: i64,
    limit: i64,
) -> bool {
    if func.function.index() != template
        || func.params.len() != 4
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [
        AstStmt::LocalDecl(decl),
        AstStmt::While(loop_),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return false;
    };
    let ([binding], [value]) = (decl.bindings.as_slice(), decl.values.as_slice()) else {
        return false;
    };
    let state = AstExpr::Var(binding.id.to_name_ref());
    let parameter = |index| AstExpr::Var(AstNameRef::Param(func.params[index]));
    let [
        AstStmt::Assign(assign),
        AstStmt::If(exit),
        AstStmt::Repeat(repeat),
    ] = loop_.body.stmts.as_slice()
    else {
        return false;
    };
    let [AstExpr::Binary(add)] = assign.values.as_slice() else {
        return false;
    };
    let AstExpr::Binary(compare) = &exit.cond else {
        return false;
    };
    if integer(value) != Some(initial)
        || loop_.cond != parameter(0)
        || ret.values.as_slice() != [state.clone()]
        || assign.targets.as_slice() != [AstLValue::Name(binding.id.to_name_ref())]
        || add.op != AstBinaryOpKind::Add
        || add.lhs != state
        || integer(&add.rhs) != Some(increment)
        || compare.op != AstBinaryOpKind::Gt
        || compare.lhs != state
        || integer(&compare.rhs) != Some(limit)
        || !simple_exit(exit, &exit.cond, false)
    {
        return false;
    }
    let [AstStmt::If(skip), AstStmt::If(stop), call] = repeat.body.stmts.as_slice() else {
        return false;
    };
    let AstExpr::Unary(not) = &skip.cond else {
        return false;
    };
    let AstExpr::LogicalOr(condition) = &repeat.cond else {
        return false;
    };
    let AstExpr::IndexAccess(access) = &condition.rhs else {
        return false;
    };
    if not.op != AstUnaryOpKind::Not
        || not.expr != parameter(1)
        || !simple_exit(skip, &skip.cond, true)
        || !simple_exit(stop, &parameter(2), false)
        || condition.lhs != parameter(0)
        || access.base != parameter(3)
        || access.index != state
    {
        return false;
    }
    // pinned CostModel：while/repeat 各乘3，普通 print 成本5；无常量时120+3，
    // 跳过 print 的路径21<=75，保留 print 的路径57>25*215/100=53。
    // 最终 AST 的控制节点和操作均在上面逐项核对，不能借语义等价任意改变成本。
    matches!(call, AstStmt::CallStmt(stmt)
        if matches!(&stmt.call, AstCallKind::Call(call)
            if matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "print")
                && call.method_key.is_none() && call.required_luau_inlining.is_none()
                && call.args.as_slice() == [state]))
}

pub(super) fn inlined_arguments(args: &[AstExpr]) -> bool {
    matches!(
        args,
        [
            AstExpr::Boolean(_),
            AstExpr::Boolean(false),
            AstExpr::Boolean(false),
            AstExpr::Nil
        ]
    )
}

pub(super) fn retained_arguments(args: &[AstExpr]) -> bool {
    matches!(
        args,
        [
            AstExpr::Boolean(true),
            AstExpr::Boolean(true),
            AstExpr::Boolean(false),
            AstExpr::Var(AstNameRef::Local(_))
        ]
    )
}

pub(super) fn comparison_result(call: &AstCallExpr) -> Option<crate::hir::HirSourceSite> {
    let [AstExpr::Binary(compare)] = call.args.as_slice() else {
        return None;
    };
    let AstExpr::Call(inner) = &compare.lhs else {
        return None;
    };
    (matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "assert")
        && call.method_key.is_none()
        && compare.op == AstBinaryOpKind::Eq
        && integer(&compare.rhs).is_some())
    .then_some(inner.required_luau_inlining)
    .flatten()
}
