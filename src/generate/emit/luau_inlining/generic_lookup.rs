//! 核对遍历查表循环的常量 guard、只读参数和固定字符串返回，保持原展开帧。

use super::*;

fn key_matches(value: &AstExpr, key: i64) -> bool {
    matches!(value, AstExpr::Integer(value) if *value == key)
        || matches!(value, AstExpr::Number(value) if *value == key as f64 && value.to_bits() != (-0.0f64).to_bits())
}

pub(super) fn body(
    func: &AstFunctionExpr,
    template: usize,
    key: i64,
    result: &crate::LuaString,
) -> bool {
    if func.function.index() != template
        || func.params.len() != 2
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [AstStmt::While(loop_), AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    let AstExpr::Unary(not) = &loop_.cond else {
        return false;
    };
    let [AstStmt::GenericFor(for_), AstStmt::If(exit)] = loop_.body.stmts.as_slice() else {
        return false;
    };
    let AstExpr::IndexAccess(lookup) = &exit.cond else {
        return false;
    };
    // pinned CostModel：空遍历成本 3、查表和 break/If 各 1，while 再乘 3；
    // guard 的 NOT 至多 1，总成本不超过 21，低于基础内联阈值 25。
    not.op == AstUnaryOpKind::Not
        && not.expr == AstExpr::Var(AstNameRef::Param(func.params[0]))
        && for_.iterator.as_slice() == [AstExpr::Var(AstNameRef::Param(func.params[1]))]
        && for_.bindings.len() == 1
        && for_.body.stmts.is_empty()
        && lookup.base == AstExpr::Var(AstNameRef::Param(func.params[1]))
        && key_matches(&lookup.index, key)
        && matches!(exit.then_block.stmts.as_slice(), [AstStmt::Break])
        && exit.else_block.is_none()
        && ret.values.as_slice() == [AstExpr::String(result.clone())]
}

pub(super) fn arguments(args: &[AstExpr], written: &BTreeSet<crate::hir::LocalId>) -> bool {
    matches!(
        args,
        [
            AstExpr::Boolean(true),
            AstExpr::Nil | AstExpr::TableConstructor(_)
        ]
    ) || matches!(args, [AstExpr::Boolean(false), AstExpr::Var(AstNameRef::Local(local))] if !written.contains(local))
}

pub(super) fn comparison_result(call: &AstCallExpr) -> Option<crate::hir::HirSourceSite> {
    let [AstExpr::LogicalAnd(and)] = call.args.as_slice() else {
        return None;
    };
    let AstExpr::Binary(compare) = &and.lhs else {
        return None;
    };
    let AstExpr::Call(inner) = &compare.lhs else {
        return None;
    };
    (matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "assert")
        && call.method_key.is_none()
        && compare.op == AstBinaryOpKind::Eq)
        .then_some(inner.required_luau_inlining)
        .flatten()
}
