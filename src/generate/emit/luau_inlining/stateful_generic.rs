//! 核对状态查找 while 的常量真分支展开及原低槽结果前缀。

use super::*;

fn integer(expr: &AstExpr, expected: i64) -> bool {
    match expr {
        AstExpr::Integer(value) => *value == expected,
        AstExpr::Number(value) => {
            *value == expected as f64 && value.to_bits() != (-0.0f64).to_bits()
        }
        _ => false,
    }
}

pub(super) fn body(
    func: &AstFunctionExpr,
    template: usize,
    initial: i64,
    increment: i64,
    field: &crate::LuaString,
) -> bool {
    if func.function.index() != template
        || func.params.len() != 4
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
        || i16::try_from(initial).is_err()
        || i16::try_from(increment).is_err()
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
    let AstExpr::Unary(condition) = &loop_.cond else {
        return false;
    };
    let AstExpr::FieldAccess(access) = &condition.expr else {
        return false;
    };
    let [AstStmt::If(branch)] = loop_.body.stmts.as_slice() else {
        return false;
    };
    let [AstStmt::If(probe)] = branch.then_block.stmts.as_slice() else {
        return false;
    };
    let AstExpr::Unary(test) = &probe.cond else {
        return false;
    };
    let AstExpr::IndexAccess(lookup) = &test.expr else {
        return false;
    };
    let [AstStmt::GenericFor(for_)] = probe.then_block.stmts.as_slice() else {
        return false;
    };
    let Some(else_) = &branch.else_block else {
        return false;
    };
    let [AstStmt::Assign(update)] = else_.stmts.as_slice() else {
        return false;
    };
    let [AstExpr::Binary(add)] = update.values.as_slice() else {
        return false;
    };
    // pinned CostModel：未知参数为 42+3；首参 true 后成本33，收益136%，
    // 阈值25*136/100=34。精确语法同时固定查表次序、迭代体和状态更新。
    integer(value, initial)
        && ret.values.as_slice() == std::slice::from_ref(&state)
        && condition.op == AstUnaryOpKind::Not
        && access.base == parameter(1)
        && field.as_utf8() == Some(access.field.as_str())
        && branch.cond == parameter(0)
        && probe.else_block.is_none()
        && test.op == AstUnaryOpKind::Not
        && lookup.base == parameter(2)
        && lookup.index == state
        && for_.iterator.as_slice() == [parameter(3)]
        && for_.bindings.len() == 2
        && matches!(for_.body.stmts.as_slice(), [AstStmt::Break])
        && update.targets.as_slice() == [AstLValue::Name(binding.id.to_name_ref())]
        && add.op == AstBinaryOpKind::Add
        && add.lhs == state
        && integer(&add.rhs, increment)
}

pub(super) fn inlined_arguments(args: &[AstExpr], written: &BTreeSet<crate::hir::LocalId>) -> bool {
    matches!(args, [AstExpr::Boolean(true), AstExpr::Var(AstNameRef::Local(state)), AstExpr::TableConstructor(table), AstExpr::Var(AstNameRef::Local(iterator))]
        if table.fields.is_empty() && !written.contains(state) && !written.contains(iterator))
}
