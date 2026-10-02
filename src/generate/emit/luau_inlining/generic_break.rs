//! 核对立即退出的捕获状态迭代函数；嵌套闭包体保持普通编译边界。

use super::*;

pub(super) fn body(func: &AstFunctionExpr, template: usize, initial: i64) -> bool {
    if func.function.index() != template
        || !func.params.is_empty()
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [
        AstStmt::LocalDecl(state),
        AstStmt::LocalFunctionDecl(iterator),
        AstStmt::GenericFor(for_),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return false;
    };
    let ([binding], [value]) = (state.bindings.as_slice(), state.values.as_slice()) else {
        return false;
    };
    let name = binding.id.to_name_ref();
    // 无参数、一次闭包分配和立即 break 的 pinned Luau 成本为 16；迭代器通过 FORGLOOP 调用，不额外内联。
    (matches!(value, AstExpr::Integer(value) if *value == initial)
        || matches!(value, AstExpr::Number(value) if *value == initial as f64 && value.to_bits() != (-0.0f64).to_bits()))
        && iterator.func.params.is_empty()
        && iterator.func.captured_bindings == BTreeSet::from([binding.id])
        && iterator.func.capture_write_names == BTreeSet::from([name.clone()])
        && PlainExpressions::new(&BTreeMap::new()).function(&iterator.func)
        && for_.bindings.len() == 1
        && for_.iterator.as_slice() == [AstExpr::Var(iterator.name.to_name_ref())]
        && matches!(for_.body.stmts.as_slice(), [AstStmt::Break])
        && ret.values.as_slice() == [AstExpr::Var(name)]
}
