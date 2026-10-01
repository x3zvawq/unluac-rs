//! 核对数值遍历闭包的最终源码与固定单结果调用合同。

use super::*;

fn one(expr: &AstExpr) -> bool {
    matches!(expr, AstExpr::Integer(1)) || matches!(expr, AstExpr::Number(value) if *value == 1.0)
}

fn event(stmt: &AstStmt, tag: &crate::LuaString) -> bool {
    matches!(stmt, AstStmt::CallStmt(stmt)
        if matches!(&stmt.call, AstCallKind::Call(call)
            if call.method_key.is_none() && call.required_luau_inlining.is_none()
                && matches!(&call.callee, AstExpr::FieldAccess(field)
                    if field.field == "insert" && matches!(&field.base,
                        AstExpr::Var(AstNameRef::Global(name)) if name.text == "table"))
                && call.args.as_slice() == [AstExpr::Var(AstNameRef::Upvalue(crate::hir::UpvalueId(0))), AstExpr::String(tag.clone())]))
}

pub(super) fn body(
    func: &AstFunctionExpr,
    proto: &crate::hir::HirProto,
    capture: Option<crate::hir::LocalId>,
) -> bool {
    let Some(template) = crate::hir::luau_inlining::numeric_exit_template(proto) else {
        return false;
    };
    let Some(capture) = capture else { return false };
    if func.function != proto.id
        || func.params.len() != 1
        || func.is_vararg
        || func.named_vararg.is_some()
        || func.captured_bindings != BTreeSet::from([AstBindingRef::Local(capture)])
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [AstStmt::NumericFor(for_), miss, AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    if !one(&for_.start)
        || !one(&for_.step)
        || !matches!(&for_.limit, AstExpr::Unary(value) if value.op == AstUnaryOpKind::Length
            && value.expr == AstExpr::Var(AstNameRef::Param(func.params[0])))
        || !event(miss, &template.miss)
        || ret.values.as_slice() != [AstExpr::Boolean(false)]
    {
        return false;
    }
    let [AstStmt::If(branch)] = for_.body.stmts.as_slice() else {
        return false;
    };
    if branch.else_block.is_some()
        || !matches!(&branch.cond, AstExpr::IndexAccess(access)
            if access.base == AstExpr::Var(AstNameRef::Param(func.params[0]))
                && access.index == AstExpr::Var(for_.binding.to_name_ref()))
    {
        return false;
    }
    let [hit, AstStmt::Return(ret)] = branch.then_block.stmts.as_slice() else {
        return false;
    };
    // pinned Luau 0.713: cost 18 < 收益调整后的阈值 29；#参数不是常量循环上界。
    // 调用处的数组实参和固定单结果由 arguments/外层声明前缀校验共同约束。
    event(hit, &template.hit) && ret.values.as_slice() == [AstExpr::Nil]
}

pub(super) fn arguments(args: &[AstExpr]) -> bool {
    matches!(args, [AstExpr::TableConstructor(table)]
        if table.fields.iter().all(|field| matches!(field, AstTableField::Array(AstExpr::Boolean(_)))))
}
