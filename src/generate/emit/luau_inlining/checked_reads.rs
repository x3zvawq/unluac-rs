//! 核对参数位置创建的固定返回读取体及原标签断言。
//! 闭包身份与捕获由共享依赖合同验证，本模块保留最终 assert、计数和单返回形状。

use super::*;
use crate::hir::luau_inlining::CheckedReadTemplate;

pub(super) fn body(func: &AstFunctionExpr, template: &CheckedReadTemplate) -> bool {
    let [
        AstStmt::CallStmt(check),
        AstStmt::Assign(update),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return false;
    };
    let crate::ast::AstCallKind::Call(call) = &check.call else {
        return false;
    };
    let AstExpr::Var(AstNameRef::Global(global)) = &call.callee else {
        return false;
    };
    let [AstExpr::Binary(compare)] = call.args.as_slice() else {
        return false;
    };
    let [AstExpr::Binary(add)] = update.values.as_slice() else {
        return false;
    };
    let [value] = ret.values.as_slice() else {
        return false;
    };
    global.text == "assert"
        && call.method_key.is_none()
        && call.required_luau_inlining.is_none()
        && compare.op == AstBinaryOpKind::Eq
        && compare.lhs == AstExpr::Var(AstNameRef::Param(func.params[0]))
        && compare.rhs == AstExpr::String(template.tag.clone())
        && update.targets == [AstLValue::Name(AstNameRef::Upvalue(template.counter))]
        && add.op == AstBinaryOpKind::Add
        && add.lhs == AstExpr::Var(AstNameRef::Upvalue(template.counter))
        && counter_repeat::integer(&add.rhs) == Some(template.increment)
        && counter_repeat::integer(value) == Some(template.result)
}

pub(super) fn inputs(call: &AstCallExpr, written: &BTreeSet<crate::hir::LocalId>) -> bool {
    let [
        AstExpr::Binary(flag),
        AstExpr::Var(AstNameRef::Local(value)),
        AstExpr::FunctionExpr(_),
    ] = call.args.as_slice()
    else {
        return false;
    };
    let AstExpr::Var(AstNameRef::Local(input)) = flag.lhs else {
        return false;
    };
    flag.op == AstBinaryOpKind::Eq
        && counter_repeat::integer(&flag.rhs).is_some_and(|key| (-32768..=32767).contains(&key))
        && !written.contains(&input)
        && !written.contains(value)
}
