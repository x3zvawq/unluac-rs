//! 核对双标签读取调用的最终函数体与 trace 读取体。
//! 只接受 HIR 模板中的标签、比较和选值顺序，确保源码仍触发已证明的两层展开。

use super::*;
use crate::hir::LocalId;
use crate::hir::luau_inlining::{ObservedValueTemplate, TracedReadTemplate};

fn selection(value: &AstExpr, expected: [i64; 2]) -> Option<&AstExpr> {
    let AstExpr::LogicalOr(or) = value else {
        return None;
    };
    let AstExpr::LogicalAnd(and) = &or.lhs else {
        return None;
    };
    (counter_repeat::integer(&and.rhs) == Some(expected[0])
        && counter_repeat::integer(&or.rhs) == Some(expected[1]))
    .then_some(&and.lhs)
}

pub(super) fn body(func: &AstFunctionExpr, template: &ObservedValueTemplate) -> bool {
    let [AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    let [AstExpr::LogicalAnd(and)] = ret.values.as_slice() else {
        return false;
    };
    let AstExpr::Binary(compare) = &and.rhs else {
        return false;
    };
    let Some(AstExpr::Binary(inner)) = selection(&compare.rhs, template.outer) else {
        return false;
    };
    let Some(AstExpr::Call(left)) = selection(&inner.lhs, template.inner) else {
        return false;
    };
    let Some(AstExpr::Call(right)) = selection(&inner.rhs, template.inner) else {
        return false;
    };
    let param = |index| AstExpr::Var(AstNameRef::Param(func.params[index]));
    and.lhs == param(0)
        && compare.op == AstBinaryOpKind::Eq
        && compare.lhs == param(1)
        && inner.op == AstBinaryOpKind::Eq
        && [left, right].iter().zip(&template.tags).all(|(call, tag)| {
            call.callee == param(2)
                && call.method_key.is_none()
                && call.required_luau_inlining.is_none()
                && call.args == [AstExpr::String(tag.clone())]
        })
}

pub(super) fn reader(func: &AstFunctionExpr, template: &TracedReadTemplate) -> bool {
    let [AstStmt::Assign(update), AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    let [AstExpr::Binary(concat)] = update.values.as_slice() else {
        return false;
    };
    let [AstExpr::LogicalOr(or)] = ret.values.as_slice() else {
        return false;
    };
    let key = AstExpr::Var(AstNameRef::Param(func.params[0]));
    if update.targets != [AstLValue::Name(AstNameRef::Upvalue(template.trace))]
        || concat.op != AstBinaryOpKind::Concat
        || concat.lhs != AstExpr::Var(AstNameRef::Upvalue(template.trace))
        || concat.rhs != key
    {
        return false;
    }
    [&or.lhs, &or.rhs].iter().enumerate().all(|(index, value)| {
        let AstExpr::LogicalAnd(and) = value else {
            return false;
        };
        let (AstExpr::Binary(label), AstExpr::Binary(compare)) = (&and.lhs, &and.rhs) else {
            return false;
        };
        label.op == AstBinaryOpKind::Eq
            && label.lhs == key
            && label.rhs == AstExpr::String(template.tags[index].clone())
            && compare.op == AstBinaryOpKind::Eq
            && compare.lhs == AstExpr::Var(AstNameRef::Upvalue(template.inputs[index]))
            && counter_repeat::integer(&compare.rhs) == Some(template.values[index])
    })
}

pub(super) fn arguments(call: &AstCallExpr, reader: LocalId, written: &BTreeSet<LocalId>) -> bool {
    let [
        AstExpr::Binary(flag),
        AstExpr::Var(AstNameRef::Local(value)),
        AstExpr::Var(AstNameRef::Local(actual_reader)),
    ] = call.args.as_slice()
    else {
        return false;
    };
    let AstExpr::Var(AstNameRef::Local(input)) = flag.lhs else {
        return false;
    };
    flag.op == AstBinaryOpKind::Eq
        && counter_repeat::integer(&flag.rhs).is_some_and(|key| (-32768..=32767).contains(&key))
        && *actual_reader == reader
        && ![input, *value, reader]
            .iter()
            .any(|local| written.contains(local))
}
