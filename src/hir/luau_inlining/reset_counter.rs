//! 两个可写 Boolean 参数在循环正文清零的完整计数函数合同。
//! 只读末参数控制循环是否进入；调用方仍需证明参数准备和原返回写回。

use super::*;
use crate::hir::{HirBinaryOpKind, HirLValue};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ResetCounterTemplate {
    pub initial: i64,
    pub increment: i64,
}

pub(crate) fn reset_counter_template(proto: &HirProto) -> Option<ResetCounterTemplate> {
    if proto.params.as_slice() != [ParamId(0), ParamId(1), ParamId(2)]
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [
        HirStmt::LocalDecl(decl),
        HirStmt::While(loop_),
        HirStmt::Return(ret),
    ] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    let ([state], [initial], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    let HirExpr::LogicalAnd(and) = &loop_.cond else {
        return None;
    };
    let HirExpr::LogicalOr(or) = &and.lhs else {
        return None;
    };
    let [
        HirStmt::Assign(update),
        HirStmt::Assign(left),
        HirStmt::Assign(right),
    ] = loop_.body.stmts.as_slice()
    else {
        return None;
    };
    let [HirExpr::Binary(add)] = update.values.fixed.as_slice() else {
        return None;
    };
    let reset = |assign: &crate::hir::common::HirAssign, parameter| {
        assign.targets.as_slice() == [HirLValue::Param(ParamId(parameter))]
            && assign.values.fixed.as_slice() == [HirExpr::Boolean(false)]
            && assign.values.tail.is_none()
    };
    if or.lhs != HirExpr::ParamRef(ParamId(0))
        || or.rhs != HirExpr::ParamRef(ParamId(1))
        || and.rhs != HirExpr::ParamRef(ParamId(2))
        || update.targets.as_slice() != [HirLValue::Local(*state)]
        || update.values.tail.is_some()
        || add.op != HirBinaryOpKind::Add
        || add.lhs != HirExpr::LocalRef(*state)
        || add.source_site.is_none()
        || !reset(left, 0)
        || !reset(right, 1)
        || ret.values.fixed.as_slice() != [HirExpr::LocalRef(*state)]
        || ret.values.tail.is_some()
        || ret.pending_cleanup_source.is_some()
    {
        return None;
    }
    Some(ResetCounterTemplate {
        initial: small_integer(initial)?,
        increment: small_integer(&add.rhs)?,
    })
}
