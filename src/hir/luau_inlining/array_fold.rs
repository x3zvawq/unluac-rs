//! 数组数值遍历的索引与累积状态返回合同。
//! 只描述完整函数体；原槽、参数准备和返回 COPY 由展开帧 owner 核对。

use super::*;
use crate::hir::{HirBinaryOpKind, HirLValue, LocalId};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ArrayFoldTemplate {
    pub initial: i64,
    pub start: i64,
    pub step: i64,
    pub comparison: HirBinaryOpKind,
    pub update: HirBinaryOpKind,
}

fn local(stmt: &HirStmt) -> Option<(LocalId, &HirExpr)> {
    let HirStmt::LocalDecl(decl) = stmt else {
        return None;
    };
    match (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) {
        ([binding], [value], None) => Some((*binding, value)),
        _ => None,
    }
}

pub(crate) fn array_fold_template(proto: &HirProto) -> Option<ArrayFoldTemplate> {
    if proto.params.as_slice() != [ParamId(0), ParamId(1)]
        || proto.signature.is_vararg
        || !proto.children.is_empty()
        || !proto.upvalues.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [
        first,
        second,
        HirStmt::NumericFor(loop_),
        HirStmt::Return(ret),
    ] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    let (selected, initial) = local(first)?;
    let (state, value) = local(second)?;
    let HirExpr::Unary(limit) = &loop_.limit else {
        return None;
    };
    let [
        HirStmt::Assign(index),
        HirStmt::If(exit),
        HirStmt::Assign(update),
    ] = loop_.body.stmts.as_slice()
    else {
        return None;
    };
    let HirExpr::Binary(compare) = &exit.cond else {
        return None;
    };
    let [HirExpr::Binary(binary)] = update.values.fixed.as_slice() else {
        return None;
    };
    let lookup = |expr: &HirExpr| {
        matches!(expr, HirExpr::TableAccess(access)
            if access.base == HirExpr::ParamRef(ParamId(0))
                && access.key == HirExpr::LocalRef(loop_.binding))
    };
    if *value != HirExpr::ParamRef(ParamId(1))
        || limit.op != HirUnaryOpKind::Length
        || limit.expr != HirExpr::ParamRef(ParamId(0))
        || index.targets.as_slice() != [HirLValue::Local(selected)]
        || index.values.fixed.as_slice() != [HirExpr::LocalRef(loop_.binding)]
        || index.values.tail.is_some()
        || !lookup(&compare.lhs)
        || compare.rhs != HirExpr::LocalRef(state)
        || !matches!(
            compare.op,
            HirBinaryOpKind::Eq
                | HirBinaryOpKind::Lt
                | HirBinaryOpKind::Le
                | HirBinaryOpKind::Gt
                | HirBinaryOpKind::Ge
        )
        || !matches!(exit.then_block.stmts.as_slice(), [HirStmt::Break])
        || exit
            .else_block
            .as_ref()
            .is_some_and(|other| !other.stmts.is_empty())
        || update.targets.as_slice() != [HirLValue::Local(state)]
        || update.values.tail.is_some()
        || binary.lhs != HirExpr::LocalRef(state)
        || !lookup(&binary.rhs)
        || !matches!(binary.op, HirBinaryOpKind::Add | HirBinaryOpKind::Sub)
        || ret.values.fixed.as_slice() != [HirExpr::LocalRef(selected), HirExpr::LocalRef(state)]
        || ret.values.tail.is_some()
        || ret.pending_cleanup_source.is_some()
    {
        return None;
    }
    Some(ArrayFoldTemplate {
        initial: small_integer(initial)?,
        start: small_integer(&loop_.start)?,
        step: small_integer(&loop_.step)?,
        comparison: compare.op,
        update: binary.op,
    })
}

/// 与模板中形参、初始状态及循环绑定一一对应的 debug 身份。
pub(crate) fn array_fold_names(proto: &HirProto) -> Option<[Option<String>; 5]> {
    array_fold_template(proto)?;
    let (selected, _) = local(&proto.body.stmts[0])?;
    let (state, _) = local(&proto.body.stmts[1])?;
    let HirStmt::NumericFor(loop_) = &proto.body.stmts[2] else {
        return None;
    };
    Some([
        proto.param_debug_hints[0].clone(),
        proto.param_debug_hints[1].clone(),
        proto.local_debug_hints[selected.index()].clone(),
        proto.local_debug_hints[state.index()].clone(),
        proto.local_debug_hints[loop_.binding.index()].clone(),
    ])
}
