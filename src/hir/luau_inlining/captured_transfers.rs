//! 捕获表追加、捕获 cell 交接和固定返回的有序函数体合同。
//! HIR 与 Generate 共用完整模板，原操作槽位由展开帧 owner 验证。

use super::*;
use crate::hir::{HirBinaryOpKind, HirLValue};

pub(crate) fn template(proto: &HirProto) -> Option<(&LuaString, &LuaString)> {
    if !proto.params.is_empty()
        || proto.signature.is_vararg
        || !proto.children.is_empty()
        || proto.failure.is_some()
        || proto.upvalues != [UpvalueId(0), UpvalueId(1), UpvalueId(2)]
        || proto.mutable_upvalues != std::collections::BTreeSet::from([UpvalueId(1)])
    {
        return None;
    }
    let [
        HirStmt::Assign(append),
        HirStmt::Assign(transfer),
        HirStmt::Return(ret),
    ] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    let ([HirLValue::TableAccess(access)], [HirExpr::String(label)], None) = (
        append.targets.as_slice(),
        append.values.fixed.as_slice(),
        &append.values.tail,
    ) else {
        return None;
    };
    let HirExpr::Binary(key) = &access.key else {
        return None;
    };
    let HirExpr::Unary(length) = &key.lhs else {
        return None;
    };
    let ([HirExpr::String(result)], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return None;
    };
    (access.base == HirExpr::UpvalueRef(UpvalueId(0))
        && key.op == HirBinaryOpKind::Add
        && small_integer(&key.rhs) == Some(1)
        && length.op == HirUnaryOpKind::Length
        && length.expr == HirExpr::UpvalueRef(UpvalueId(0))
        && transfer.targets == [HirLValue::Upvalue(UpvalueId(1))]
        && transfer.values.fixed == [HirExpr::UpvalueRef(UpvalueId(2))]
        && transfer.values.tail.is_none())
    .then_some((label, result))
}
