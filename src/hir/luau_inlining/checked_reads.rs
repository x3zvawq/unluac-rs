//! 描述检查标签、更新捕获计数并返回固定字面量的完整读取体。
//! 标签检查是原调用效果；常量实参折叠后仍须以 assert(true) 重发。

use super::*;
use crate::hir::{HirBinaryOpKind, HirLValue};

#[derive(Clone)]
pub(crate) struct CheckedReadTemplate {
    pub counter: UpvalueId,
    pub tag: LuaString,
    pub increment: i64,
    pub result: i64,
}

pub(crate) fn checked_read_template(proto: &HirProto) -> Option<CheckedReadTemplate> {
    if proto.params.as_slice() != [ParamId(0)]
        || proto.upvalues.len() != 1
        || proto.signature.is_vararg
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [
        HirStmt::CallStmt(check),
        HirStmt::Assign(update),
        HirStmt::Return(ret),
    ] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    let call = &check.call;
    let HirExpr::GlobalRef(global) = &call.callee else {
        return None;
    };
    let [HirExpr::Binary(compare)] = call.args.fixed.as_slice() else {
        return None;
    };
    let HirExpr::String(tag) = &compare.rhs else {
        return None;
    };
    let ([HirLValue::Upvalue(counter)], [HirExpr::Binary(add)], None) = (
        update.targets.as_slice(),
        update.values.fixed.as_slice(),
        &update.values.tail,
    ) else {
        return None;
    };
    let ([value], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return None;
    };
    if global.key.as_utf8() != Some("assert")
        || call.args.tail.is_some()
        || call.is_method()
        || call.fastcall.is_none_or(|protocol| protocol.builtin() != 1)
        || compare.op != HirBinaryOpKind::Eq
        || compare.lhs != HirExpr::ParamRef(ParamId(0))
        || tag.as_bytes().len() > 256
        || update.is_phi_transfer
        || update.initializer_merge_transaction.is_some()
        || add.op != HirBinaryOpKind::Add
        || add.lhs != HirExpr::UpvalueRef(*counter)
        || proto.mutable_upvalues.len() != 1
        || !proto.mutable_upvalues.contains(counter)
        || ret.pending_cleanup_source.is_some()
    {
        return None;
    }
    Some(CheckedReadTemplate {
        counter: *counter,
        tag: tag.clone(),
        increment: small_integer(&add.rhs)?,
        result: small_integer(value)?,
    })
}
