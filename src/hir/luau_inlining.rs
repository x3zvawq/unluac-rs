//! Luau 闭包展开恢复与最终发射共用的封闭函数体合同。
//!
//! 输入当前 HIR 函数及其绑定身份，输出完整模板中的观察标签；原槽证明由帧 owner 持有。

use super::{HirExpr, HirMethodCall, HirProto, HirStmt, HirUnaryOpKind, ParamId, UpvalueId};
use crate::LuaString;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct NumericExitTemplate {
    pub hit: LuaString,
    pub miss: LuaString,
}

pub(crate) fn integer_one(value: &HirExpr) -> bool {
    matches!(value, HirExpr::Integer(1))
        || matches!(value, HirExpr::Number(number) if *number == 1.0)
}

pub(crate) fn insert_tag<'a>(stmt: &'a HirStmt, capture: &HirExpr) -> Option<&'a LuaString> {
    let HirStmt::CallStmt(stmt) = stmt else {
        return None;
    };
    let call = &stmt.call;
    let HirExpr::TableAccess(access) = &call.callee else {
        return None;
    };
    // pinned Luau Bytecode.h: LBF_TABLE_INSERT = 52；原 fast path 和 fallback 名称须一致。
    if call.method != HirMethodCall::None
        || call
            .fastcall
            .is_none_or(|protocol| protocol.builtin() != 52)
        || call.args.tail.is_some()
        || !matches!(&access.base, HirExpr::GlobalRef(global) if global.key.as_utf8() == Some("table"))
        || !matches!(&access.key, HirExpr::String(key) if key.as_utf8() == Some("insert"))
    {
        return None;
    }
    match call.args.fixed.as_slice() {
        [value, HirExpr::String(tag)] if value == capture => Some(tag),
        _ => None,
    }
}

pub(crate) fn numeric_exit_template(proto: &HirProto) -> Option<NumericExitTemplate> {
    if proto.params.as_slice() != [ParamId(0)]
        || proto.upvalues.as_slice() != [UpvalueId(0)]
        || !proto.mutable_upvalues.is_empty()
        || proto.signature.is_vararg
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [HirStmt::NumericFor(for_), miss, HirStmt::Return(ret)] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    if !integer_one(&for_.start)
        || !integer_one(&for_.step)
        || !matches!(&for_.limit, HirExpr::Unary(value) if value.op == HirUnaryOpKind::Length && value.expr == HirExpr::ParamRef(ParamId(0)))
        || ret.values.tail.is_some()
        || ret.values.fixed.as_slice() != [HirExpr::Boolean(false)]
    {
        return None;
    }
    let [HirStmt::If(branch)] = for_.body.stmts.as_slice() else {
        return None;
    };
    if branch.else_block.is_some()
        || !matches!(&branch.cond, HirExpr::TableAccess(access)
            if access.base == HirExpr::ParamRef(ParamId(0)) && access.key == HirExpr::LocalRef(for_.binding))
    {
        return None;
    }
    let [hit, HirStmt::Return(ret)] = branch.then_block.stmts.as_slice() else {
        return None;
    };
    if ret.values.tail.is_some() || ret.values.fixed.as_slice() != [HirExpr::Nil] {
        return None;
    }
    let capture = HirExpr::UpvalueRef(UpvalueId(0));
    Some(NumericExitTemplate {
        hit: insert_tag(hit, &capture)?.clone(),
        miss: insert_tag(miss, &capture)?.clone(),
    })
}
