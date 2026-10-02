//! 条件 continue 与共同 break 组成的计数循环合同。
//! 只提取完整函数体；调用方的参数专化、原 COPY 和源码槽由调用帧恢复者证明。

use super::*;
use crate::hir::{HirBinaryOpKind, HirLValue};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CounterLoopKind {
    While,
    Repeat,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct GuardedCounterTemplate {
    pub kind: CounterLoopKind,
    pub decrement: i64,
    pub bound: i64,
    pub stop: i64,
    pub label: LuaString,
}

pub(crate) fn guarded_counter_template(proto: &HirProto) -> Option<GuardedCounterTemplate> {
    if proto.params.as_slice() != [ParamId(0), ParamId(1), ParamId(2)]
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [loop_stmt, HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let state = HirExpr::ParamRef(ParamId(2));
    if ret.values.fixed.as_slice() != [state.clone()]
        || ret.values.tail.is_some()
        || ret.pending_cleanup_source.is_some()
    {
        return None;
    }
    let (kind, condition, body) = match loop_stmt {
        HirStmt::While(loop_) => (CounterLoopKind::While, &loop_.cond, &loop_.body),
        HirStmt::Repeat(loop_) => (CounterLoopKind::Repeat, &loop_.cond, &loop_.body),
        _ => return None,
    };
    let HirExpr::Binary(condition) = condition else {
        return None;
    };
    let [
        HirStmt::Assign(update),
        HirStmt::If(guard),
        HirStmt::If(exit),
    ] = body.stmts.as_slice()
    else {
        return None;
    };
    let [HirExpr::Binary(binary)] = update.values.fixed.as_slice() else {
        return None;
    };
    let [HirStmt::If(continued)] = guard.then_block.stmts.as_slice() else {
        return None;
    };
    let [HirStmt::CallStmt(observation)] = guard.else_block.as_ref()?.stmts.as_slice() else {
        return None;
    };
    let HirExpr::Binary(stop) = &exit.cond else {
        return None;
    };
    let call = &observation.call;
    let [HirExpr::String(label), observed] = call.args.fixed.as_slice() else {
        return None;
    };
    if condition.lhs != state
        || condition.source_site.is_none()
        || condition.op
            != match kind {
                CounterLoopKind::While => HirBinaryOpKind::Gt,
                CounterLoopKind::Repeat => HirBinaryOpKind::Le,
            }
        || update.targets.as_slice() != [HirLValue::Param(ParamId(2))]
        || update.values.tail.is_some()
        || update.initializer_merge_transaction.is_some()
        || update.generic_for_initializer_producer.is_some()
        || update.method_rewrite_transaction.is_some()
        || update.parallel_nil_frame.is_some()
        || update.root_release.is_some()
        || binary.op != HirBinaryOpKind::Sub
        || binary.lhs != state
        || binary.source_site.is_none()
        || guard.cond != HirExpr::ParamRef(ParamId(0))
        || continued.cond != HirExpr::ParamRef(ParamId(1))
        || !matches!(continued.then_block.stmts.as_slice(), [HirStmt::Continue])
        || continued
            .else_block
            .as_ref()
            .is_some_and(|other| !other.stmts.is_empty())
        || stop.op != HirBinaryOpKind::Eq
        || stop.lhs != state
        || stop.source_site.is_none()
        || !matches!(exit.then_block.stmts.as_slice(), [HirStmt::Break])
        || exit
            .else_block
            .as_ref()
            .is_some_and(|other| !other.stmts.is_empty())
        || !matches!(&call.callee,HirExpr::GlobalRef(global) if global.key.as_utf8()==Some("print"))
        || *observed != state
        || call.args.tail.is_some()
        || call.fastcall.is_some()
        || call.is_method()
        || call.required_luau_inlining.is_some()
    {
        return None;
    }
    Some(GuardedCounterTemplate {
        kind,
        decrement: small_integer(&binary.rhs)?,
        bound: small_integer(&condition.rhs)?,
        stop: small_integer(&stop.rhs)?,
        label: label.clone(),
    })
}
