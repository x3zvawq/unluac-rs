//! 核对最终计数循环及常量、动态调用的编译成本。
//! 与 HIR 合同逐项匹配原操作，成组结果的槽位由父级 occurrence 校验消费。

use super::counter_repeat::integer;
use super::*;
use crate::hir::luau_inlining::{
    CounterLoopKind, GuardedCounterTemplate, guarded_counter_template,
};

fn shape(func: &AstFunctionExpr) -> Option<GuardedCounterTemplate> {
    let [loop_stmt, AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return None;
    };
    let state = AstExpr::Var(AstNameRef::Param(func.params[2]));
    let parameter = |index| AstExpr::Var(AstNameRef::Param(func.params[index]));
    if ret.values.as_slice() != [state.clone()] {
        return None;
    }
    let (kind, condition, body) = match loop_stmt {
        AstStmt::While(loop_) => (CounterLoopKind::While, &loop_.cond, &loop_.body),
        AstStmt::Repeat(loop_) => (CounterLoopKind::Repeat, &loop_.cond, &loop_.body),
        _ => return None,
    };
    let AstExpr::Binary(condition) = condition else {
        return None;
    };
    let [
        AstStmt::Assign(update),
        AstStmt::If(guard),
        AstStmt::If(exit),
    ] = body.stmts.as_slice()
    else {
        return None;
    };
    let [AstExpr::Binary(binary)] = update.values.as_slice() else {
        return None;
    };
    let [AstStmt::If(continued)] = guard.then_block.stmts.as_slice() else {
        return None;
    };
    let [AstStmt::CallStmt(observation)] = guard.else_block.as_ref()?.stmts.as_slice() else {
        return None;
    };
    let AstCallKind::Call(call) = &observation.call else {
        return None;
    };
    let [AstExpr::String(label), observed] = call.args.as_slice() else {
        return None;
    };
    let AstExpr::Binary(stop) = &exit.cond else {
        return None;
    };
    if condition.lhs != state
        || !condition.original_operation
        || condition.op
            != match kind {
                CounterLoopKind::While => AstBinaryOpKind::Gt,
                CounterLoopKind::Repeat => AstBinaryOpKind::Le,
            }
        || update.targets.as_slice() != [AstLValue::Name(AstNameRef::Param(func.params[2]))]
        || binary.op != AstBinaryOpKind::Sub
        || binary.lhs != state
        || !binary.original_operation
        || guard.cond != parameter(0)
        || continued.cond != parameter(1)
        || !matches!(continued.then_block.stmts.as_slice(), [AstStmt::Continue])
        || continued
            .else_block
            .as_ref()
            .is_some_and(|other| !other.stmts.is_empty())
        || stop.op != AstBinaryOpKind::Eq
        || stop.lhs != state
        || !stop.original_operation
        || !matches!(exit.then_block.stmts.as_slice(), [AstStmt::Break])
        || exit
            .else_block
            .as_ref()
            .is_some_and(|other| !other.stmts.is_empty())
        || !matches!(&call.callee,AstExpr::Var(AstNameRef::Global(global)) if global.text=="print")
        || *observed != state
        || call.method_key.is_some()
        || call.required_luau_inlining.is_some()
    {
        return None;
    }
    Some(GuardedCounterTemplate {
        kind,
        decrement: integer(&binary.rhs)?,
        bound: integer(&condition.rhs)?,
        stop: integer(&stop.rhs)?,
        label: label.clone(),
    })
}

pub(super) fn body(func: &AstFunctionExpr, proto: &crate::hir::HirProto) -> bool {
    if func.function != proto.id || func.params.len() != 3 {
        return false;
    }
    let Some(expected) = guarded_counter_template(proto) else {
        return false;
    };
    if shape(func).as_ref() != Some(&expected) {
        return false;
    }
    let costs = constant_control::CostAnalysis::new(func);
    let Some(baseline) = costs.cost(None) else {
        return false;
    };
    // 三种专化分别保留观察、跳过 break、保留共同 break；原动态调用没有控制参数折扣。
    !baseline.permits_inline(baseline)
        && [0, 1, 3].into_iter().all(|mask| {
            costs
                .cost(Some(mask))
                .is_some_and(|profile| profile.permits_inline(baseline))
        })
}

pub(super) fn arguments(args: &[AstExpr]) -> bool {
    matches!(args,[AstExpr::Boolean(_),AstExpr::Boolean(_),value] if integer(value).is_some())
}

pub(super) fn retained(args: &[AstExpr], nonconstant: &BTreeSet<crate::hir::LocalId>) -> bool {
    args.len()==3 && args.iter().all(|value|matches!(value,AstExpr::Var(AstNameRef::Local(local)) if nonconstant.contains(local)))
}
