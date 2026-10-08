//! 核对计数遍历模板及常量短路调用的编译成本；调用结果仍占原观察参数槽。

use super::counter_repeat::integer;
use super::repeat_prefix::observation;
use super::*;

fn add(stmt: &AstStmt, state: &AstNameRef, increment: i64) -> bool {
    matches!(stmt, AstStmt::Assign(assign)
        if assign.targets.as_slice() == [AstLValue::Name(state.clone())]
            && matches!(assign.values.as_slice(), [AstExpr::Binary(add)]
                if add.op == AstBinaryOpKind::Add && add.lhs == AstExpr::Var(state.clone())
                    && integer(&add.rhs) == Some(increment)))
}

pub(super) fn body(
    func: &AstFunctionExpr,
    template: usize,
    initial: i64,
    increment: i64,
    repeats: usize,
) -> bool {
    if func.function.index() != template || func.params.len() != 4 {
        return false;
    }
    let [
        AstStmt::LocalDecl(decl),
        AstStmt::GenericFor(for_),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return false;
    };
    let ([binding], [value]) = (decl.bindings.as_slice(), decl.values.as_slice()) else {
        return false;
    };
    let state = binding.id.to_name_ref();
    let parameter = |index| AstExpr::Var(AstNameRef::Param(func.params[index]));
    let [AstStmt::If(branch), tail] = for_.body.stmts.as_slice() else {
        return false;
    };
    if integer(value) != Some(initial)
        || for_.iterator.as_slice() != [parameter(3)]
        || for_.bindings.len() != 2
        || branch.cond != parameter(0)
        || !add(tail, &state, increment)
        || ret.values.as_slice() != [AstExpr::Var(state.clone())]
    {
        return false;
    }
    let (steps, remainder) = branch.then_block.stmts.as_chunks::<2>();
    if steps.len() != repeats || repeats == 0 || !remainder.is_empty() {
        return false;
    }
    for [update, repeat] in steps {
        let AstStmt::Repeat(repeat) = repeat else {
            return false;
        };
        if !add(update, &state, increment)
            || repeat.cond != parameter(1)
            || !matches!(repeat.body.stmts.as_slice(), [update] if add(update, &state, increment))
        {
            return false;
        }
    }
    let Some(other) = &branch.else_block else {
        return false;
    };
    let [AstStmt::If(skip), AstStmt::If(update), AstStmt::If(stop)] = other.stmts.as_slice() else {
        return false;
    };
    let AstExpr::LogicalAnd(condition) = &skip.cond else {
        return false;
    };
    let not_parameter = |expr: &AstExpr, index| {
        matches!(expr, AstExpr::Unary(not)
        if not.op == AstUnaryOpKind::Not && not.expr == parameter(index))
    };
    let and_parameters = |expr: &AstExpr| {
        matches!(expr, AstExpr::LogicalAnd(and)
        if and.lhs == parameter(0) && and.rhs == parameter(1))
    };
    let [call, AstStmt::If(exit)] = stop.then_block.stmts.as_slice() else {
        return false;
    };
    let AstExpr::IndexAccess(lookup) = &exit.cond else {
        return false;
    };
    // pinned CostModel 会以固定实参重算函数体：三个 Boolean 选中加法后 continue，
    // generic-for 的迭代成本为3*(1+1+1)=9，低于基础内联阈值25。
    // 未选中的分支仍逐项核对，确保参数没有写入，也不改变保留的普通调用。
    not_parameter(&condition.lhs, 0)
        && not_parameter(&condition.rhs, 2)
        && skip.else_block.is_none()
        && matches!(skip.then_block.stmts.as_slice(), [step, AstStmt::Continue] if add(step, &state, increment))
        && and_parameters(&update.cond)
        && update.else_block.is_none()
        && matches!(update.then_block.stmts.as_slice(), [step] if add(step, &state, increment))
        && and_parameters(&stop.cond)
        && stop.else_block.is_none()
        && observation(call, &state)
        && lookup.base == parameter(3)
        && lookup.index == AstExpr::Var(state)
        && exit.else_block.is_none()
        && matches!(exit.then_block.stmts.as_slice(), [AstStmt::Break])
}

pub(super) fn arguments(args: &[AstExpr]) -> bool {
    matches!(
        args,
        [
            AstExpr::Boolean(false),
            AstExpr::Boolean(true),
            AstExpr::Boolean(false),
            AstExpr::TableConstructor(_)
        ]
    )
}

pub(super) fn retained_arguments(args: &[AstExpr]) -> bool {
    // 两个索引结果不是编译期常量；只有一组 repeat 时成本下界仍为66。
    // pinned baseline 饱和上限为127+3；即使取此上限，收益折扣阈值也至多49。
    matches!(
        args,
        [
            AstExpr::IndexAccess(_),
            AstExpr::Boolean(true),
            AstExpr::IndexAccess(_),
            AstExpr::TableConstructor(_)
        ]
    )
}
