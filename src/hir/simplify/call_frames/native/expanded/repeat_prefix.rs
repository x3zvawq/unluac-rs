//! 配对常量条件选中 repeat 首段后留下的高槽状态与低槽返回。
//! 现存函数提供完整控制结构；调用、算术和写回按原帧核对，再交给整批前缀事务。

use super::*;
use crate::hir::common::{HirBinaryOpKind, HirUnaryOpKind, ParamId};

#[derive(Clone)]
pub(super) struct Body {
    initial: i64,
    increment: i64,
}

pub(super) fn integer(expr: &HirExpr) -> Option<i64> {
    match expr {
        HirExpr::Integer(value) if i16::try_from(*value).is_ok() => Some(*value),
        HirExpr::Number(value)
            if value.fract() == 0.0
                && (-32768.0..=32767.0).contains(value)
                && value.to_bits() != (-0.0f64).to_bits() =>
        {
            Some(*value as i64)
        }
        _ => None,
    }
}

fn conjunction(expr: &HirExpr) -> Option<bool> {
    match expr {
        HirExpr::LogicalAnd(expr)
            if expr.lhs == HirExpr::ParamRef(ParamId(0))
                && expr.rhs == HirExpr::ParamRef(ParamId(1)) =>
        {
            Some(true)
        }
        HirExpr::LogicalOr(expr)
            if matches!(&expr.lhs, HirExpr::Unary(v) if v.op == HirUnaryOpKind::Not && v.expr == HirExpr::ParamRef(ParamId(0)))
                && matches!(&expr.rhs, HirExpr::Unary(v) if v.op == HirUnaryOpKind::Not && v.expr == HirExpr::ParamRef(ParamId(1))) =>
        {
            Some(false)
        }
        _ => None,
    }
}

fn empty_condition(stmt: &HirStmt) -> bool {
    let HirStmt::If(branch) = stmt else {
        return false;
    };
    let empty_else = |branch: &crate::hir::common::HirIf| {
        branch
            .else_block
            .as_ref()
            .is_none_or(|block| block.stmts.is_empty())
    };
    if conjunction(&branch.cond) == Some(true) {
        return branch.then_block.stmts.is_empty() && empty_else(branch);
    }
    let [HirStmt::If(inner)] = branch.then_block.stmts.as_slice() else {
        return false;
    };
    branch.cond == HirExpr::ParamRef(ParamId(0))
        && inner.cond == HirExpr::ParamRef(ParamId(1))
        && inner.then_block.stmts.is_empty()
        && empty_else(branch)
        && empty_else(inner)
}

pub(super) fn observation(stmt: &HirStmt, local: LocalId) -> Option<&HirCallExpr> {
    let HirStmt::CallStmt(stmt) = stmt else {
        return None;
    };
    let call = &stmt.call;
    // print 的普通 CALL 成本为 5，且没有 builtin 常量折叠。其它全局调用须先补齐成本合同。
    (matches!(&call.callee, HirExpr::GlobalRef(global) if global.key.as_utf8() == Some("print"))
        && call.args.fixed.as_slice() == [HirExpr::LocalRef(local)]
        && call.args.tail.is_none()
        && call.fastcall.is_none()
        && !call.is_method())
    .then_some(call)
}

fn update(stmt: &HirStmt, input: LocalId) -> Option<(LocalId, &crate::hir::common::HirBinaryExpr)> {
    let (result, HirExpr::Binary(binary)) = scalar_local(stmt)? else {
        return None;
    };
    (binary.op == HirBinaryOpKind::Add && binary.lhs == HirExpr::LocalRef(input))
        .then_some((result, binary))
}

pub(super) fn update_layout(
    binary: &crate::hir::common::HirBinaryExpr,
    facts: &ProtoPromotionFacts,
    home: HomeSlotKey,
) -> bool {
    let Some(layout) = facts.native_binary_layout(binary) else {
        return false;
    };
    layout.lhs == Some(home)
        && layout.rhs.is_none()
        && facts.direct_binary_operand_home(binary, 0) == Some(home)
        && binary.source_site.is_some_and(|site| {
            facts
                .operation_writeback(site)
                .is_some_and(|(_, written)| written == home)
        })
}

fn observation_layout(call: &HirCallExpr, facts: &ProtoPromotionFacts, base: usize) -> bool {
    facts.native_call_frame(call).is_some_and(|frame| {
        frame.home == HomeSlotKey::new(base, 0)
            && frame.arguments_unaliased
            && frame.results == Some(ResultPack::Ignore)
            && matches!(frame.args, ValuePack::Fixed(pack) if pack.start.index() == base + 1 && pack.len == 1)
    })
}

pub(super) fn body(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<Body> {
    // 候选拒绝[ProofIncomplete]：当前编译合同只覆盖无捕获的双条件参数与单数值状态。
    if proto.params.len() != 2
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [
        first @ HirStmt::LocalDecl(_),
        HirStmt::Repeat(repeat),
        HirStmt::Return(ret),
    ] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    let (local, value) = scalar_local(first)?;
    let initial = integer(value)?;
    let home = HomeSlotKey::new(2, 0);
    if facts.trusted_local_home_slot(local) != Some(home)
        || repeat.cond != HirExpr::ParamRef(ParamId(0))
        || ret.values.fixed.as_slice() != [HirExpr::LocalRef(local)]
        || ret.values.tail.is_some()
        || !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(pack) if pack.start.index() == 2 && pack.len == 1)
    {
        return None;
    }
    let (first, mut rest) = repeat.body.stmts.split_first()?;
    if !observation_layout(observation(first, local)?, facts, 3) {
        return None;
    }
    let mut increment = None;
    let mut steps = 0;
    loop {
        let [assign, call, condition] = rest else {
            return None;
        };
        let (result, binary) = update(assign, local)?;
        let value = integer(&binary.rhs)?;
        if result != local
            || !update_layout(binary, facts, home)
            || !observation_layout(observation(call, local)?, facts, 3)
            || increment.is_some_and(|previous| previous != value)
        {
            return None;
        }
        increment = Some(value);
        steps += 1;
        if empty_condition(condition) {
            break;
        }
        let HirStmt::If(branch) = condition else {
            return None;
        };
        let other = branch.else_block.as_ref()?;
        let (exit, next) = if conjunction(&branch.cond)? {
            (&branch.then_block, other)
        } else {
            (other, &branch.then_block)
        };
        if !matches!(exit.stmts.as_slice(), [HirStmt::Continue]) {
            return None;
        }
        rest = &next.stmts;
    }
    crate::hir::common::luau_repeat_prefix_costs(steps).then_some(Body {
        initial,
        increment: increment?,
    })
}

pub(super) fn plans(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let Some(callees) = context.expanded_callees else {
        return Vec::new();
    };
    let mut templates = BTreeMap::new();
    for callee in callees.values() {
        if let Some(body) = &callee.repeat_prefix {
            templates
                .entry((body.initial, body.increment))
                .and_modify(|entry| *entry = None)
                .or_insert(Some(callee));
        }
    }
    let mut plans = Vec::new();
    for (start, window) in context.proto.body.stmts.windows(5).enumerate() {
        let candidate = (|| {
            let [first, before, assign, after, copy] = window else {
                return None;
            };
            let (input, initial_value) = scalar_local(first)?;
            let initial = integer(initial_value)?;
            let (updated, binary) = update(assign, input)?;
            let callee = *templates.get(&(initial, integer(&binary.rhs)?))?.as_ref()?;
            let (result, value) = scalar_local(copy)?;
            let base = facts.trusted_local_home_slot(result)?;
            let home = HomeSlotKey::new(base.slot() + 1, 0);
            let source = binary.source_site?;
            if start <= callee.declaration
                || source.proto != callee.creation.proto
                || *value != HirExpr::LocalRef(updated)
                || facts.trusted_local_home_slot(input) != Some(home)
                || facts.trusted_local_home_slot(updated) != Some(home)
                || !update_layout(binary, facts, home)
                || !facts.operation_result_reference_unaliased(source)
                || (base.slot()..=base.slot() + 1).any(|slot| {
                    let home = HomeSlotKey::new(slot, 0);
                    context.barred.contains(&home) || context.closed.contains(&home)
                })
                || [input, updated]
                    .iter()
                    .any(|id| context.proto.local_debug_scopes[id.index()].is_some())
            {
                return None;
            }
            let before = observation(before, input)?;
            let after = observation(after, updated)?;
            // 原 COPY 仍读取本窗口的初值 binding；中间没有状态写入或引用捕获，
            // 加法的直接输入因此是同一版本。第二次读取再按原加法 Def 配对。
            let before_copy = facts.call_argument_copy(before, 0)?;
            let after_copy = facts.call_argument_copy(after, 0)?;
            if facts.promoted_local_for_temp(before_copy.source) != Some(input)
                || Some(after_copy.source) != facts.operation_result_temp(source)
                || before_copy.source_home != home
                || after_copy.source_home != home
            {
                return None;
            }
            for call in [before, after] {
                if !observation_layout(call, facts, base.slot() + 2) {
                    return None;
                }
                let mut builder =
                    frame_builder(context, &[], facts, DecompileDialect::Luau, base.slot() + 2)?;
                builder.call(call, 0, base.slot() + 2, false, CallWidth::Ignore)?;
            }
            // COPY 不能来自 phi 或多声明合并；其独立高槽读取由当前 binding 与原 home 共同证明。
            if !matches!(copy, HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_none())
                && !matches!(copy, HirStmt::Assign(assign) if !assign.is_phi_transfer && assign.initializer_merge_transaction.is_none())
            {
                return None;
            }
            let mut plan = factories::invocation(callee, source, base, result, start, start + 4);
            plan.values = vec![factories::factory_call(
                callee.local,
                Some(source),
                vec![HirExpr::Boolean(true), HirExpr::Boolean(true)].into(),
            )]
            .into();
            // 两次调用仍在同一展开路径中执行；状态声明须正常退休，
            // 后继同槽写才能恢复为新声明。最终 Generate 必须证明新增 CALL 消失。
            plan.replayed_effects = vec![start + 1, start + 3];
            Some(plan)
        })();
        plans.extend(candidate);
    }
    plans
}
