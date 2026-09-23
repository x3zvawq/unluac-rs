//! 配对单参数函数的快照、条件方法调用与字段返回展开帧。
//!
//! 函数体和 caller 的每个读取仍保留独立来源；只有表达式、原槽和方法协议共同吻合，
//! 才交给整批源码帧事务恢复调用，并要求 Generate 证明该调用会再次内联。

use super::*;
use crate::hir::common::{HirOperationSources, HirUnaryOpKind, ParamId};

#[derive(Clone)]
pub(super) struct Body {
    snapshot: HirExpr,
    condition: HirExpr,
    method: HirCallExpr,
    returned: HirExpr,
    local: LocalId,
    name: Option<String>,
}

fn literal(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
    )
}

fn method_args(call: &HirCallExpr) -> Option<&[HirExpr]> {
    if call.args.tail.is_some() || call.fastcall.is_some() {
        return None;
    }
    call.method_receiver()?;
    Some(&call.args.fixed[usize::from(call.method == HirMethodCall::Explicit)..])
}

fn expression_cost(expr: &HirExpr, local: LocalId) -> Option<usize> {
    Some(match expr {
        HirExpr::ParamRef(ParamId(0)) => 0,
        HirExpr::LocalRef(id) if *id == local => 0,
        HirExpr::TableAccess(access) if matches!(access.key, HirExpr::String(_)) => {
            expression_cost(&access.base, local)? + 1
        }
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not && unary.source_site.is_none() => {
            expression_cost(&unary.expr, local)? + 1
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expression_cost(&logical.lhs, local)? + expression_cost(&logical.rhs, local)? + 1
        }
        _ => return None,
    })
}

fn body_layout(expr: &HirExpr, local: LocalId, facts: &ProtoPromotionFacts, slot: usize) -> bool {
    match expr {
        HirExpr::ParamRef(ParamId(0)) => true,
        HirExpr::LocalRef(id) => *id == local,
        HirExpr::TableAccess(access) => {
            let Some(layout) = facts.native_table_read_layout(access) else {
                return false;
            };
            let base = if matches!(access.base, HirExpr::ParamRef(ParamId(0))) {
                0
            } else {
                slot
            };
            matches!(access.key, HirExpr::String(_))
                && layout.key.is_none()
                && layout.base == HomeSlotKey::new(base, 0)
                && facts.table_read_result_home(access) == Some(HomeSlotKey::new(slot, 0))
                && body_layout(&access.base, local, facts, slot)
        }
        HirExpr::Unary(unary) => {
            unary.op == HirUnaryOpKind::Not
                && unary.source_site.is_none()
                && body_layout(&unary.expr, local, facts, slot)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            body_layout(&logical.lhs, local, facts, slot)
                && body_layout(&logical.rhs, local, facts, slot)
        }
        _ => false,
    }
}

pub(super) fn body(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<Body> {
    if proto.params.len() != 1
        || proto.signature.is_vararg
        || !proto.children.is_empty()
        || !proto.upvalues.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [
        first @ HirStmt::LocalDecl(_),
        HirStmt::If(branch),
        HirStmt::Return(ret),
    ] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    let (local, snapshot @ HirExpr::TableAccess(read)) = scalar_local(first)? else {
        return None;
    };
    let ([returned @ HirExpr::TableAccess(last)], None) =
        (ret.values.fixed.as_slice(), &ret.values.tail)
    else {
        return None;
    };
    let [HirStmt::CallStmt(method)] = branch.then_block.stmts.as_slice() else {
        return None;
    };
    let (receiver, _) = method.call.method_receiver()?;
    let args = method_args(&method.call)?;
    let frame = facts.native_call_frame(&method.call)?;
    if branch.else_block.is_some()
        || read.base != HirExpr::ParamRef(ParamId(0))
        || last.base != read.base
        || *receiver != read.base
        || facts.trusted_local_home_slot(local) != Some(HomeSlotKey::new(1, 0))
        || !body_layout(snapshot, local, facts, 1)
        || !body_layout(&branch.cond, local, facts, 2)
        || !body_layout(returned, local, facts, 2)
        || frame.home != HomeSlotKey::new(2, 0)
        || frame.results != Some(ResultPack::Ignore)
        || !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(pack)
            if pack.start.index() == 2 && pack.len == 1)
        || args.len() > 16
        || !args.iter().all(literal)
    {
        return None;
    }
    // pinned CostModel：local/index 成本、if 跳转以及方法 lookup/CALL/常量实参逐项计入；
    // 直接低槽实参不依赖常量折扣，成本不超过基础阈值即可保证这一层内联。
    let cost = expression_cost(snapshot, local)?
        + expression_cost(&branch.cond, local)?
        + 1
        + 4
        + args.len()
        + expression_cost(returned, local)?;
    if cost > 25 {
        return None;
    }
    Some(Body {
        snapshot: snapshot.clone(),
        condition: branch.cond.clone(),
        method: method.call.clone(),
        returned: returned.clone(),
        local,
        name: proto.local_debug_hints[local.index()].clone(),
    })
}

struct Match<'a> {
    body: &'a Body,
    facts: &'a ProtoPromotionFacts,
    argument: LocalId,
    argument_home: HomeSlotKey,
    snapshot: HirExpr,
}

impl Match<'_> {
    fn expression(&self, expected: &HirExpr, actual: &HirExpr, slot: usize) -> bool {
        match (expected, actual) {
            (HirExpr::ParamRef(ParamId(0)), HirExpr::LocalRef(id)) => *id == self.argument,
            (HirExpr::LocalRef(left), right) => *left == self.body.local && *right == self.snapshot,
            (HirExpr::TableAccess(left), HirExpr::TableAccess(right)) => {
                let Some(layout) = self.facts.native_table_read_layout(right) else {
                    return false;
                };
                let base = if matches!(left.base, HirExpr::ParamRef(ParamId(0))) {
                    self.argument_home
                } else {
                    HomeSlotKey::new(slot, 0)
                };
                left.key == right.key
                    && layout.key.is_none()
                    && layout.base == base
                    && self.facts.table_read_result_home(right) == Some(HomeSlotKey::new(slot, 0))
                    && matches!(right.sources, HirOperationSources::Single(source)
                        if self.facts.operation_result_reference_unaliased(source))
                    && self.expression(&left.base, &right.base, slot)
            }
            (HirExpr::Unary(left), HirExpr::Unary(right)) => {
                left.op == right.op
                    && right.source_site.is_none()
                    && self.expression(&left.expr, &right.expr, slot)
            }
            (HirExpr::LogicalAnd(left), HirExpr::LogicalAnd(right))
            | (HirExpr::LogicalOr(left), HirExpr::LogicalOr(right)) => {
                self.expression(&left.lhs, &right.lhs, slot)
                    && self.expression(&left.rhs, &right.rhs, slot)
            }
            _ => false,
        }
    }
}

pub(super) fn plans(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let mut writes = BTreeMap::<LocalId, usize>::new();
    visit_stmts(
        &context.proto.body.stmts,
        &mut BindingWriteCollector(|binding| {
            if let HirBinding::Local(local) = binding {
                *writes.entry(local).or_default() += 1;
            }
        }),
    );
    let Some(callees) = context.expanded_callees else {
        return Vec::new();
    };
    let mut by_snapshot = BTreeMap::new();
    for callee in callees.values() {
        if let Some(body) = &callee.conditional_method
            && let HirExpr::TableAccess(read) = &body.snapshot
            && let HirExpr::String(key) = &read.key
        {
            // 多个模板拥有同一入口时没有唯一的反向身份；保留展开体，不逐候选重扫。
            by_snapshot
                .entry(key)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(callee));
        }
    }
    let mut plans = Vec::new();
    for (start, window) in context.proto.body.stmts.windows(3).enumerate() {
        let [first, HirStmt::If(branch), last @ HirStmt::LocalDecl(_)] = window else {
            continue;
        };
        let (snapshot, initial, snapshot_home, snapshot_name) = match first {
            HirStmt::LocalDecl(_) => {
                let Some((local, value)) = scalar_local(first) else {
                    continue;
                };
                if writes.get(&local) != Some(&1) {
                    continue;
                }
                (
                    HirExpr::LocalRef(local),
                    value,
                    facts.trusted_local_home_slot(local),
                    context.proto.local_debug_hints[local.index()].as_ref(),
                )
            }
            HirStmt::Assign(assign) => {
                let ([HirLValue::Temp(temp)], [value], None) = (
                    assign.targets.as_slice(),
                    assign.values.fixed.as_slice(),
                    &assign.values.tail,
                ) else {
                    continue;
                };
                if !facts.temp_definition_reference_unaliased(*temp) {
                    continue;
                }
                (
                    HirExpr::TempRef(*temp),
                    value,
                    facts.trusted_temp_home_slot(*temp),
                    None,
                )
            }
            _ => continue,
        };
        let HirExpr::TableAccess(read) = initial else {
            continue;
        };
        let Some((result, returned @ HirExpr::TableAccess(last_read))) = scalar_local(last) else {
            continue;
        };
        let HirExpr::LocalRef(argument) = read.base else {
            continue;
        };
        let [HirStmt::CallStmt(method)] = branch.then_block.stmts.as_slice() else {
            continue;
        };
        let Some(base) = facts.trusted_local_home_slot(result) else {
            continue;
        };
        let Some(argument_home) = facts.trusted_local_home_slot(argument) else {
            continue;
        };
        if branch.else_block.is_some()
            || base != HomeSlotKey::new(base.slot(), 0)
            || argument_home.slot() >= base.slot()
            || writes.get(&argument) != Some(&1)
            || context.barred.contains(&argument_home)
            || context.closed.contains(&argument_home)
            || snapshot_home != Some(HomeSlotKey::new(base.slot() + 1, 0))
        {
            continue;
        }
        let HirExpr::String(key) = &read.key else {
            continue;
        };
        if let Some(Some(callee)) = by_snapshot.get(key) {
            let Some(body) = &callee.conditional_method else {
                continue;
            };
            let paired = (|| {
                if start <= callee.declaration
                    || snapshot_name.is_some_and(|name| body.name.as_ref() != Some(name))
                {
                    return None;
                }
                let matcher = Match {
                    body,
                    facts,
                    argument,
                    argument_home,
                    snapshot,
                };
                if !matcher.expression(&body.snapshot, initial, base.slot() + 1)
                    || !matcher.expression(&body.condition, &branch.cond, base.slot() + 2)
                    || !matcher.expression(&body.returned, returned, base.slot())
                    || method.call.method_receiver()?
                        != (
                            &HirExpr::LocalRef(argument),
                            body.method.method_receiver()?.1,
                        )
                    || method_args(&method.call)? != method_args(&body.method)?
                {
                    return None;
                }
                let mut builder =
                    frame_builder(context, &[], facts, DecompileDialect::Luau, base.slot() + 2)?;
                builder.call(&method.call, 0, base.slot() + 2, false, CallWidth::Ignore)?;
                let HirOperationSources::Single(source) = last_read.sources else {
                    return None;
                };
                let mut plan =
                    factories::invocation(callee, source, base, result, start, start + 2);
                plan.values = vec![factories::factory_call(
                    callee.local,
                    Some(source),
                    vec![HirExpr::LocalRef(argument)].into(),
                )]
                .into();
                Some(plan)
            })();
            if let Some(plan) = paired {
                plans.push(plan);
            }
        }
    }
    plans
}
