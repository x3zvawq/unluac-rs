//! 恢复返回按值捕获闭包的直线工厂展开体。
//!
//! 函数体与 caller 按原操作、捕获身份和统一槽偏移配对；常量参数只在原展开体
//! 已折叠相应算术时替换。后续调用、结果 COPY 和整个源码前缀仍随同一事务提交。

use super::*;
use crate::hir::common::{HirClosureCreation, HirSourceSite};

#[derive(Clone)]
pub(super) struct Factory {
    pub(super) template: usize,
    parameter: crate::hir::ParamId,
    steps: Vec<(Option<LocalId>, HirExpr, usize)>,
    result: LocalId,
    result_slot: usize,
    names: BTreeMap<LocalId, String>,
}

fn statements<'a>(block: &'a HirBlock, output: &mut Vec<&'a HirStmt>) {
    for stmt in &block.stmts {
        if let HirStmt::Block(child) = stmt {
            statements(child, output);
        } else {
            output.push(stmt);
        }
    }
}

fn operand_cost(value: &HirExpr, depth: usize) -> Option<usize> {
    if depth > 4 {
        return None;
    }
    match value {
        HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::Nil
        | HirExpr::Integer(_)
        | HirExpr::String(_) => Some(0),
        HirExpr::Number(_) if integer(value).is_some() => Some(0),
        HirExpr::Binary(binary)
            if matches!(
                binary.op,
                crate::hir::HirBinaryOpKind::Add
                    | crate::hir::HirBinaryOpKind::Sub
                    | crate::hir::HirBinaryOpKind::Mul
            ) =>
        {
            Some(1 + operand_cost(&binary.lhs, depth + 1)? + operand_cost(&binary.rhs, depth + 1)?)
        }
        _ => None,
    }
}

fn integer(value: &HirExpr) -> Option<i64> {
    match value {
        HirExpr::Integer(value) => i32::try_from(*value).ok().map(i64::from),
        HirExpr::Number(value)
            if value.to_bits() != (-0.0f64).to_bits()
                && *value >= f64::from(i32::MIN)
                && *value <= f64::from(i32::MAX)
                && value.fract() == 0.0 =>
        {
            Some(*value as i64)
        }
        _ => None,
    }
}

fn frame(
    facts: &ProtoPromotionFacts,
    call: &HirCallExpr,
) -> Option<crate::hir::promotion::NativeCallFrame> {
    facts
        .native_call_frame(call)
        .or_else(|| facts.native_fastcall_frame(call))
}

fn nil_bindings(facts: &ProtoPromotionFacts) -> BTreeSet<LocalId> {
    facts
        .nil_write_groups()
        .filter_map(|group| {
            let [temp] = group else {
                return None;
            };
            facts
                .temp_definition_reference_unaliased(*temp)
                .then(|| facts.promoted_local_for_temp(*temp))
                .flatten()
        })
        .collect()
}

pub(super) fn body(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    protos: &[HirProto],
) -> Option<Factory> {
    if proto.signature.is_vararg
        || proto.params.len() != 1
        || !proto.upvalues.is_empty()
        || proto.failure.is_some()
        || proto.children.len() != 1
    {
        return None;
    }
    let mut flat = Vec::new();
    statements(&proto.body, &mut flat);
    let nils = nil_bindings(facts);
    let (last, prefix) = flat.split_last()?;
    let HirStmt::Return(ret) = last else {
        return None;
    };
    let ([HirExpr::LocalRef(result)], None) = (ret.values.fixed.as_slice(), &ret.values.tail)
    else {
        return None;
    };
    let mut steps = Vec::new();
    let mut template = None;
    let mut result_slot = None;
    let mut cost = 0;
    for stmt in prefix {
        let (target, value, home) = if let Some((local, value)) = scalar_local(stmt) {
            (
                Some(local),
                value.clone(),
                facts.trusted_local_home_slot(local)?,
            )
        } else if let HirStmt::CallStmt(call) = stmt {
            (
                None,
                HirExpr::Call(Box::new(call.call.clone())),
                frame(facts, &call.call)?.home,
            )
        } else {
            return None;
        };
        if home != HomeSlotKey::new(home.slot(), 0) {
            return None;
        }
        match &value {
            HirExpr::Nil
                if target.is_some_and(|local| nils.contains(&local))
                    && matches!(stmt, HirStmt::LocalDecl(_)) => {}
            HirExpr::Call(call)
                if call.method == HirMethodCall::None
                    && call.args.tail.is_none()
                    && matches!(call.callee, HirExpr::GlobalRef(_)) =>
            {
                let layout = frame(facts, call)?;
                if target.is_some()
                    && (!matches!(stmt, HirStmt::LocalDecl(_))
                        || !facts.operation_result_reference_unaliased(call.source_site?))
                {
                    return None;
                }
                let HirExpr::GlobalRef(global) = &call.callee else {
                    unreachable!()
                };
                let builtin = matches!(global.key.as_utf8(), Some("tostring" | "type"));
                if (!builtin && global.key.as_utf8() != Some("print"))
                    || call.args.fixed.len() > 4
                    || builtin != call.fastcall.is_some()
                {
                    return None;
                }
                cost += if builtin { 2 } else { 4 };
                for argument in &call.args.fixed {
                    let argument = operand_cost(argument, 0)?;
                    cost += if builtin && call.args.fixed.len() <= 2 {
                        argument
                    } else {
                        argument.max(1)
                    };
                }
                if layout.home != home
                    || !layout.arguments_unaliased
                    || !matches!((target, layout.results),
                        (Some(_), Some(ResultPack::Fixed(pack))) if pack.start.index() == home.slot() && pack.len == 1)
                        && !(target.is_none() && layout.results == Some(ResultPack::Ignore))
                {
                    return None;
                }
            }
            HirExpr::Closure(closure) if target == Some(*result) => {
                let Some(HirClosureCreation::Fresh { template: identity }) = closure.creation
                else {
                    return None;
                };
                if template.replace(identity).is_some()
                    || closure.captures.is_empty()
                    || closure.captures.iter().any(|capture| {
                        capture.mode != HirCaptureMode::ByValue
                            || !matches!(capture.binding, HirBinding::Local(_))
                    })
                    || facts.operation_result_home(closure.source_site?) != Some(home)
                    || !facts.operation_result_reference_unaliased(closure.source_site?)
                {
                    return None;
                }
                result_slot = Some(home.slot());
                cost += 10;
                let child = &protos[closure.proto.index()];
                if !child.params.is_empty()
                    || child.signature.is_vararg
                    || !child.children.is_empty()
                    || !child.mutable_upvalues.is_empty()
                    || !matches!(child.body.stmts.as_slice(), [HirStmt::Return(ret)]
                        if ret.values.tail.is_none() && matches!(ret.values.fixed.as_slice(), [HirExpr::UpvalueRef(_)]))
                {
                    return None;
                }
            }
            _ => return None,
        }
        if let Some(local) = target
            && !facts
                .complete_local_definition_write_homes(local)
                .iter()
                .copied()
                .eq([home])
        {
            return None;
        }
        steps.push((target, value, home.slot()));
    }
    let result_slot = result_slot?;
    if cost > 25 || steps.iter().filter(|step| step.0.is_some()).count() > 15 {
        return None;
    }
    if !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(pack)
        if pack.start.index() == result_slot && pack.len == 1)
    {
        return None;
    }
    let names = steps
        .iter()
        .filter_map(|(local, _, _)| {
            let local = (*local)?;
            Some((local, proto.local_debug_hints[local.index()].clone()?))
        })
        .collect();
    Some(Factory {
        template: template?,
        parameter: proto.params[0],
        steps,
        result: *result,
        result_slot,
        names,
    })
}

struct Match<'a> {
    factory: &'a Factory,
    facts: &'a ProtoPromotionFacts,
    offset: usize,
    argument: Option<i64>,
    bindings: BTreeMap<LocalId, LocalId>,
    site: Option<HirSourceSite>,
    proto: &'a HirProto,
    nils: &'a BTreeSet<LocalId>,
}

impl Match<'_> {
    fn constant(&self, value: &HirExpr) -> Option<i64> {
        if let Some(value) = integer(value) {
            return Some(value);
        }
        match value {
            HirExpr::ParamRef(param) if *param == self.factory.parameter => self.argument,
            HirExpr::Integer(value) => Some(*value),
            HirExpr::Binary(binary) => {
                let lhs = self.constant(&binary.lhs)?;
                let rhs = self.constant(&binary.rhs)?;
                let value = match binary.op {
                    crate::hir::HirBinaryOpKind::Add => lhs.checked_add(rhs),
                    crate::hir::HirBinaryOpKind::Sub => lhs.checked_sub(rhs),
                    crate::hir::HirBinaryOpKind::Mul => lhs.checked_mul(rhs),
                    _ => None,
                }?;
                // 小整数域在 pinned Luau 的 double 常量折叠中精确；不按相近浮点值匹配。
                i32::try_from(value).ok().map(i64::from)
            }
            _ => None,
        }
    }

    fn expression(&mut self, expected: &HirExpr, actual: &HirExpr) -> bool {
        if let HirExpr::ParamRef(param) = expected {
            let Some(value) = integer(actual) else {
                return false;
            };
            if *param != self.factory.parameter || !(-32768..=32767).contains(&value) {
                return false;
            }
            return *self.argument.get_or_insert(value) == value;
        }
        if let Some(value) = integer(actual) {
            return self.constant(expected) == Some(value);
        }
        match (expected, actual) {
            (HirExpr::LocalRef(left), HirExpr::LocalRef(right)) => {
                self.bindings.get(left) == Some(right)
            }
            (HirExpr::Nil, HirExpr::Nil) => true,
            (HirExpr::String(left), HirExpr::String(right)) => left == right,
            (HirExpr::Call(left), HirExpr::Call(right)) => {
                let (HirExpr::GlobalRef(left_name), HirExpr::GlobalRef(right_name)) =
                    (&left.callee, &right.callee)
                else {
                    return false;
                };
                left_name.key == right_name.key
                    && left.method == HirMethodCall::None
                    && right.method == HirMethodCall::None
                    && left.args.tail.is_none()
                    && right.args.tail.is_none()
                    && left.args.fixed.len() == right.args.fixed.len()
                    && left.fastcall.map(|protocol| protocol.builtin())
                        == right.fastcall.map(|protocol| protocol.builtin())
                    && left
                        .args
                        .fixed
                        .iter()
                        .zip(&right.args.fixed)
                        .all(|(left, right)| self.expression(left, right))
            }
            (HirExpr::Closure(left), HirExpr::Closure(right)) => {
                if left.creation != right.creation || left.captures.len() != right.captures.len() {
                    return false;
                }
                self.site = right.source_site;
                left.captures.iter().zip(&right.captures).all(|(left, right)| {
                    matches!((left.binding, right.binding), (HirBinding::Local(left_local), HirBinding::Local(right_local))
                        if left.mode == HirCaptureMode::ByValue && right.mode == left.mode
                            && self.bindings.get(&left_local) == Some(&right_local))
                })
            }
            _ => false,
        }
    }

    fn step(&mut self, expected: &(Option<LocalId>, HirExpr, usize), actual: &HirStmt) -> bool {
        let (target, value, home) = if let Some((target, value)) = scalar_local(actual) {
            (
                Some(target),
                value.clone(),
                self.facts.trusted_local_home_slot(target),
            )
        } else if let HirStmt::CallStmt(call) = actual {
            (
                None,
                HirExpr::Call(Box::new(call.call.clone())),
                frame(self.facts, &call.call).map(|layout| layout.home),
            )
        } else {
            return false;
        };
        if home != Some(HomeSlotKey::new(expected.2 + self.offset, 0))
            || target.is_some() != expected.0.is_some()
            || !self.expression(&expected.1, &value)
        {
            return false;
        }
        if let (Some(expected_local), Some(local)) = (expected.0, target) {
            // 候选拒绝[ProofIncomplete:Identity]：不让另一个 debug 身份借用相同槽位。
            if self.factory.names.get(&expected_local)
                != self.proto.local_debug_hints[local.index()].as_ref()
                || self
                    .facts
                    .complete_local_definition_write_homes(local)
                    .iter()
                    .any(|write| {
                        Some(*write) != home
                            && !(expected_local == self.factory.result
                                && *write == HomeSlotKey::new(self.offset, 0))
                    })
            {
                return false;
            }
        }
        match &value {
            HirExpr::Nil if !target.is_some_and(|local| self.nils.contains(&local)) => {
                return false;
            }
            HirExpr::Closure(closure)
                if !closure.source_site.is_some_and(|site| {
                    self.facts.operation_result_home(site) == home
                        && self.facts.operation_result_reference_unaliased(site)
                }) =>
            {
                return false;
            }
            _ => {}
        }
        if let HirExpr::Call(call) = &value {
            let Some(layout) = frame(self.facts, call) else {
                return false;
            };
            if target.is_some()
                && !call
                    .source_site
                    .is_some_and(|site| self.facts.operation_result_reference_unaliased(site))
            {
                return false;
            }
            if Some(layout.home) != home
                || !layout.arguments_unaliased
                || !matches!(layout.args, ValuePack::Fixed(pack)
                    if pack.start.index() == layout.home.slot() + 1 && pack.len == call.args.fixed.len())
                || !matches!((target, layout.results), (Some(_), Some(ResultPack::Fixed(pack)))
                    if pack.start.index() == layout.home.slot() && pack.len == 1)
                    && !(target.is_none() && layout.results == Some(ResultPack::Ignore))
            {
                return false;
            }
        }
        if let (Some(expected), Some(actual)) = (expected.0, target) {
            self.bindings.insert(expected, actual);
        }
        true
    }
}

pub(super) fn plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    root_indices: &[usize],
) -> Vec<Plan> {
    let Some(callees) = context.expanded_callees else {
        return Vec::new();
    };
    let mut plans = Vec::new();
    // 每个闭包模板只对应一个已验证函数；返回 COPY 给出窗口末端，不枚举所有起点。
    let factories = callees
        .values()
        .filter_map(|callee| {
            let Some(factories::Factory::Snapshot(factory)) = &callee.factory else {
                return None;
            };
            Some((factory.template, (callee, factory)))
        })
        .collect::<BTreeMap<_, _>>();
    if factories.is_empty() {
        return plans;
    }
    let nils = nil_bindings(facts);
    let mut flat = Vec::new();
    let mut scopes = BTreeMap::new();
    let mut scope_stack = Vec::new();
    prefix::coordinates::visit(&context.proto.body, &mut 0, &mut |index, kind, stmt| {
        if matches!(stmt, HirStmt::Block(_)) {
            if kind == PointKind::Statement {
                scope_stack.push(index);
            } else if kind == PointKind::Boundary {
                scopes.insert(scope_stack.pop().unwrap(), index);
            }
        } else if kind == PointKind::Statement {
            flat.push(Some((index, stmt)));
        } else {
            flat.push(None);
        }
    });
    let mut closures = BTreeMap::new();
    let mut consumed_end = 0;
    for (position, entry) in flat.iter().enumerate() {
        let Some((index, stmt)) = *entry else {
            closures.clear();
            continue;
        };
        if let Some((local, HirExpr::Closure(closure))) = scalar_local(stmt)
            && let Some(HirClosureCreation::Fresh { template }) = closure.creation
        {
            closures.insert(local, template);
        }
        let Some((target, HirExpr::LocalRef(source))) = scalar_local(stmt) else {
            continue;
        };
        let Some((callee, factory)) = closures
            .get(source)
            .and_then(|template| factories.get(template))
        else {
            continue;
        };
        let candidate = (|| {
            let first = position.checked_sub(factory.steps.len())?;
            let (start, _) = flat[first]?;
            if start < consumed_end {
                return None;
            }
            if root_indices[callee.declaration] >= start
                || !matches!(stmt, HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_none())
            {
                return None;
            }
            let base = facts.trusted_local_home_slot(target)?;
            if !facts
                .complete_local_definition_write_homes(target)
                .iter()
                .copied()
                .eq([base])
            {
                return None;
            }
            let mut matched = Match {
                factory,
                facts,
                offset: base.slot(),
                argument: None,
                bindings: BTreeMap::new(),
                site: None,
                proto: context.proto,
                nils: &nils,
            };
            if !factory
                .steps
                .iter()
                .zip(&flat[first..position])
                .all(|(expected, actual)| {
                    actual.is_some_and(|(_, stmt)| matched.step(expected, stmt))
                })
                || matched.bindings.get(&factory.result) != Some(source)
                || facts.trusted_local_home_slot(*source)
                    != Some(HomeSlotKey::new(base.slot() + factory.result_slot, 0))
            {
                return None;
            }
            let mut plan = factories::invocation(callee, matched.site?, base, target, start, index);
            // 只消费完整词法包装；窗口中的调用原位重发，内部声明仍逐个退休。
            for (&scope, &end) in scopes.range(start..index) {
                if end > index {
                    return None;
                }
                plan.replayed_effects.push(scope);
            }
            plan.replayed_effects
                .extend(flat[first..position].iter().filter_map(|entry| {
                    entry
                        .filter(|(_, stmt)| matches!(stmt, HirStmt::CallStmt(_)))
                        .map(|(index, _)| index)
                }));
            let HirExpr::Call(call) = &mut plan.values.fixed[0] else {
                unreachable!()
            };
            call.args.fixed.push(HirExpr::Integer(matched.argument?));
            Some(plan)
        })();
        if candidate.is_some() {
            consumed_end = index + 1;
        }
        plans.extend(candidate);
    }
    plans
}
