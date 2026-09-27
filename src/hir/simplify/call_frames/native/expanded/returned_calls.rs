//! 恢复只读捕获产生 callable 后返回标签与调用结果的 Luau 展开帧。
//!
//! 两个低返回槽、内部资源绑定及高 CALL/COPY 一起配对；后缀沿用完整帧事务，
//! 不能把仍由后续调用读取的资源根当成普通别名单独消除。

use super::*;

#[derive(Clone)]
pub(super) struct Body {
    pub(super) label: crate::LuaString,
    producer: HirCallExpr,
    names: BTreeSet<String>,
    normalization: Option<(HirBlock, HirProto)>,
}

pub(super) fn body(proto: &HirProto) -> Option<Body> {
    if !proto.params.is_empty()
        || proto.signature.is_vararg
        || !proto.children.is_empty()
        || proto.upvalues.is_empty()
        || !proto.mutable_upvalues.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let (HirStmt::Return(ret), prefix) = proto.body.stmts.split_last()? else {
        return None;
    };
    let ([HirExpr::String(label)], Some(tail)) = (ret.values.fixed.as_slice(), &ret.values.tail)
    else {
        return None;
    };
    let HirExpr::Call(last) = tail.as_expr() else {
        return None;
    };
    if tail.exact_width().is_some()
        || !last.args.is_empty()
        || last.is_method()
        || last.fastcall.is_some()
    {
        return None;
    }
    let HirExpr::LocalRef(result) = last.callee else {
        return None;
    };
    let mut aliases = BTreeSet::new();
    let mut producer = None;
    for stmt in prefix {
        let (local, value) = scalar_local(stmt)?;
        if !matches!(stmt, HirStmt::LocalDecl(_)) {
            return None;
        }
        match value {
            HirExpr::Call(call) if producer.is_none() && supported_producer(call) => {
                producer = Some(call.as_ref().clone());
            }
            HirExpr::LocalRef(source) if aliases.contains(source) => {}
            _ => return None,
        }
        aliases.insert(local);
    }
    aliases.contains(&result).then_some(Body {
        label: label.clone(),
        producer: producer?,
        names: aliases
            .iter()
            .filter_map(|local| proto.local_debug_hints[local.index()].clone())
            .collect(),
        normalization: None,
    })
}

pub(super) fn prepare_body(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    identity: Option<&HirProto>,
) -> Option<Body> {
    if let Some(body) = body(proto) {
        return Some(body);
    }
    let [first, copy, label, callee, HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let (input, HirExpr::Call(producer)) = scalar_local(first)? else {
        return None;
    };
    let (result, HirExpr::LocalRef(source)) = scalar_local(copy)? else {
        return None;
    };
    let (label_local, HirExpr::String(label)) = scalar_local(label)? else {
        return None;
    };
    let (callee_local, HirExpr::LocalRef(callable)) = scalar_local(callee)? else {
        return None;
    };
    let tail = ret.values.tail.as_ref()?;
    let HirExpr::Call(last) = tail.as_expr() else {
        return None;
    };
    let hint = proto.local_debug_hints[input.index()].as_ref()?;
    let template = identity?;
    if !proto.params.is_empty()
        || proto.signature.is_vararg
        || !proto.children.is_empty()
        || proto.failure.is_some()
        || !proto.mutable_upvalues.is_empty()
        || proto.body.stmts[..4]
            .iter()
            .any(|stmt| !matches!(stmt, HirStmt::LocalDecl(_)))
        || *source != input
        || *callable != result
        || !supported_producer(producer)
        || proto.local_debug_hints[label_local.index()].is_some()
        || proto.local_debug_hints[callee_local.index()].is_some()
        || ret.values.fixed != [HirExpr::LocalRef(label_local)]
        || tail.exact_width().is_some()
        || last.callee != HirExpr::LocalRef(callee_local)
        || !last.args.is_empty()
        || last.fastcall.is_some()
        || last.is_method()
        || facts.trusted_local_home_slot(input) != Some(HomeSlotKey::new(1, 0))
        || facts.trusted_local_home_slot(result) != Some(HomeSlotKey::new(0, 0))
        || facts.trusted_local_home_slot(label_local) != Some(HomeSlotKey::new(1, 0))
        || facts.native_call_frame(producer)?.home != HomeSlotKey::new(1, 0)
        || facts.native_call_frame(last)?.home != HomeSlotKey::new(2, 0)
        || !matches!(facts.native_return_frame(ret)?.values, ValuePack::Open(start) if start.index() == 1)
    {
        return None;
    }
    let temp = facts.operation_result_temp(producer.source_site?)?;
    let scope = proto
        .debug_scopes
        .get(proto.local_debug_scopes[input.index()]?)?
        .as_ref()?;
    if scope.initializer_temp != Some(temp)
        || scope.initializer_end_instr != Some(producer.source_site?.instr)
        || scope.end_instr?.index() != producer.source_site?.instr.index() + 2
        || !matches!(facts.native_call_frame(producer)?.results, Some(ResultPack::Fixed(pack)) if pack.start.index() == 1 && pack.len == 1)
    {
        return None;
    }
    if !matches!(facts.trusted_immediate_moves(temp)?, [copy] if copy.source_home == HomeSlotKey::new(1,0)
        && copy.target_home == HomeSlotKey::new(0,0) && facts.promoted_local_for_temp(copy.target) == Some(result))
    {
        return None;
    }
    let restrictions = frame_restrictions(proto, facts);
    let context = NativeFrameContext {
        proto,
        rk_literals: None,
        expanded_callees: None,
        retired_roots: None,
        barred: &restrictions.barred,
        closed: &restrictions.closed,
        callee_aliases: &restrictions.callee_aliases,
        constants_fit_rk: tables::constants_fit_rk(proto),
    };
    let return_run = [&proto.body.stmts[2], &proto.body.stmts[3]];
    let returned_plan = return_plan(context, &return_run, facts, DecompileDialect::Luau, ret)?;
    if returned_plan.start != 0
        || returned_plan.values.fixed != [HirExpr::String(label.clone())]
        || !matches!(returned_plan.values.tail.as_ref()?.as_expr(), HirExpr::Call(call) if call.callee == HirExpr::LocalRef(result))
    {
        return None;
    }
    // 原高槽 debug 形参及低槽返回 COPY 是恒等调用的完整展开帧。
    // 直接匿名 identity 会被 O2 在创建闭包前内联，不新增 capture 或运行时分配。
    let mut wrapper = template.clone();
    wrapper.param_debug_hints = vec![Some(hint.clone())];
    wrapper.source = proto.source.clone();
    wrapper.line_range = proto.line_range;
    if let [HirStmt::Return(ret)] = wrapper.body.stmts.as_mut_slice() {
        ret.frame_source = None;
    }
    let mut invocation = producer.as_ref().clone();
    invocation.source_site = None;
    invocation.required_luau_inlining = producer.source_site;
    invocation.argument_roots.clear();
    invocation.frame_root_ends.clear();
    invocation.callee = HirExpr::Closure(Box::new(crate::hir::HirClosureExpr {
        source_site: None,
        creation: None,
        proto: wrapper.id,
        captures: Vec::new(),
    }));
    invocation.args = vec![HirExpr::Call(producer.clone())].into();
    let HirStmt::LocalDecl(mut decl) = copy.clone() else {
        return None;
    };
    decl.values = vec![HirExpr::Call(Box::new(invocation))].into();
    let mut returned = ret.clone();
    returned.values = returned_plan.values;
    let normalized = HirBlock {
        stmts: vec![HirStmt::LocalDecl(decl), HirStmt::Return(returned)],
    };
    Some(Body {
        label: label.clone(),
        producer: producer.as_ref().clone(),
        names: [input, result]
            .into_iter()
            .filter_map(|local| proto.local_debug_hints[local.index()].clone())
            .collect(),
        normalization: Some((normalized, wrapper)),
    })
}

pub(super) fn publish(
    body: &Body,
    proto: &mut HirProto,
    id: crate::hir::HirProtoRef,
) -> Option<HirProto> {
    let (mut block, mut wrapper) = body.normalization.clone()?;
    let HirStmt::LocalDecl(decl) = &mut block.stmts[0] else {
        unreachable!()
    };
    let HirExpr::Call(call) = &mut decl.values.fixed[0] else {
        unreachable!()
    };
    let HirExpr::Closure(closure) = &mut call.callee else {
        unreachable!()
    };
    closure.proto = id;
    wrapper.id = id;
    proto.inline_dispositions.preserve_local(
        decl.bindings[0],
        HirInlineRetentionReason::PhysicalFramePrefix,
    );
    proto.body = block;
    proto.children.push(id);
    Some(wrapper)
}

fn supported_producer(call: &HirCallExpr) -> bool {
    if call.is_method() || call.fastcall.is_some() || call.args.tail.is_some() {
        return false;
    }
    match (&call.callee, call.args.fixed.as_slice()) {
        (HirExpr::UpvalueRef(_), []) => true,
        (HirExpr::TableAccess(access), [HirExpr::Call(argument)]) => {
            matches!(access.base, HirExpr::UpvalueRef(_))
                && matches!(access.key, HirExpr::Integer(1..=256))
                && matches!(argument.callee, HirExpr::UpvalueRef(_))
                && argument.args.is_empty()
                && !argument.is_method()
                && argument.fastcall.is_none()
        }
        _ => false,
    }
}

fn same_expression(expected: &HirExpr, actual: &HirExpr, captures: &[LocalId]) -> bool {
    match (expected, actual) {
        (HirExpr::UpvalueRef(upvalue), HirExpr::LocalRef(local)) => {
            captures.get(upvalue.index()) == Some(local)
        }
        (HirExpr::Integer(left), HirExpr::Integer(right)) => left == right,
        (HirExpr::TableAccess(left), HirExpr::TableAccess(right)) => {
            same_expression(&left.base, &right.base, captures)
                && same_expression(&left.key, &right.key, captures)
        }
        (HirExpr::Call(left), HirExpr::Call(right)) => same_call(left, right, captures),
        _ => false,
    }
}

fn same_call(expected: &HirCallExpr, actual: &HirCallExpr, captures: &[LocalId]) -> bool {
    expected.method == actual.method
        && actual.fastcall.is_none()
        && actual.args.tail.is_none()
        && expected.args.fixed.len() == actual.args.fixed.len()
        && same_expression(&expected.callee, &actual.callee, captures)
        && expected
            .args
            .fixed
            .iter()
            .zip(&actual.args.fixed)
            .all(|(left, right)| same_expression(left, right, captures))
}

pub(super) fn plans(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let Some(callees) = context.expanded_callees else {
        return Vec::new();
    };
    let mut plans = Vec::new();
    let mut floor = 0;
    let stmts = &context.proto.body.stmts;
    for (sink, stmt) in stmts.iter().enumerate() {
        if sink < floor {
            continue;
        }
        if scalar_local(stmt).is_none() {
            floor = sink + 1;
            continue;
        }
        let mut closed_pair = false;
        let candidate = (|| {
            let (second, HirExpr::LocalRef(source)) = scalar_local(stmt)? else {
                return None;
            };
            let (call_owner, HirExpr::Call(last)) = scalar_local(stmts.get(sink.checked_sub(1)?)?)?
            else {
                return None;
            };
            if source != &call_owner
                || !last.args.is_empty()
                || last.is_method()
                || last.fastcall.is_some()
            {
                return None;
            }
            let (callee_copy, HirExpr::LocalRef(resource)) =
                scalar_local(stmts.get(sink.checked_sub(2)?)?)?
            else {
                return None;
            };
            if last.callee != HirExpr::LocalRef(callee_copy) {
                return None;
            }
            let (first, HirExpr::String(label)) = scalar_local(stmts.get(sink.checked_sub(3)?)?)?
            else {
                return None;
            };
            // 这次 CALL/COPY 已结束一个完整返回对。即使模板或证明拒绝，也不能
            // 让后续候选再次扫描这个准备区，或把其中事件当作自己的 producer。
            closed_pair = true;
            let callee =
                callees.get(&(HirLuauInliningBody::CapturedCallablePair, label.clone()))?;
            let body = callee.returned_call.as_ref()?;
            let base = facts.trusted_local_home_slot(first)?;
            let resource_home = HomeSlotKey::new(base.slot() + 2, 0);
            let high = HomeSlotKey::new(base.slot() + 3, 0);
            if facts.trusted_local_home_slot(second) != Some(HomeSlotKey::new(base.slot() + 1, 0))
                || facts.trusted_local_home_slot(*resource) != Some(resource_home)
                || facts.native_call_frame(last)?.home != high
            {
                return None;
            }
            let result = facts.operation_result_temp(last.source_site?)?;
            let [copy] = facts.trusted_immediate_moves(result)? else {
                return None;
            };
            if copy.target_home != HomeSlotKey::new(base.slot() + 1, 0)
                || facts.promoted_local_for_temp(copy.target) != Some(second)
            {
                return None;
            }
            let tail_run = [&stmts[sink - 2]];
            let mut tail_builder = frame_builder(
                context,
                &tail_run,
                facts,
                DecompileDialect::Luau,
                high.slot(),
            )?;
            let tail = tail_builder.call(last, 1, high.slot(), false, CallWidth::Single)?;
            if tail_builder.next_event != 1 || tail.callee != HirExpr::LocalRef(*resource) {
                return None;
            }
            let initializer = sink.checked_sub(4)?;
            let (owner, value) = scalar_local(&stmts[initializer])?;
            if owner != *resource {
                return None;
            }
            let (call_index, call) = match value {
                HirExpr::Call(call) => (initializer, call.as_ref()),
                HirExpr::LocalRef(producer) => {
                    let index = initializer.checked_sub(1)?;
                    let (owner, HirExpr::Call(call)) = scalar_local(&stmts[index])? else {
                        return None;
                    };
                    if owner != *producer {
                        return None;
                    }
                    let temp = facts.operation_result_temp(call.source_site?)?;
                    let [copy] = facts.trusted_immediate_moves(temp)? else {
                        return None;
                    };
                    if copy.target_home != resource_home
                        || copy.source_home != high
                        || facts.promoted_local_for_temp(copy.target) != Some(*resource)
                    {
                        return None;
                    }
                    (index, call.as_ref())
                }
                _ => return None,
            };
            let frame = facts.native_call_frame(call)?;
            let producer = facts.operation_result_temp(call.source_site?)?;
            let copied_resource = facts.trusted_immediate_moves(producer).is_some_and(|moves|
                matches!(moves, [copy] if copy.source_home == high && copy.target_home == resource_home
                    && facts.promoted_local_for_temp(copy.target) == Some(*resource)));
            if frame.home != resource_home && !(frame.home == high && copied_resource)
                || !matches!(frame.results, Some(ResultPack::Fixed(pack)) if pack.len == 1 && pack.start.index() == frame.home.slot())
                || !matches!(facts.native_call_frame(last)?.results, Some(ResultPack::Fixed(pack)) if pack.len == 1 && pack.start.index() == high.slot())
                || call_index < floor
            {
                return None;
            }
            let run = stmts[floor..call_index].iter().collect::<Vec<_>>();
            let mut builder = frame_builder(
                context,
                &run,
                facts,
                DecompileDialect::Luau,
                frame.home.slot(),
            )?;
            let rebuilt =
                builder.call(call, run.len(), frame.home.slot(), false, CallWidth::Single)?;
            if builder.first_event.is_some() && builder.next_event != run.len()
                || !same_call(&body.producer, &rebuilt, &callee.readonly_captures)
            {
                return None;
            }
            let start = floor + builder.first_event.unwrap_or(run.len());
            if start <= callee.declaration {
                return None;
            }
            // 内部 debug local 只由原函数的同名绑定承接；返回接收者仍留在 caller。
            for stmt in &stmts[start..sink - 3] {
                let (local, _) = scalar_local(stmt)?;
                if context.proto.local_debug_hints[local.index()]
                    .as_ref()
                    .is_some_and(|name| !body.names.contains(name))
                {
                    return None;
                }
            }
            let invocation =
                factories::factory_call(callee.local, last.source_site, HirValuePack::default());
            let mut plan =
                factories::invocation(callee, last.source_site?, base, first, start, sink);
            plan.values = HirValuePack {
                fixed: Vec::new(),
                tail: Some(HirPackTail::exact(invocation, 2)),
            };
            plan.result_locals.push(second);
            // 对已有低槽的两项写回属于同一个返回包，不能留下临时接收声明抬高后缀。
            if let (Some(HirStmt::Assign(left)), Some(HirStmt::Assign(right))) =
                (stmts.get(sink + 1), stmts.get(sink + 2))
                && left.values.fixed.as_slice() == [HirExpr::LocalRef(first)]
                && left.values.tail.is_none()
                && right.values.fixed.as_slice() == [HirExpr::LocalRef(second)]
                && right.values.tail.is_none()
                && let ([HirLValue::Local(a)], [HirLValue::Local(b)]) =
                    (left.targets.as_slice(), right.targets.as_slice())
                && a != b
                && [a, b].iter().all(|local| {
                    facts
                        .trusted_local_home_slot(**local)
                        .is_some_and(|home| home.slot() < base.slot())
                })
            {
                plan.result_locals.clear();
                plan.assignment_targets = vec![HirLValue::Local(*a), HirLValue::Local(*b)];
                plan.sink = sink + 2;
                plan.removed = (start..plan.sink).collect();
            }
            Some(plan)
        })();
        if let Some(plan) = candidate {
            floor = plan.sink + 1;
            plans.push(plan);
        } else if closed_pair {
            floor = sink + 1;
        }
    }
    plans
}
