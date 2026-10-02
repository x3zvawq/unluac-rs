//! 核对急切读取后共享结果的原函数体及完整展开帧。
//! 短路只控制返回表达式，计数更新和两臂读取保持独立的原操作身份。

use super::*;
use crate::transformer::InstrRef;

mod live;
mod program;
pub(super) use program::{ReturnSlots, matches_return};

pub(super) fn body(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<Body> {
    let template = crate::hir::luau_inlining::calling_shared_value(proto)?;
    let [HirStmt::LocalDecl(decl), HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let HirExpr::Call(call) = &decl.values.fixed[0] else {
        return None;
    };
    let HirExpr::LogicalAnd(final_) = &ret.values.fixed[0] else {
        return None;
    };
    let HirExpr::LogicalAnd(guard) = &final_.lhs else {
        return None;
    };
    let HirExpr::Binary(compare) = &guard.rhs else {
        return None;
    };
    let HirExpr::Binary(check) = &final_.rhs else {
        return None;
    };
    let frame = facts.native_call_frame(call)?;
    let result = facts.fixed_return_input(ret, 0)?;
    let first = facts.native_binary_layout(compare)?;
    let second = facts.native_binary_layout(check)?;
    // 候选拒绝[ProofIncomplete:SharedBody]：完整函数体的读取、单返回和两次
    // 比较须使用同一原 item 槽，不能仅按表达式形状认领展开帧。
    if frame.home != HomeSlotKey::new(3, 0)
        || !matches!(frame.results, Some(ResultPack::Fixed(pack)) if pack.start.index() == 3 && pack.len == 1)
        || facts.trusted_local_home_slot(template.item) != Some(HomeSlotKey::new(3, 0))
        || !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(pack) if pack.start.index() == 4 && pack.len == 1)
        || facts.copy_value_prewrite(result)?.1 != HomeSlotKey::new(4, 0)
        || first.lhs != Some(HomeSlotKey::new(1, 0))
        || first.rhs != Some(HomeSlotKey::new(5, 0))
        || second.lhs != Some(HomeSlotKey::new(3, 0))
        || second.rhs != Some(HomeSlotKey::new(1, 0))
    {
        return None;
    }
    Some(Body {
        kind: Kind::Shared,
        fallback: template.fallback.clone(),
        selection_hit: Some(Literal::from_expr(template.hit)?),
        read_tag: Some(template.tag.clone()),
        names: proto.param_debug_hints.clone(),
        item: Some((
            template.item,
            proto.local_debug_hints[template.item.index()].clone(),
        )),
    })
}

pub(super) struct Candidate {
    pub source: crate::hir::HirSourceSite,
    pub argument: pairs::ArgumentCopy,
    pub read: reading::Read,
    pub result: TempId,
    pub target: ResultTarget,
    pub end: InstrRef,
    pub live: Option<live::Return>,
}

/// 原结果的直接消费位置；草稿只能替换该 use，不能重找形状相似的表达式。
#[derive(Clone, Copy)]
pub(super) enum ResultTarget {
    Local(LocalId),
    CallArgument(crate::hir::HirSourceSite, usize),
    ComparisonOperand(crate::hir::HirSourceSite, usize),
}

impl ResultTarget {
    fn local(&self) -> Option<LocalId> {
        match self {
            Self::Local(local) => Some(*local),
            _ => None,
        }
    }
}

impl Candidate {
    pub fn flag(&self) -> HirExpr {
        self.live
            .as_ref()
            .map_or(HirExpr::Nil, |value| HirExpr::LocalRef(value.flag))
    }
}

pub(super) fn call(stmt: &HirStmt) -> Option<&HirCallExpr> {
    match stmt {
        HirStmt::CallStmt(stmt) => Some(&stmt.call),
        stmt => match scalar_local(stmt)?.1 {
            HirExpr::Call(call) => Some(call),
            _ => None,
        },
    }
}

pub(super) fn candidates(proto: &HirProto, facts: &ProtoPromotionFacts) -> Vec<Candidate> {
    let mut copies = BTreeMap::new();
    for copy in facts.unread_copies() {
        if let Some(local) = facts.promoted_local_for_temp(copy.write.target) {
            copies
                .entry(local)
                .and_modify(|entry| *entry = None)
                .or_insert(Some(copy));
        }
    }
    let mut output = Vec::new();
    let mut pending = vec![&proto.body];
    while let Some(block) = pending.pop() {
        for window in block.stmts.windows(4) {
            let candidate = (|| {
                let (local, HirExpr::LocalRef(input)) = scalar_local(&window[0])? else {
                    return None;
                };
                if !pairs::scalar_write(&window[0]) {
                    return None;
                }
                let copy = (*copies.get(&local)?)?;
                let read = reading::match_read(facts, &window[1], &window[2])?;
                let reading::Value::Unused { .. } = read.value else {
                    return None;
                };
                let site = |instr| crate::hir::HirSourceSite {
                    proto: proto.id,
                    instr,
                };
                let result = facts.operation_result_temp(site(read.end))?;
                let home = facts.trusted_temp_home_slot(result)?;
                let target = if let Some((local, HirExpr::Nil)) = scalar_local(&window[3]) {
                    if !pairs::scalar_write(&window[3])
                        || facts.promoted_local_for_temp(result) != Some(local)
                        || facts.nil_write_temps(result)? != [result]
                    {
                        return None;
                    }
                    ResultTarget::Local(local)
                } else {
                    let call = call(&window[3])?;
                    let source = call.source_site?;
                    if source.instr.index() != read.end.index() + 1 || call.args.tail.is_some() {
                        return None;
                    }
                    let argument =
                        call.args
                            .fixed
                            .iter()
                            .enumerate()
                            .find_map(|(index, value)| {
                                (*value == HirExpr::Nil
                                    && facts.call_argument_value(call, index) == Some(result)
                                    && facts
                                        .call_argument_preparation_instruction(call, index, value)
                                        == Some(read.end))
                                .then_some(index)
                            })?;
                    ResultTarget::CallArgument(source, argument)
                };
                // 候选拒绝[ProofIncomplete:SharedFrame]：COPY、急切读取和 nil 返回
                // 是同一连续原帧；低槽输入不参与这些高槽的覆盖。
                if read.source.instr.index() != copy.instruction.index() + 1
                    || facts.promoted_local_for_temp(copy.write.source?) != Some(*input)
                    || copy.write.target_home.slot() != home.slot() + 1
                    || read.home.slot() != home.slot() + 2
                    || copy.write.source_home.slot() >= home.slot()
                    || read.inputs.iter().any(|input| input.slot() >= home.slot())
                {
                    return None;
                }
                Some(Candidate {
                    source: site(copy.instruction),
                    argument: pairs::ArgumentCopy {
                        body_pc: copy.after_pc,
                        local,
                        input: copy.write.target,
                        source: copy.write.source?,
                    },
                    end: InstrRef(read.end.index() + 1),
                    read,
                    result,
                    target,
                    live: None,
                })
            })();
            output.extend(candidate);
        }
        for stmt in &block.stmts {
            crate::hir::visit::for_each_nested_block(stmt, &mut |child| pending.push(child));
        }
    }
    output.extend(live::candidates(proto, facts));
    output
}

pub(super) fn prepare(
    draft: &mut HirProto,
    original: &HirProto,
    facts: &ProtoPromotionFacts,
    templates: &Templates,
    invocations: &[index::SharedInvocation],
) -> Option<()> {
    if invocations.is_empty() {
        return Some(());
    }
    for invocation in invocations {
        let candidate = &invocation.candidate;
        let argument = candidate.argument;
        let end = candidate.end;
        if original.local_debug_hints[argument.local.index()].is_some()
            || original.local_debug_scopes[argument.local.index()].is_some()
        {
            let scope = original
                .debug_scopes
                .get(original.local_debug_scopes[argument.local.index()]?)?
                .as_ref()?;
            let name = &templates.bodies[invocation.callee.child.index()]
                .as_ref()?
                .names[1];
            if scope.start_pc != argument.body_pc
                || scope.end_instr != Some(end)
                || scope.initializer_temp != Some(argument.input)
                || name.is_none()
                || &original.local_debug_hints[argument.local.index()] != name
            {
                return None;
            }
            draft.local_debug_hints[argument.local.index()] = None;
            draft.local_debug_scopes[argument.local.index()] = None;
            draft.temp_debug_locals[argument.input.index()] = None;
            draft.temp_debug_scopes[argument.input.index()] = None;
        }
        if candidate.live.is_some() {
            live::prepare(draft, original, templates, invocation)?;
            continue;
        }
        let reading::Value::Unused { bindings, temps } = &candidate.read.value else {
            return None;
        };
        for (&binding, &temp) in bindings.iter().zip(temps) {
            // 候选拒绝[PolicyBoundary:DebugIdentity]：两臂独立的源码声明不能随
            // 死值一起退休；当前调用只吸收没有独立 debug 身份的读取准备。
            if original.temp_debug_locals[temp.index()].is_some()
                || original.temp_debug_scopes[temp.index()].is_some()
                || matches!(binding, HirBinding::Local(local) if original.local_debug_hints[local.index()].is_some() || original.local_debug_scopes[local.index()].is_some())
            {
                return None;
            }
        }
    }
    let by_source = invocations
        .iter()
        .map(|invocation| (invocation.candidate.read.source, invocation))
        .collect::<BTreeMap<_, _>>();
    fn rewrite(
        block: &mut HirBlock,
        facts: &ProtoPromotionFacts,
        by_source: &BTreeMap<crate::hir::HirSourceSite, &index::SharedInvocation>,
        count: &mut usize,
    ) -> Option<()> {
        let mut removed = vec![false; block.stmts.len()];
        let mut index = 0;
        while index + 2 < block.stmts.len() {
            let source = match scalar_local(&block.stmts[index]) {
                Some((_, HirExpr::Binary(binary))) => binary.source_site,
                _ => None,
            };
            let Some(invocation) = source.and_then(|source| by_source.get(&source)) else {
                index += 1;
                continue;
            };
            let candidate = &invocation.candidate;
            if reading::match_read(facts, &block.stmts[index], &block.stmts[index + 1])?
                != candidate.read
            {
                return None;
            }
            let value = factories::factory_call(
                invocation.callee.local,
                Some(candidate.source),
                vec![
                    candidate.flag(),
                    HirExpr::LocalRef(candidate.argument.local),
                    HirExpr::LocalRef(invocation.reader.local),
                ]
                .into(),
            );
            let result_index = if let Some(live) = &candidate.live {
                let initial_index = index + 2 + usize::from(live.release.is_some());
                if live.release.is_some_and(|local| {
                    block.stmts.get(index + 2) != Some(&HirStmt::LocalRootRelease(local))
                }) || scalar_local(block.stmts.get(initial_index)?)
                    != Some((live.initial, &HirExpr::LocalRef(live.flag)))
                {
                    return None;
                }
                let result_index =
                    initial_index + 1 + usize::from(live.consumer_declaration.is_some());
                if let Some(local) = live.consumer_declaration
                    && !matches!(block.stmts.get(initial_index + 1), Some(HirStmt::LocalDecl(decl))
                        if decl.bindings == [local] && decl.values.is_empty()
                            && decl.initializer_merge_transaction.is_none()
                            && decl.generic_for_initializer_producer.is_none())
                {
                    return None;
                }
                if let Some(local) = candidate.target.local()
                    && scalar_local(block.stmts.get(result_index)?)
                        != Some((local, &live.expression))
                {
                    return None;
                }
                // 同 local 的预写声明由完整调用结果接替；不同 local 的预写没有独立 debug 身份。
                if candidate.target.local() == Some(live.initial) {
                    block.stmts[result_index] = block.stmts[initial_index].clone();
                }
                removed[initial_index] = true;
                result_index
            } else {
                index + 2
            };
            let next = &mut block.stmts[result_index];
            if let Some(local) = candidate.target.local() {
                if scalar_local(next).map(|(actual, _)| actual) != Some(local)
                    || candidate.live.is_none()
                        && scalar_local(next) != Some((local, &HirExpr::Nil))
                {
                    return None;
                }
                match next {
                    HirStmt::LocalDecl(decl) => decl.values = vec![value].into(),
                    HirStmt::Assign(assign) => assign.values = vec![value].into(),
                    _ => return None,
                }
            } else if let ResultTarget::CallArgument(source, argument) = candidate.target {
                let call = match next {
                    HirStmt::CallStmt(stmt) => &mut stmt.call,
                    HirStmt::LocalDecl(decl) => match decl.values.fixed.as_mut_slice() {
                        [HirExpr::Call(call)] => call,
                        _ => return None,
                    },
                    HirStmt::Assign(assign) => match assign.values.fixed.as_mut_slice() {
                        [HirExpr::Call(call)] => call,
                        _ => return None,
                    },
                    _ => return None,
                };
                if call.source_site != Some(source)
                    || call.args.fixed.get(argument) != Some(&HirExpr::Nil)
                {
                    return None;
                }
                call.args.fixed[argument] = value;
            } else if let ResultTarget::ComparisonOperand(source, operand) = candidate.target {
                live::replace_comparison(
                    next,
                    source,
                    operand,
                    &candidate.live.as_ref()?.expression,
                    value,
                )?;
            } else {
                return None;
            }
            removed[index] = true;
            removed[index + 1] = true;
            *count += 1;
            index = result_index + 1;
        }
        let mut position = 0;
        block.stmts.retain(|_| {
            let keep = !removed[position];
            position += 1;
            keep
        });
        let mut valid = Some(());
        for stmt in &mut block.stmts {
            crate::hir::simplify::walk::for_each_nested_block_mut(stmt, &mut |child| {
                if valid.is_some() {
                    valid = rewrite(child, facts, by_source, count);
                }
            });
        }
        valid
    }
    let mut count = 0;
    rewrite(&mut draft.body, facts, &by_source, &mut count)?;
    (count == invocations.len()).then_some(())
}

pub(super) fn plans(
    invocations: &[index::SharedInvocation],
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
) -> Vec<Plan> {
    let Some(callees) = context.expanded_callees else {
        return Vec::new();
    };
    let by_source = invocations
        .iter()
        .filter(|invocation| invocation.candidate.target.local().is_some())
        .map(|invocation| (invocation.candidate.source, invocation))
        .collect::<BTreeMap<_, _>>();
    if by_source.is_empty() {
        return Vec::new();
    }
    let mut points = Vec::new();
    prefix::coordinates::visit(&context.proto.body, &mut 0, &mut |index, kind, stmt| {
        points.push((kind == PointKind::Statement).then_some((index, stmt)));
    });
    points
        .windows(2)
        .chain(points.windows(3))
        .filter_map(|window| {
            let (start, copy, sink, result, release) = match window {
                [Some((start, copy)), Some((sink, result))] => {
                    (*start, *copy, *sink, *result, None)
                }
                [
                    Some((start, copy)),
                    Some((_, HirStmt::LocalRootRelease(local))),
                    Some((sink, result)),
                ] => (*start, *copy, *sink, *result, Some(*local)),
                _ => return None,
            };
            let (local, HirExpr::Call(call)) = scalar_local(result)? else {
                return None;
            };
            let source = call.required_luau_inlining?;
            let invocation = by_source.get(&source)?;
            let candidate = &invocation.candidate;
            let callee = callees.get(&(
                HirLuauInliningBody::CallingSharedValue {
                    template: invocation.callee.child.index(),
                },
                "".into(),
            ))?;
            let base = facts.trusted_temp_home_slot(candidate.result)?;
            if sink != start + window.len() - 1
                || release != candidate.live.as_ref().and_then(|value| value.release)
                || candidate.target.local() != Some(local)
                || callee.local != invocation.callee.local
                || !pairs::scalar_write(result)
                || facts.promoted_local_for_temp(candidate.result) != Some(local)
            {
                return None;
            }
            let run = [copy, result];
            let mut builder =
                frame_builder(context, &run, facts, DecompileDialect::Luau, base.slot())?;
            let call =
                builder.expanded_calling_value(call, 1, base.slot(), Some(candidate.result))?;
            if builder.first_event != Some(0) || builder.next_event != 1 {
                return None;
            }
            // release 仍留在草稿及 removed 中，由 preview 核对其旧 epoch 同批退休。
            let mut plan = factories::invocation(callee, source, base, local, start, sink);
            plan.values = vec![HirExpr::Call(Box::new(call))].into();
            if matches!(result, HirStmt::Assign(_)) {
                plan.result_locals.clear();
                plan.assignment_targets = vec![HirLValue::Local(local)];
            }
            Some(plan)
        })
        .collect()
}
