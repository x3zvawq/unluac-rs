//! 恢复数组数值遍历的双结果展开帧。
//! 消费原循环、操作 home 和状态 COPY；嵌套调用点使用共享坐标，后缀仍由整批事务验证。

use super::super::assignments::plain_copy;
use super::*;
use crate::hir::luau_inlining::{ArrayFoldTemplate, small_integer};

pub(super) struct Recovered {
    pub draft: Option<HirProto>,
    pub obligations: Vec<(crate::hir::HirSourceSite, LocalId)>,
    pub plans: Vec<Plan>,
    pub result_slots: BTreeMap<crate::hir::HirSourceSite, usize>,
}

struct Candidate<'a> {
    callee: &'a Callee,
    source: crate::hir::HirSourceSite,
    base: usize,
    first: LocalId,
    second: LocalId,
    begin: usize,
    end: usize,
    replayed: std::ops::Range<usize>,
    inputs: [LocalId; 2],
    arguments: Vec<HirStmt>,
    debug: Vec<(LocalId, TempId)>,
}

fn lookup(
    expr: &HirExpr,
    input: LocalId,
    index: LocalId,
    facts: &ProtoPromotionFacts,
    base: usize,
) -> bool {
    let HirExpr::TableAccess(access) = expr else {
        return false;
    };
    let Some(layout) = facts.native_table_read_layout(access) else {
        return false;
    };
    access.base == HirExpr::LocalRef(input)
        && access.key == HirExpr::LocalRef(index)
        && layout.base == HomeSlotKey::new(base + 2, 0)
        && layout.key == Some(HomeSlotKey::new(base + 8, 0))
        && facts.table_read_result_home(access) == Some(HomeSlotKey::new(base + 9, 0))
}

pub(super) fn plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    templates: &[Option<ArrayFoldTemplate>],
    names: &[Option<[Option<String>; 5]>],
) -> Recovered {
    let mut result = Recovered {
        draft: None,
        obligations: Vec::new(),
        plans: Vec::new(),
        result_slots: BTreeMap::new(),
    };
    let mut callees = BTreeMap::new();
    for callee in context
        .expanded_callees
        .into_iter()
        .flat_map(|callees| callees.values())
    {
        if let HirLuauInliningBody::ArrayFold { template } = callee.body
            && let Some(body) = &templates[template]
        {
            callees
                .entry(body.clone())
                .and_modify(|value| *value = None)
                .or_insert(Some(callee));
        }
    }
    if callees.is_empty() {
        return result;
    }
    let copies = facts
        .state_copy_frames()
        .filter_map(|copy| {
            Some((
                (
                    facts.promoted_local_for_temp(copy.source?)?,
                    facts.promoted_local_for_temp(copy.target)?,
                ),
                copy,
            ))
        })
        .fold(BTreeMap::new(), |mut map, (key, copy)| {
            map.entry(key)
                .and_modify(|value| *value = None)
                .or_insert(Some(copy));
            map
        });
    let mut candidates = Vec::new();
    let uses = value_uses::ValueUses::new(context.proto);
    let mut blocks = vec![uses.tree.root_block()];
    while let Some(block) = blocks.pop() {
        let ids = uses.tree.block(block);
        for &id in ids {
            blocks.extend(uses.tree.stmt(id).children.iter().copied());
        }
        let stmts: Vec<_> = ids.iter().map(|id| uses.points[id.index()].1).collect();
        for position in 3..stmts.len().saturating_sub(2) {
            let candidate = (|| {
                let HirStmt::NumericFor(loop_) = stmts[position] else {
                    return None;
                };
                let (selected, initial) = scalar_local(stmts[position - 2])?;
                let (state, value) = scalar_local(stmts[position - 1])?;
                // debug 参数可能已由原成组初始化事务合并；仅在 builder 的局部视图拆开，
                // 真正提交仍消费原语句坐标和同一组参数求值。
                let (start, arguments) = if let HirStmt::LocalDecl(decl) = stmts[position - 3]
                    && decl.bindings.len() == 2
                    && decl.values.fixed.len() == 2
                    && decl.values.tail.is_none()
                    && plain_copy(stmts[position - 3])
                {
                    let arguments = decl
                        .bindings
                        .iter()
                        .zip(&decl.values.fixed)
                        .map(|(&binding, value)| {
                            let mut scalar = decl.clone();
                            scalar.bindings = vec![binding];
                            scalar.values = vec![value.clone()].into();
                            HirStmt::LocalDecl(scalar)
                        })
                        .collect::<Vec<_>>();
                    (position - 3, arguments)
                } else {
                    let start = position.checked_sub(4)?;
                    (start, vec![stmts[start].clone(), stmts[start + 1].clone()])
                };
                let (input, _) = scalar_local(&arguments[0])?;
                let (argument, _) = scalar_local(&arguments[1])?;
                let HirExpr::Unary(length) = &loop_.limit else {
                    return None;
                };
                let (first, first_value) = scalar_local(stmts[position + 1])?;
                let (second, second_value) = scalar_local(stmts[position + 2])?;
                let first_copy = *copies.get(&(selected, first))?.as_ref()?;
                let second_copy = *copies.get(&(state, second))?.as_ref()?;
                let base = first_copy.target_home.slot();
                let home = |offset| HomeSlotKey::new(base + offset, 0);
                let [
                    HirStmt::Assign(index),
                    HirStmt::If(exit),
                    HirStmt::Assign(update),
                ] = loop_.body.stmts.as_slice()
                else {
                    return None;
                };
                let HirExpr::Binary(compare) = &exit.cond else {
                    return None;
                };
                let [HirExpr::Binary(binary)] = update.values.fixed.as_slice() else {
                    return None;
                };
                let key = ArrayFoldTemplate {
                    initial: small_integer(initial)?,
                    start: small_integer(&loop_.start)?,
                    step: small_integer(&loop_.step)?,
                    comparison: compare.op,
                    update: binary.op,
                };
                let callee = *callees.get(&key)?.as_ref()?;
                let source = binary.source_site?;
                let frame = facts.numeric_for_body_frame(loop_)?;
                if *value != HirExpr::LocalRef(argument)
                    || *first_value != HirExpr::LocalRef(selected)
                    || *second_value != HirExpr::LocalRef(state)
                    || first_copy.source_home != home(4)
                    || first_copy.target_home != home(0)
                    || second_copy.source_home != home(5)
                    || second_copy.target_home != home(1)
                    || [
                        (input, 2),
                        (argument, 3),
                        (selected, 4),
                        (state, 5),
                        (loop_.binding, 8),
                        (first, 0),
                        (second, 1),
                    ]
                    .iter()
                    .any(|&(local, offset)| {
                        facts.trusted_local_home_slot(local) != Some(home(offset))
                    })
                    || length.op != crate::hir::HirUnaryOpKind::Length
                    || length.expr != HirExpr::LocalRef(input)
                    || facts.unary_result_home(length) != Some(home(6))
                    || loop_.control_homes != [home(8), home(6), home(7)]
                    || frame.binding_slot != base + 8
                    || frame.controls_len != 2
                    || frame.controls != [home(6), home(7), home(8)]
                    || index.targets.as_slice() != [HirLValue::Local(selected)]
                    || index.values.fixed.as_slice() != [HirExpr::LocalRef(loop_.binding)]
                    || index.values.tail.is_some()
                    || !lookup(&compare.lhs, input, loop_.binding, facts, base)
                    || compare.rhs != HirExpr::LocalRef(state)
                    || facts.native_binary_layout(compare)?.lhs != Some(home(9))
                    || facts.native_binary_layout(compare)?.rhs != Some(home(5))
                    || !matches!(exit.then_block.stmts.as_slice(), [HirStmt::Break])
                    || exit
                        .else_block
                        .as_ref()
                        .is_some_and(|other| !other.stmts.is_empty())
                    || update.targets.as_slice() != [HirLValue::Local(state)]
                    || update.values.tail.is_some()
                    || binary.lhs != HirExpr::LocalRef(state)
                    || !lookup(&binary.rhs, input, loop_.binding, facts, base)
                    || facts.native_binary_layout(binary)?.lhs != Some(home(5))
                    || facts.native_binary_layout(binary)?.rhs != Some(home(9))
                    || facts.operation_writeback(source)?.1 != home(5)
                    || callee.creation.instr >= source.instr
                    || (start..position)
                        .chain([position + 1, position + 2])
                        .any(|index| !plain_copy(stmts[index]))
                    || (base..=base + 9).any(|slot| {
                        context.closed.contains(&HomeSlotKey::new(slot, 0))
                            || context.barred.contains(&HomeSlotKey::new(slot, 0))
                    })
                {
                    // 候选拒绝[ProofIncomplete]：完整状态、操作输入与循环控制槽必须共同匹配原展开帧。
                    return None;
                }
                for (from, to, source_home, target_home) in [
                    (argument, state, home(3), home(5)),
                    (loop_.binding, selected, home(8), home(4)),
                ] {
                    let copy = *copies.get(&(from, to))?.as_ref()?;
                    if copy.source_home != source_home || copy.target_home != target_home {
                        return None;
                    }
                }
                let coordinate = |ordinal: usize| uses.points[ids[ordinal].index()].0;
                let end = coordinate(position + 2);
                let begin = coordinate(start);
                if [input, argument, selected, state, loop_.binding]
                    .iter()
                    .any(|&local| {
                        uses.reads(local, 0, begin) != 0
                            || uses.reads(local, end + 1, uses.count) != 0
                    })
                {
                    return None;
                }
                let mut debug = Vec::new();
                let role_names = names[callee.child.index()].as_ref()?;
                let binding = loop_.binding.index();
                if context.proto.local_debug_hints[binding].is_some()
                    && context.proto.local_debug_hints[binding] != role_names[4]
                {
                    return None;
                }
                for (role, local) in [input, argument, selected, state].into_iter().enumerate() {
                    if context.proto.local_debug_hints[local.index()].is_none()
                        && context.proto.local_debug_scopes[local.index()].is_none()
                    {
                        continue;
                    }
                    let scope = context.proto.debug_scopes
                        [context.proto.local_debug_scopes[local.index()]?]
                    .as_ref()?;
                    let initial = scope.initializer_temp?;
                    let initial_site = scope.initializer_end_instr?;
                    let end_site = scope.end_instr?;
                    let last_return = facts.state_copy_site(second_copy.target)?;
                    let HirExpr::TableAccess(argument_value) = scalar_local(&arguments[1])?.1
                    else {
                        return None;
                    };
                    let crate::hir::common::HirOperationSources::Single(argument_end) =
                        argument_value.sources
                    else {
                        return None;
                    };
                    let state_copy = *copies.get(&(argument, state))?.as_ref()?;
                    let expected_site = if role < 2 {
                        argument_end.instr
                    } else if role == 2 {
                        crate::transformer::InstrRef(argument_end.instr.index() + 1)
                    } else {
                        facts.state_copy_site(state_copy.target)?
                    };
                    let expected_temp = if role < 2 {
                        let HirExpr::TableAccess(access) = scalar_local(&arguments[role])?.1 else {
                            return None;
                        };
                        let crate::hir::common::HirOperationSources::Single(site) = access.sources
                        else {
                            return None;
                        };
                        facts.operation_result_temp(site)?
                    } else if role == 2 {
                        facts.operation_result_temp(crate::hir::HirSourceSite {
                            proto: context.proto.id,
                            instr: initial_site,
                        })?
                    } else {
                        state_copy.target
                    };
                    if context.proto.local_debug_hints[local.index()].is_none()
                        || context.proto.local_debug_hints[local.index()] != role_names[role]
                        || initial != expected_temp
                        || facts.promoted_local_for_temp(initial) != Some(local)
                        || initial_site != expected_site
                        || end_site.index() != last_return.index() + 1
                        || scope.initializer_phi.is_some()
                        || scope.branch_initializer.is_some()
                        || scope.ends_before_return
                    {
                        // 候选拒绝[ProofIncomplete:Binding]：只转交同一展开区间、原初始化与 child 角色共同确认的 debug 身份。
                        return None;
                    }
                    debug.push((local, initial));
                }
                Some(Candidate {
                    callee,
                    source,
                    base,
                    first,
                    second,
                    begin,
                    end,
                    replayed: coordinate(position)..coordinate(position + 1),
                    inputs: [input, argument],
                    arguments,
                    debug,
                })
            })();
            candidates.extend(candidate);
        }
    }
    if candidates
        .iter()
        .any(|candidate| !candidate.debug.is_empty())
    {
        let mut draft = context.proto.clone();
        for candidate in &candidates {
            for &(local, initial) in &candidate.debug {
                draft.local_debug_hints[local.index()] = None;
                draft.local_debug_scopes[local.index()] = None;
                draft.temp_debug_locals[initial.index()] = None;
                draft.temp_debug_scopes[initial.index()] = None;
            }
            if !candidate.debug.is_empty() {
                result
                    .obligations
                    .push((candidate.source, candidate.callee.local));
            }
        }
        result.draft = Some(draft);
    }
    let context = NativeFrameContext {
        proto: result.draft.as_ref().unwrap_or(context.proto),
        ..context
    };
    for candidate in candidates {
        let accepted = (|| {
            let Candidate {
                callee,
                source,
                base,
                first,
                second,
                begin,
                end,
                replayed,
                inputs,
                arguments,
                ..
            } = candidate;
            let argument_refs = arguments.iter().collect::<Vec<_>>();
            let run = argument_refs.as_slice();
            let mut builder = frame_builder(context, run, facts, DecompileDialect::Luau, base)?;
            let mut arguments = Vec::new();
            for (offset, local) in inputs.into_iter().enumerate() {
                let producer = builder.definition_producer(offset)?;
                arguments.push(builder.expr(
                    &HirExpr::LocalRef(local),
                    run.len(),
                    base + 2 + offset,
                    None,
                    false,
                    true,
                    Some(producer),
                )?);
            }
            if builder.first_event != Some(0) || builder.next_event != run.len() {
                return None;
            }
            let call = factories::factory_call(callee.local, Some(source), arguments.into());
            let mut plan =
                factories::invocation(callee, source, HomeSlotKey::new(base, 0), first, begin, end);
            plan.values = HirValuePack::expanding(Vec::new(), HirPackTail::exact(call, 2));
            plan.result_locals.push(second);
            plan.removed = (begin..end).collect();
            plan.replayed_effects = replayed.collect();
            Some((source, base, plan))
        })();
        if let Some((source, base, plan)) = accepted {
            result.result_slots.insert(source, base);
            result.plans.push(plan);
        }
    }
    result
}
