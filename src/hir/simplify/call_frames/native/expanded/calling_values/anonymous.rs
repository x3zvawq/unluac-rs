//! 恢复参数位置创建的读取闭包及其连续展开窗口。
//! 原闭包创建、FASTCALL 检查、捕获写入和纯返回程序共同证明整帧，不能单独删除读取效果。

use super::super::value_uses::ValueUses;
use super::*;
use crate::hir::common::{HirClosureExpr, HirSourceSite};
use crate::hir::luau_inlining::{CheckedReadTemplate, small_integer};
use crate::hir::promotion::value_programs::Region;
use crate::transformer::{InstrRef, Reg};

pub(super) fn reader(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<CheckedReadTemplate> {
    let template = crate::hir::luau_inlining::checked_read_template(proto)?;
    let [
        HirStmt::CallStmt(check),
        HirStmt::Assign(update),
        HirStmt::Return(ret),
    ] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    let call = &check.call;
    let HirExpr::Binary(compare) = &call.args.fixed[0] else {
        return None;
    };
    let HirExpr::GlobalRef(global) = &call.callee else {
        return None;
    };
    let HirOperationSources::Single(global_site) = global.sources else {
        return None;
    };
    let HirExpr::Binary(add) = &update.values.fixed[0] else {
        return None;
    };
    let source = call.source_site?;
    let frame = facts.native_fastcall_frame(call)?;
    let input = facts.comparison_result_temp(compare)?;
    let add_layout = facts.native_binary_layout(add)?;
    let compare_layout = facts.native_binary_layout(compare)?;
    if frame.home != HomeSlotKey::new(1, 0)
        || frame.results != Some(ResultPack::Ignore)
        || !matches!(frame.args, ValuePack::Fixed(pack) if pack.start.index() == 2 && pack.len == 1)
        || facts.call_argument_value(call, 0) != Some(input)
        || facts.trusted_temp_home_slot(input) != Some(HomeSlotKey::new(2, 0))
        || facts.global_read_frame(global, DecompileDialect::Luau) != Some(frame.home)
        || facts.operation_result_temp(global_site) != Some(frame.callee)
        || global_site.proto != proto.id
        || source.instr.index() != global_site.instr.index() + 1
        || compare.source_site?.instr.index() + 5 != source.instr.index()
        || compare_layout.lhs != Some(HomeSlotKey::new(0, 0))
        || compare_layout.rhs.is_some()
        || add.source_site?.instr.index() != source.instr.index() + 2
        || facts
            .binary_preparation_instruction(add, 0, &add.lhs)?
            .index()
            != source.instr.index() + 1
        || add_layout.lhs != Some(HomeSlotKey::new(2, 0))
        || add_layout.rhs.is_some()
        || facts.operation_result_home(add.source_site?) != Some(frame.home)
        || facts.upvalue_write_value(update)?
            != (facts.operation_result_temp(add.source_site?), frame.home)
        || update.upvalue_write_source?.instr.index() != source.instr.index() + 3
        || ret.frame_source?.instr.index() != source.instr.index() + 5
        || !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(pack) if pack.start.index() == 1 && pack.len == 1)
    {
        return None;
    }
    Some(template)
}

pub(super) struct Invocation {
    pub source: HirSourceSite,
    pub result: TempId,
    pub local: LocalId,
    pub callee: index::Function,
    pub reader: Box<HirClosureExpr>,
    flag: (LocalId, TempId),
    read: (LocalId, TempId),
    item: (LocalId, TempId),
    end: InstrRef,
    item_pc: u32,
    window: Vec<HirStmt>,
}

struct Window {
    source: HirSourceSite,
    result: TempId,
    local: LocalId,
    reader: Box<HirClosureExpr>,
    flag: (LocalId, TempId),
    read: (LocalId, TempId),
    item: (LocalId, TempId),
    initial: LocalId,
    end: InstrRef,
    item_pc: u32,
    key: (Literal, Literal, crate::LuaString),
}

fn window(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    templates: &Templates,
    programs: &BTreeMap<InstrRef, Option<&Region>>,
    stmts: &[&HirStmt],
    uses: &ValueUses<'_>,
) -> Option<Window> {
    let (flag, HirExpr::Binary(argument)) = scalar_local(stmts[0])? else {
        return None;
    };
    let HirExpr::LocalRef(flag_input) = argument.lhs else {
        return None;
    };
    let (read, HirExpr::Closure(closure)) = scalar_local(stmts[1])? else {
        return None;
    };
    let HirStmt::CallStmt(check) = stmts[2] else {
        return None;
    };
    let (counter, HirExpr::Binary(add)) = scalar_local(stmts[3])? else {
        return None;
    };
    let (item, constant) = scalar_local(stmts[4])?;
    let (initial, HirExpr::LocalRef(initial_flag)) = scalar_local(stmts[5])? else {
        return None;
    };
    let (local, HirExpr::LogicalAnd(final_)) = scalar_local(stmts[6])? else {
        return None;
    };
    let HirExpr::LogicalAnd(guard) = &final_.lhs else {
        return None;
    };
    let HirExpr::Binary(compare) = &guard.rhs else {
        return None;
    };
    let HirExpr::Binary(last) = &final_.rhs else {
        return None;
    };
    let HirExpr::LocalRef(value) = compare.lhs else {
        return None;
    };
    let (selected, literals) = crate::hir::luau_inlining::selection(&compare.rhs)?;
    let hit = Literal::from_expr(literals[0])?;
    let fallback = Literal::from_expr(literals[1])?;
    let template = templates.checked[closure.proto.index()].as_ref()?;
    let source = closure.source_site?;
    let site = |offset| HirSourceSite {
        proto: proto.id,
        instr: InstrRef(source.instr.index() + offset),
    };
    let program = (*programs.get(&site(6).instr)?)?;
    let base = facts.trusted_temp_home_slot(program.result)?;
    let flag_value = facts.comparison_result_temp(argument)?;
    let read_value = facts.operation_result_temp(source)?;
    let item_value = facts.operation_result_temp(site(5))?;
    let flag_frame = facts.branch_value_frame(flag_value)?;
    let value_home = facts.trusted_local_home_slot(value)?;
    let counter_home = facts.trusted_local_home_slot(counter)?;
    let input_home = facts.trusted_local_home_slot(flag_input)?;
    let call = &check.call;
    let HirExpr::GlobalRef(global) = &call.callee else {
        return None;
    };
    let frame = facts.native_fastcall_frame(call)?;
    let add_layout = facts.native_binary_layout(add)?;
    let argument_layout = facts.native_binary_layout(argument)?;
    // 候选拒绝[ProofIncomplete:AnonymousFrame]：形状、原操作位置与值版本同时匹配。
    // assert(true) 是折叠标签比较后的原调用效果，仍由恢复的读取体重新执行。
    if source.proto != proto.id
        || closure.creation.is_none()
        || closure.captures.len() != 1
        || !matches!(closure.captures.get(template.counter.index()), Some(capture) if capture.mode == HirCaptureMode::ByReference && capture.binding == HirBinding::Local(counter))
        || [0, 1, 3, 4, 5, 6]
            .iter()
            .any(|&i| !pairs::scalar_write(stmts[i]))
        || !matches!(stmts[1], HirStmt::LocalDecl(_))
        || argument.op != HirBinaryOpKind::Eq
        || small_integer(&argument.rhs).is_none()
        || argument_layout.lhs != Some(input_home)
        || argument_layout.rhs.is_some()
        || uses.writes(flag_input) != 1
        || uses.writes(value) != 1
        || flag_frame.end != source.instr
        || facts.promoted_local_for_temp(flag_value) != Some(flag)
        || facts.promoted_local_for_temp(read_value) != Some(read)
        || facts.promoted_local_for_temp(item_value) != Some(item)
        || facts.promoted_local_for_temp(program.initial?) != Some(initial)
        || facts.promoted_local_for_temp(program.result) != Some(local)
        || *initial_flag != flag
        || guard.lhs != HirExpr::LocalRef(initial)
        || compare.op != HirBinaryOpKind::Eq
        || *selected != HirExpr::LocalRef(item)
        || last.op != HirBinaryOpKind::Eq
        || last.lhs != HirExpr::LocalRef(item)
        || last.rhs != HirExpr::LocalRef(value)
        || compare.source_site != Some(site(13))
        || last.source_site != Some(site(14))
        || global.key.as_utf8() != Some("assert")
        || global.sources != HirOperationSources::Single(site(2))
        || call.source_site != Some(site(3))
        || call.is_method()
        || call.args.tail.is_some()
        || call.args.fixed != [HirExpr::Boolean(true)]
        || call.fastcall.is_none_or(|protocol| protocol.builtin() != 1)
        || frame.results != Some(ResultPack::Ignore)
        || frame.home != HomeSlotKey::new(base.slot() + 4, 0)
        || !matches!(frame.args, ValuePack::Fixed(pack) if pack.start.index() == base.slot() + 5 && pack.len == 1)
        || facts.operation_result_temp(site(2)) != Some(frame.callee)
        || facts.call_argument_preparation_instruction(call, 0, &HirExpr::Boolean(true))
            != Some(site(1).instr)
        || add.op != HirBinaryOpKind::Add
        || add.lhs != HirExpr::LocalRef(counter)
        || add.source_site != Some(site(4))
        || small_integer(&add.rhs) != Some(template.increment)
        || add_layout.lhs != Some(counter_home)
        || add_layout.rhs.is_some()
        || facts.operation_result_home(site(4)) != Some(counter_home)
        || small_integer(constant) != Some(template.result)
        || facts.trusted_temp_home_slot(flag_value) != Some(HomeSlotKey::new(base.slot() + 1, 0))
        || facts.trusted_temp_home_slot(read_value) != Some(HomeSlotKey::new(base.slot() + 2, 0))
        || facts.trusted_temp_home_slot(item_value) != Some(HomeSlotKey::new(base.slot() + 3, 0))
        || [input_home, value_home, counter_home]
            .iter()
            .any(|home| home.slot() >= base.slot())
        || proto.local_debug_hints[initial.index()].is_some()
        || proto.local_debug_scopes[initial.index()].is_some()
        || !shared::matches_return(
            program,
            shared::ReturnSlots {
                base,
                flag: HomeSlotKey::new(base.slot() + 1, 0),
                value: value_home,
                item: HomeSlotKey::new(base.slot() + 3, 0),
                selection: HomeSlotKey::new(base.slot() + 4, 0),
            },
            &hit,
            &fallback,
        )
        || program.inputs.get(&Reg(base.slot() + 1)) != Some(&flag_value)
        || program.inputs.get(&Reg(base.slot() + 3)) != Some(&item_value)
        || program
            .inputs
            .get(&Reg(value_home.slot()))
            .and_then(|temp| facts.promoted_local_for_temp(*temp))
            != Some(value)
    {
        return None;
    }
    Some(Window {
        source,
        result: program.result,
        local,
        reader: closure.clone(),
        flag: (flag, flag_value),
        read: (read, read_value),
        item: (item, item_value),
        initial,
        end: program.end,
        item_pc: program.source_pc,
        key: (hit, fallback, template.tag.clone()),
    })
}

pub(super) fn invocations(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    templates: &Templates,
) -> Vec<Invocation> {
    if proto
        .children
        .iter()
        .all(|child| templates.checked[child.index()].is_none())
    {
        return Vec::new();
    }
    let uses = ValueUses::new(proto);
    let mut functions = BTreeMap::new();
    for &(_, stmt) in &uses.points {
        let Some((local, HirExpr::Closure(closure))) = scalar_local(stmt) else {
            continue;
        };
        let Some(body) = templates.bodies[closure.proto.index()].as_ref() else {
            continue;
        };
        let Some((hit, fallback, tag)) = body
            .selection_hit
            .clone()
            .zip(Literal::from_expr(&body.fallback))
            .zip(body.read_tag.clone())
            .map(|((hit, fallback), tag)| (hit, fallback, tag))
        else {
            continue;
        };
        let Some(creation) = closure.source_site else {
            continue;
        };
        if body.kind != Kind::Shared
            || !closure.captures.is_empty()
            || closure.creation.is_none()
            || uses.writes(local) != 1
            || !matches!(stmt, HirStmt::LocalDecl(_))
        {
            continue;
        }
        functions
            .entry((hit, fallback, tag))
            .and_modify(|entry| *entry = None)
            .or_insert(Some(index::Function {
                local,
                child: closure.proto,
                creation,
                captures: Vec::new(),
            }));
    }
    let mut programs = BTreeMap::new();
    for program in facts
        .value_programs()
        .filter(|program| program.initial.is_some())
    {
        programs
            .entry(program.source)
            .and_modify(|entry| *entry = None)
            .or_insert(Some(program));
    }
    let mut output = Vec::new();
    let mut pending = vec![uses.tree.root_block()];
    while let Some(block) = pending.pop() {
        let ids = uses.tree.block(block);
        let stmts = ids
            .iter()
            .map(|id| uses.points[id.index()].1)
            .collect::<Vec<_>>();
        let positions = ids
            .iter()
            .map(|id| uses.points[id.index()].0)
            .collect::<Vec<_>>();
        let mut definitions = BTreeMap::<LocalId, Vec<usize>>::new();
        for (index, &id) in ids.iter().enumerate() {
            pending.extend(uses.tree.stmt(id).children.iter().copied());
            if let Some((local, _)) = scalar_local(stmts[index]) {
                definitions.entry(local).or_default().push(index);
            }
        }
        for (index, stmts) in stmts.windows(7).enumerate() {
            let Some(candidate) = window(proto, facts, templates, &programs, stmts, &uses) else {
                continue;
            };
            let Some(Some(callee)) = functions.get(&candidate.key) else {
                continue;
            };
            let sink = index + 6;
            let closed = |local, begin, count| {
                let end = definitions
                    .get(&local)
                    .and_then(|sites| sites.get(sites.partition_point(|&site| site <= sink)))
                    .map_or(uses.count, |&end| positions[end] + 1);
                uses.reads(local, positions[begin], end) == count
            };
            // 旧 LocalId 可以先承载另一条断言；本次 COPY 的原 SSA 已另行匹配，
            // 只检查它到下一次无条件覆盖之间的读取，后缀交给同批 preview。
            if callee.creation.instr >= candidate.source.instr
                || !closed(candidate.flag.0, index, 1)
                || !closed(candidate.read.0, index + 1, 0)
                || !closed(candidate.item.0, index + 4, 2)
                || candidate.initial != candidate.local && !closed(candidate.initial, index + 5, 1)
            {
                continue;
            }
            output.push(Invocation {
                source: candidate.source,
                result: candidate.result,
                local: candidate.local,
                callee: callee.clone(),
                reader: candidate.reader,
                flag: candidate.flag,
                read: candidate.read,
                item: candidate.item,
                end: candidate.end,
                item_pc: candidate.item_pc,
                window: stmts.iter().map(|stmt| (*stmt).clone()).collect(),
            });
        }
    }
    output
}

pub(super) fn prepare(
    draft: &mut HirProto,
    original: &HirProto,
    templates: &Templates,
    invocations: &[Invocation],
) -> Option<()> {
    for invocation in invocations {
        let body = templates.bodies[invocation.callee.child.index()].as_ref()?;
        let reader_scope = original.local_debug_scopes[invocation.read.0.index()]
            .and_then(|id| original.debug_scopes.get(id))
            .and_then(Option::as_ref);
        for (role, (local, temp), name) in [
            (0, invocation.flag, body.names[0].as_ref()),
            (1, invocation.read, body.names[2].as_ref()),
            (2, invocation.item, body.item.as_ref()?.1.as_ref()),
        ] {
            if original.local_debug_hints[local.index()].is_none()
                && original.local_debug_scopes[local.index()].is_none()
            {
                continue;
            }
            let scope = original
                .debug_scopes
                .get(original.local_debug_scopes[local.index()]?)?
                .as_ref()?;
            // 候选拒绝[PolicyBoundary:DebugIdentity]：形参入口在闭包及捕获创建之后，
            // 不能借布尔合流 pc 清除独立声明。item 则从原返回预写入口开始。
            if scope.end_instr != Some(invocation.end)
                || scope.initializer_temp.or(scope.initializer_phi) != Some(temp)
                || name.is_none()
                || original.local_debug_hints[local.index()].as_ref() != name
                || role < 2 && scope.start_pc != reader_scope?.start_pc
                || role == 1 && scope.initializer_end_instr != Some(invocation.source.instr)
                || role == 2
                    && (scope.start_pc != invocation.item_pc
                        || scope.initializer_end_instr
                            != Some(InstrRef(invocation.source.instr.index() + 5)))
            {
                return None;
            }
            draft.local_debug_hints[local.index()] = None;
            draft.local_debug_scopes[local.index()] = None;
            draft.temp_debug_locals[temp.index()] = None;
            draft.temp_debug_scopes[temp.index()] = None;
        }
    }
    Some(())
}

pub(super) fn plans(
    invocations: &[Invocation],
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
) -> Vec<Plan> {
    let Some(callees) = context.expanded_callees else {
        return Vec::new();
    };
    let by_source = invocations
        .iter()
        .map(|invocation| (invocation.source, invocation))
        .collect::<BTreeMap<_, _>>();
    let mut points = Vec::new();
    prefix::coordinates::visit(&context.proto.body, &mut 0, &mut |index, kind, stmt| {
        points.push((kind == PointKind::Statement).then_some((index, stmt)))
    });
    points.windows(7).chain(points.windows(8)).filter_map(|window| {
        let stmts = window.iter().map(|point| point.map(|(_, stmt)| stmt)).collect::<Option<Vec<_>>>()?;
        let offset = stmts.len() - 7;
        let (_, HirExpr::Closure(closure)) = scalar_local(stmts[offset + 1])? else { return None; };
        let invocation = by_source.get(&closure.source_site?)?;
        if !stmts[offset..].iter().zip(&invocation.window).all(|(current, original)| *current == original) { return None; }
        let (flag, expression) = scalar_local(stmts[offset])?;
        if offset == 1 {
            if !matches!(stmts[0], HirStmt::LocalDecl(decl) if decl.bindings == [flag] && decl.values.is_empty() && decl.initializer_merge_transaction.is_none() && decl.generic_for_initializer_producer.is_none()) { return None; }
        } else if !matches!(stmts[0], HirStmt::LocalDecl(_)) { return None; }
        let callee = callees.get(&(HirLuauInliningBody::CallingSharedValue { template: invocation.callee.child.index() }, "".into()))?;
        let base = facts.trusted_temp_home_slot(invocation.result)?;
        let start = window[0]?.0;
        let sink = window.last().copied()??.0;
        if callee.local != invocation.callee.local || sink != start + stmts.len() - 1 || context.barred.contains(&base) || context.closed.contains(&base) { return None; }
        let HirExpr::LogicalAnd(final_) = scalar_local(stmts[offset + 6])?.1 else { return None; };
        let HirExpr::LogicalAnd(guard) = &final_.lhs else { return None; };
        let HirExpr::Binary(compare) = &guard.rhs else { return None; };
        let mut plan = factories::invocation(callee, invocation.source, base, invocation.local, start, sink);
        // 原标签检查与捕获更新由同一 required 调用重新执行；它们不是被退休的值版本。
        // 闭包、形参及 item 声明仍交给 preview 检查悬空读取与后继覆盖。
        plan.replayed_effects = vec![start + offset + 2, start + offset + 3];
        plan.values = vec![factories::factory_call(callee.local, Some(invocation.source), vec![expression.clone(), compare.lhs.clone(), HirExpr::Closure(invocation.reader.clone())].into())].into();
        Some(plan)
    }).collect()
}
