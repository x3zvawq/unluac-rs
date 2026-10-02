//! 连接两个有序 trace 读取与外层短路比较的完整展开窗口。
//! 纯决策程序、捕获 CONCAT 和 EdgeCopy 结果各自消费原 owner 的事实。

use super::super::value_uses::ValueUses;
use super::*;
use crate::hir::luau_inlining::{
    ObservedValueTemplate, TracedReadTemplate, selection, small_integer,
};
use crate::hir::promotion::value_programs::{Operation, Predicate, Region};
use crate::transformer::{InstrRef, Reg};

#[derive(Clone)]
pub(super) struct Body {
    pub template: ObservedValueTemplate,
    pub names: Vec<Option<String>>,
}

pub(super) fn body(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<Body> {
    let template = crate::hir::luau_inlining::observed_value_template(proto)?;
    let [HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let HirExpr::LogicalAnd(and) = &ret.values.fixed[0] else {
        return None;
    };
    let HirExpr::Binary(compare) = &and.rhs else {
        return None;
    };
    let (HirExpr::Binary(inner), _) = selection(&compare.rhs)? else {
        return None;
    };
    let (HirExpr::Call(left), _) = selection(&inner.lhs)? else {
        return None;
    };
    let (HirExpr::Call(right), _) = selection(&inner.rhs)? else {
        return None;
    };
    let first = facts.native_call_frame(left)?;
    let second = facts.native_call_frame(right)?;
    let first_compare = facts.native_binary_layout(compare)?;
    let second_compare = facts.native_binary_layout(inner)?;
    if first.home != HomeSlotKey::new(6, 0)
        || second.home != HomeSlotKey::new(7, 0)
        || !matches!(first.results, Some(ResultPack::Fixed(pack)) if pack.start.index() == 6 && pack.len == 1)
        || !matches!(second.results, Some(ResultPack::Fixed(pack)) if pack.start.index() == 7 && pack.len == 1)
        || first_compare.lhs != Some(HomeSlotKey::new(1, 0))
        || first_compare.rhs != Some(HomeSlotKey::new(4, 0))
        || second_compare.lhs != Some(HomeSlotKey::new(5, 0))
        || second_compare.rhs != Some(HomeSlotKey::new(6, 0))
        || !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(pack) if pack.start.index() == 3 && pack.len == 1)
        || facts
            .copy_value_prewrite(facts.fixed_return_input(ret, 0)?)?
            .1
            != HomeSlotKey::new(3, 0)
    {
        return None;
    }
    Some(Body {
        template,
        names: proto.param_debug_hints.clone(),
    })
}

pub(super) fn reader(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<TracedReadTemplate> {
    let template = crate::hir::luau_inlining::traced_read_template(proto)?;
    let [HirStmt::Assign(update), HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let HirExpr::Binary(concat) = &update.values.fixed[0] else {
        return None;
    };
    let buffer = facts.native_concat_buffer(concat)?;
    if buffer.start.index() != 2
        || buffer.len != 2
        || facts.operation_result_home(concat.source_site?) != Some(HomeSlotKey::new(1, 0))
        || facts.upvalue_write_value(update)?.1 != HomeSlotKey::new(1, 0)
        || !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(pack) if pack.start.index() == 1 && pack.len == 1)
    {
        return None;
    }
    Some(template)
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ReadKey {
    bindings: [LocalId; 3],
    tags: [crate::LuaString; 2],
    values: [i64; 2],
}

pub(super) struct Candidate {
    pub source: crate::hir::HirSourceSite,
    pub predicate: crate::hir::HirSourceSite,
    pub end: InstrRef,
    pub result: TempId,
    pub local: LocalId,
    pub initial: LocalId,
    pub initial_value: TempId,
    pub flag: LocalId,
    pub flag_value: TempId,
    pub flag_pc: u32,
    pub value: LocalId,
    template: ObservedValueTemplate,
    reader: ReadKey,
}

pub(super) struct Invocation {
    pub candidate: Candidate,
    pub callee: index::Function,
    pub reader: index::Function,
}

fn trace(stmt: &HirStmt) -> Option<(LocalId, &crate::hir::HirBinaryExpr, &crate::LuaString)> {
    if !matches!(stmt, HirStmt::Assign(_)) || !pairs::scalar_write(stmt) {
        return None;
    }
    let (local, HirExpr::Binary(concat)) = scalar_local(stmt)? else {
        return None;
    };
    let HirExpr::String(tag) = &concat.rhs else {
        return None;
    };
    (concat.op == HirBinaryOpKind::Concat
        && concat.lhs == HirExpr::LocalRef(local)
        && tag.as_bytes().len() <= 256)
        .then_some((local, concat, tag))
}

fn constant(value: &Literal, expected: i64) -> bool {
    match value {
        Literal::Integer(value) => *value == expected,
        Literal::Number(value) => *value == (expected as f64).to_bits(),
        _ => false,
    }
}

fn matches_first_program(
    program: &Region,
    base: usize,
    input: HomeSlotKey,
    key: i64,
    values: [i64; 2],
) -> bool {
    matches!(program.program.shape.as_slice(), [Operation::Load(Literal::Boolean(true)),
        Operation::Branch { predicate: Predicate::Eq, negated: false, operands, truthy: 3, falsy: 2 },
        Operation::Load(Literal::Boolean(false)),
        Operation::Branch { predicate: Predicate::Truthy, negated: true, operands: test, truthy: 6, falsy: 4 },
        Operation::Load(hit), Operation::Jump(7), Operation::Load(miss)]
        if matches!(operands.as_slice(), [None, Some(value)] if constant(value, key)) && test.as_slice() == [None]
            && constant(hit, values[0]) && constant(miss, values[1]))
        && program.program.registers.iter().map(Vec::as_slice).eq([
            &[Reg(base + 4)] as &[Reg],
            &[Reg(input.slot())],
            &[Reg(base + 4)],
            &[Reg(base + 4)],
            &[Reg(base + 3)],
            &[],
            &[Reg(base + 3)],
        ])
}

fn matches_second_program(
    program: &Region,
    base: usize,
    input: HomeSlotKey,
    key: i64,
    inner: [i64; 2],
    outer: [i64; 2],
) -> bool {
    matches!(program.program.shape.as_slice(), [
        Operation::Branch { predicate: Predicate::Eq, negated: false, operands, truthy: 3, falsy: 1 },
        Operation::Load(Literal::Boolean(false)), Operation::Jump(4), Operation::Load(Literal::Boolean(true)),
        Operation::Branch { predicate: Predicate::Truthy, negated: true, operands: test, truthy: 7, falsy: 5 },
        Operation::Load(hit), Operation::Jump(8), Operation::Load(miss),
        Operation::Branch { predicate: Predicate::Eq, negated: true, operands: compare, truthy: 11, falsy: 9 },
        Operation::Load(yes), Operation::Jump(12), Operation::Load(no)]
        if matches!(operands.as_slice(), [None, Some(value)] if constant(value, key)) && test.as_slice() == [None]
            && compare.as_slice() == [None, None] && constant(hit, inner[0]) && constant(miss, inner[1])
            && constant(yes, outer[0]) && constant(no, outer[1]))
        && program.program.registers.iter().map(Vec::as_slice).eq([
            &[Reg(input.slot())] as &[Reg],
            &[Reg(base + 5)],
            &[],
            &[Reg(base + 5)],
            &[Reg(base + 5)],
            &[Reg(base + 4)],
            &[],
            &[Reg(base + 4)],
            &[Reg(base + 3), Reg(base + 4)],
            &[Reg(base + 2)],
            &[],
            &[Reg(base + 2)],
        ])
}

fn candidate(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    uses: &ValueUses<'_>,
    programs: &BTreeMap<InstrRef, Option<&Region>>,
    branch: &crate::hir::HirIf,
) -> Option<Candidate> {
    let HirExpr::LocalRef(initial) = branch.cond else {
        return None;
    };
    let [
        first_update,
        prewrite,
        first_value,
        second_update,
        second_value,
        result_write,
    ] = branch.then_block.stmts.as_slice()
    else {
        return None;
    };
    let (capture, first_concat, first_tag) = trace(first_update)?;
    let (other_capture, second_concat, second_tag) = trace(second_update)?;
    let (first, first_expr) = scalar_local(first_value)?;
    let (HirExpr::Binary(left), inner) = selection(first_expr)? else {
        return None;
    };
    let (second, second_expr) = scalar_local(second_value)?;
    let (HirExpr::Binary(middle), outer) = selection(second_expr)? else {
        return None;
    };
    let (HirExpr::Binary(right), other_inner) = selection(&middle.rhs)? else {
        return None;
    };
    let (local, HirExpr::Binary(compare)) = scalar_local(result_write)? else {
        return None;
    };
    let HirExpr::LocalRef(value) = compare.lhs else {
        return None;
    };
    let (HirExpr::LocalRef(a), HirExpr::LocalRef(b)) = (&left.lhs, &right.lhs) else {
        return None;
    };
    let predicate = branch.predicate_source?;
    let frame = facts.branch_value_frame_at(predicate)?;
    let result = frame
        .edge_results(facts)
        .find(|result| facts.promoted_local_for_temp(result.value) == Some(local))?;
    let incoming = result.incoming.iter().find(|input| input.copy.is_some())?;
    let (HirBinding::Temp(flag_value), flag_home) = incoming.copy? else {
        return None;
    };
    let source = crate::hir::HirSourceSite {
        proto: proto.id,
        instr: incoming.source?,
    };
    let flag = facts.promoted_local_for_temp(flag_value)?;
    let first_source = first_concat.source_site?;
    let second_source = second_concat.source_site?;
    let first_program = (*programs.get(&InstrRef(first_source.instr.index() + 1))?)?;
    let second_program = (*programs.get(&InstrRef(second_source.instr.index() + 1))?)?;
    let state = frame
        .results
        .iter()
        .find(|result| facts.promoted_local_for_temp(result.value) == Some(capture))?;
    let base = result.home.slot();
    let keys = [small_integer(&left.rhs)?, small_integer(&right.rhs)?];
    let inner_values = [small_integer(inner[0])?, small_integer(inner[1])?];
    let outer_values = [small_integer(outer[0])?, small_integer(outer[1])?];
    let a_home = facts.trusted_local_home_slot(*a)?;
    let b_home = facts.trusted_local_home_slot(*b)?;
    let first_buffer = facts.captured_concat_buffer(first_concat, capture)?;
    let second_buffer = facts.captured_concat_buffer(second_concat, capture)?;
    let (prewrite_binding, HirExpr::Boolean(true)) = scalar_binding(prewrite)? else {
        return None;
    };
    let prewrite_value = facts.operation_result_temp(crate::hir::HirSourceSite {
        proto: proto.id,
        instr: first_program.source,
    })?;
    // 完整纯程序保留这次原预写；未读的 SSA Temp 不必先伪造成 Local 才能配对。
    let prewrite_matches = match prewrite_binding {
        HirBinding::Temp(temp) => {
            temp == prewrite_value
                && proto.temp_debug_locals[temp.index()].is_none()
                && proto.temp_debug_scopes[temp.index()].is_none()
        }
        HirBinding::Local(local) => {
            facts.promoted_local_for_temp(prewrite_value) == Some(local)
                && proto.local_debug_hints[local.index()].is_none()
                && proto.local_debug_scopes[local.index()].is_none()
        }
        _ => false,
    };
    let carries = match &branch.else_block {
        None => local == initial,
        Some(block) => {
            matches!(block.stmts.as_slice(), [HirStmt::Assign(assign)] if assign.is_phi_transfer && assign.targets == [HirLValue::Local(local)] && assign.values.fixed == [HirExpr::LocalRef(initial)] && assign.values.tail.is_none())
        }
    };
    let (yes, no) = facts.original_branch_routes(compare.source_site?)?;
    let terminal = |site, boolean| {
        result.incoming.iter().any(|input| {
            input.source == Some(site)
                && input.literal == Some(Literal::Boolean(boolean))
                && input.terminal_write
        })
    };
    // 候选拒绝[ProofIncomplete:ObservedFrame]：两次 CONCAT、纯程序和 EdgeCopy
    // 必须逐原事件连接；当前中间身份有额外读取或独立 debug 归属时不能退休。
    if !carries
        || capture != other_capture
        || first_tag == second_tag
        || inner != other_inner
        || [first_value, prewrite, second_value, result_write]
            .iter()
            .any(|stmt| !pairs::scalar_write(stmt))
        || left.op != HirBinaryOpKind::Eq
        || right.op != HirBinaryOpKind::Eq
        || middle.op != HirBinaryOpKind::Eq
        || compare.op != HirBinaryOpKind::Eq
        || middle.lhs != HirExpr::LocalRef(first)
        || compare.rhs != HirExpr::LocalRef(second)
        || ![first, second]
            .into_iter()
            .all(|local| uses.reads(local, 0, uses.count) == 1 && uses.writes(local) == 1)
        || uses.binding_reads(prewrite_binding, 0, uses.count) != 0
        || uses.binding_writes(prewrite_binding) != 1
        || [first, second, initial].iter().any(|local| {
            proto.local_debug_hints[local.index()].is_some()
                || proto.local_debug_scopes[local.index()].is_some()
        })
        || [*a, *b, value].iter().any(|local| uses.writes(*local) != 1)
        || frame.predicates != [predicate.instr]
        || frame.results.len() != 1
        || result.incoming.len() != 3
        || state.incoming.len() != 3
        || source.instr.index() + 1 != predicate.instr.index()
        || predicate.instr.index() + 3 != first_source.instr.index()
        || facts.original_branch_routes(predicate)?
            != (InstrRef(first_source.instr.index() - 2), frame.end)
        || first_program.end.index() + 2 != second_source.instr.index()
        || second_program.end != compare.source_site?.instr
        || frame.end.index() != second_program.end.index() + 4
        || !terminal(yes, true)
        || !terminal(no, false)
        || facts.promoted_local_for_temp(incoming.value) != Some(initial)
        || !prewrite_matches
        || facts.promoted_local_for_temp(first_program.result) != Some(first)
        || facts.promoted_local_for_temp(second_program.result) != Some(second)
        || flag_home != HomeSlotKey::new(base + 1, 0)
        || facts.trusted_temp_home_slot(incoming.value) != Some(result.home)
        || first_buffer.start.index() != base + 5
        || first_buffer.len != 2
        || second_buffer.start.index() != base + 6
        || second_buffer.len != 2
        || first_program.inputs.len() != 1
        || second_program.inputs.len() != 2
        || first_program
            .inputs
            .get(&Reg(a_home.slot()))
            .and_then(|value| facts.promoted_local_for_temp(*value))
            != Some(*a)
        || second_program
            .inputs
            .get(&Reg(b_home.slot()))
            .and_then(|value| facts.promoted_local_for_temp(*value))
            != Some(*b)
        || second_program.inputs.get(&Reg(base + 3)) != Some(&first_program.result)
        || facts.native_binary_layout(compare)?.lhs != facts.trusted_local_home_slot(value)
        || facts.native_binary_layout(compare)?.rhs != Some(HomeSlotKey::new(base + 2, 0))
        || [
            a_home,
            b_home,
            state.home,
            facts.trusted_local_home_slot(value)?,
        ]
        .iter()
        .any(|home| home.slot() >= base)
        || !matches_first_program(first_program, base, a_home, keys[0], inner_values)
        || !matches_second_program(
            second_program,
            base,
            b_home,
            keys[1],
            inner_values,
            outer_values,
        )
        || state
            .incoming
            .iter()
            .filter(|input| input.source == Some(second_source.instr))
            .count()
            != 2
        || state
            .incoming
            .iter()
            .filter(|input| input.source.is_some_and(|site| site < source.instr))
            .count()
            != 1
    {
        return None;
    }
    // COPY 的输入是当前 Boolean 参数，debug scope 从该 COPY 的原边界起生效。
    let flag_frame = facts.branch_value_frame(flag_value)?;
    if flag_frame.end != source.instr {
        return None;
    }
    Some(Candidate {
        source,
        predicate,
        end: frame.end,
        result: result.value,
        local,
        initial,
        initial_value: incoming.value,
        flag,
        flag_value,
        flag_pc: flag_frame.end_pc?,
        value,
        template: ObservedValueTemplate {
            tags: [first_tag.clone(), second_tag.clone()],
            inner: inner_values,
            outer: outer_values,
        },
        reader: ReadKey {
            bindings: [capture, *a, *b],
            tags: [first_tag.clone(), second_tag.clone()],
            values: keys,
        },
    })
}

pub(super) fn invocations(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    templates: &Templates,
) -> Vec<Invocation> {
    if templates.observed.iter().all(Option::is_none) {
        return Vec::new();
    }
    let uses = ValueUses::new(proto);
    let mut functions = BTreeMap::<ObservedValueTemplate, Option<index::Function>>::new();
    let mut readers = BTreeMap::<ReadKey, Option<index::Function>>::new();
    for &(_, stmt) in &uses.points {
        let Some((local, HirExpr::Closure(closure))) = scalar_local(stmt) else {
            continue;
        };
        let Some(creation) = closure.source_site else {
            continue;
        };
        if !matches!(stmt, HirStmt::LocalDecl(_))
            || uses.writes(local) != 1
            || closure.creation.is_none()
        {
            continue;
        }
        let function = index::Function {
            local,
            child: closure.proto,
            creation,
            captures: closure.captures.clone(),
        };
        if let Some(body) = &templates.observed[closure.proto.index()]
            && closure.captures.is_empty()
        {
            functions
                .entry(body.template.clone())
                .and_modify(|entry| *entry = None)
                .or_insert(Some(function));
            continue;
        }
        let Some(body) = &templates.traced[closure.proto.index()] else {
            continue;
        };
        let binding = |id: UpvalueId, mode| {
            let capture = closure.captures.get(id.index())?;
            let HirBinding::Local(local) = capture.binding else {
                return None;
            };
            (capture.mode == mode
                && (mode == HirCaptureMode::ByReference || uses.writes(local) == 1))
                .then_some(local)
        };
        if let (Some(trace), Some(a), Some(b)) = (
            binding(body.trace, HirCaptureMode::ByReference),
            binding(body.inputs[0], HirCaptureMode::ByValue),
            binding(body.inputs[1], HirCaptureMode::ByValue),
        ) {
            readers
                .entry(ReadKey {
                    bindings: [trace, a, b],
                    tags: body.tags.clone(),
                    values: body.values,
                })
                .and_modify(|entry| *entry = None)
                .or_insert(Some(function));
        }
    }
    let mut programs = BTreeMap::new();
    for region in facts
        .value_programs()
        .filter(|region| region.initial.is_none())
    {
        programs
            .entry(region.source)
            .and_modify(|entry| *entry = None)
            .or_insert(Some(region));
    }
    uses.points
        .iter()
        .filter_map(|&(_, stmt)| {
            let HirStmt::If(branch) = stmt else {
                return None;
            };
            let candidate = candidate(proto, facts, &uses, &programs, branch)?;
            let callee = functions.get(&candidate.template)?.as_ref()?;
            let reader = readers.get(&candidate.reader)?.as_ref()?;
            if [callee, reader]
                .iter()
                .any(|function| function.creation.instr >= candidate.source.instr)
            {
                return None;
            }
            Some(Invocation {
                candidate,
                callee: callee.clone(),
                reader: reader.clone(),
            })
        })
        .collect()
}

pub(super) fn prepare(
    draft: &mut HirProto,
    original: &HirProto,
    facts: &ProtoPromotionFacts,
    templates: &Templates,
    invocations: &[Invocation],
) -> Option<()> {
    let mut replacements = BTreeMap::new();
    for invocation in invocations {
        let candidate = &invocation.candidate;
        if original.local_debug_hints[candidate.flag.index()].is_some()
            || original.local_debug_scopes[candidate.flag.index()].is_some()
        {
            let scope = original
                .debug_scopes
                .get(original.local_debug_scopes[candidate.flag.index()]?)?
                .as_ref()?;
            let name = &templates.observed[invocation.callee.child.index()]
                .as_ref()?
                .names[0];
            // 候选拒绝[PolicyBoundary:DebugIdentity]：只转交这次内联的 enabled 参数副本。
            if scope.start_pc != candidate.flag_pc
                || scope.end_instr != Some(candidate.end)
                || scope.initializer_temp.or(scope.initializer_phi) != Some(candidate.flag_value)
                || name.is_none()
                || &original.local_debug_hints[candidate.flag.index()] != name
            {
                return None;
            }
            draft.local_debug_hints[candidate.flag.index()] = None;
            draft.local_debug_scopes[candidate.flag.index()] = None;
            draft.temp_debug_locals[candidate.flag_value.index()] = None;
            draft.temp_debug_scopes[candidate.flag_value.index()] = None;
        }
        replacements.insert(candidate.predicate, invocation);
    }
    let mut count = 0;
    prefix::coordinates::visit_mut(&mut draft.body, &mut 0, &mut |_, _, stmt| {
        let HirStmt::If(branch) = stmt else {
            return Some(());
        };
        let Some(invocation) = branch
            .predicate_source
            .and_then(|source| replacements.get(&source))
        else {
            return Some(());
        };
        let candidate = &invocation.candidate;
        let HirStmt::Assign(write) = branch.then_block.stmts.last()? else {
            return None;
        };
        if facts.promoted_local_for_temp(candidate.result) != Some(candidate.local) {
            return None;
        }
        let mut write = write.clone();
        write.values = vec![factories::factory_call(
            invocation.callee.local,
            Some(candidate.source),
            vec![
                HirExpr::LocalRef(candidate.flag),
                HirExpr::LocalRef(candidate.value),
                HirExpr::LocalRef(invocation.reader.local),
            ]
            .into(),
        )]
        .into();
        *stmt = HirStmt::Assign(write);
        count += 1;
        Some(())
    })?;
    (count == invocations.len()).then_some(())
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
        .map(|invocation| (invocation.candidate.source, invocation))
        .collect::<BTreeMap<_, _>>();
    let mut points = Vec::new();
    prefix::coordinates::visit(&context.proto.body, &mut 0, &mut |index, kind, stmt| {
        points.push((kind == PointKind::Statement).then_some((index, stmt)))
    });
    points
        .windows(3)
        .chain(points.windows(4))
        .filter_map(|window| {
            let stmts = window
                .iter()
                .map(|point| point.map(|(_, stmt)| stmt))
                .collect::<Option<Vec<_>>>()?;
            let (local, HirExpr::Call(call)) = scalar_local(stmts.last()?)? else {
                return None;
            };
            let source = call.required_luau_inlining?;
            let invocation = by_source.get(&source)?;
            let candidate = &invocation.candidate;
            let callee = callees.get(&(
                HirLuauInliningBody::CallingObservedValue {
                    template: invocation.callee.child.index(),
                },
                "".into(),
            ))?;
            let base = facts.trusted_temp_home_slot(candidate.result)?;
            if candidate.local != local || callee.local != invocation.callee.local {
                return None;
            }
            let before = stmts.len() - 1;
            let mut builder =
                frame_builder(context, &stmts, facts, DecompileDialect::Luau, base.slot())?;
            let call = builder.expanded_calling_value(
                call,
                before,
                base.slot(),
                Some(candidate.result),
            )?;
            if builder.first_event != Some(0) || builder.next_event != before {
                return None;
            }
            let start = window[0]?.0;
            let sink = window.last().copied()??.0;
            if sink != start + stmts.len() - 1 {
                return None;
            }
            let mut plan = factories::invocation(callee, source, base, local, start, sink);
            plan.values = vec![HirExpr::Call(Box::new(call))].into();
            Some(plan)
        })
        .collect()
}

/// 独立结果声明与外层比较共同消费同一参数帧；原 COPY/phi 身份不随嵌入位置改变。
pub(super) fn expand(
    builder: &mut FrameBuilder<'_>,
    call: &HirCallExpr,
    before: usize,
    slot: usize,
    producer: Option<TempId>,
    invocation: &Invocation,
    original_nil: &BTreeSet<LocalId>,
) -> Option<HirCallExpr> {
    let context = builder.native?;
    let candidate = &invocation.candidate;
    let base = builder.facts.trusted_temp_home_slot(candidate.result)?;
    let initial = builder.definition(candidate.initial, before)?;
    let flag = builder.definition(candidate.flag, initial)?;
    let (_, HirExpr::Binary(compare)) = scalar_local(builder.run[flag])? else {
        return None;
    };
    let HirExpr::LocalRef(input) = compare.lhs else {
        return None;
    };
    let layout = builder.facts.native_binary_layout(compare)?;
    // 候选拒绝[ProofIncomplete:ArgumentFrame]：当前参数比较、结果预写与原 SSA
    // 必须属于同一帧；LocalId 的更早使用不替代本次 COPY，也不禁止合法的后续复用。
    if producer != Some(candidate.result)
        || base != HomeSlotKey::new(slot, 0)
        || context.barred.contains(&base)
        || context.closed.contains(&base)
        || compare.op != HirBinaryOpKind::Eq
        || small_integer(&compare.rhs).is_none()
        || layout.lhs != builder.facts.trusted_local_home_slot(input)
        || layout.rhs.is_some()
        || layout.lhs.is_none_or(|home| home.slot() >= slot)
        || builder.facts.comparison_result_temp(compare) != Some(candidate.flag_value)
        || !builder.homes_match(
            candidate.flag,
            flag,
            slot + 1,
            None,
            Some(candidate.flag_value),
        )
        || !builder.homes_match(
            candidate.initial,
            initial,
            slot,
            None,
            Some(candidate.initial_value),
        )
        || scalar_local(builder.run[initial])
            != Some((candidate.initial, &HirExpr::LocalRef(candidate.flag)))
        || ![flag, initial]
            .iter()
            .all(|&index| pairs::scalar_write(builder.run[index]))
        || [candidate.flag, candidate.initial].iter().any(|local| {
            context.proto.local_debug_hints[local.index()].is_some()
                || context.proto.local_debug_scopes[local.index()].is_some()
        })
        || call.args.fixed
            != [
                HirExpr::LocalRef(candidate.flag),
                HirExpr::LocalRef(candidate.value),
                HirExpr::LocalRef(invocation.reader.local),
            ]
    {
        return None;
    }
    let empty_result = if initial + 1 == before {
        None
    } else {
        let [HirStmt::LocalDecl(decl)] = &builder.run[initial + 1..before] else {
            return None;
        };
        if decl.bindings != [candidate.local]
            || !decl.values.is_empty()
            || decl.initializer_merge_transaction.is_some()
            || decl.generic_for_initializer_producer.is_some()
            || !builder.facts.is_phi_carrier_temp(candidate.result)
            || original_nil.contains(&candidate.local)
        {
            return None;
        }
        // 独立结果计划在调用 sink 保留同一 local/debug 身份，仅转移合成空声明。
        // 嵌入比较时，外层 LocalRef builder 已先验证该结果没有独立 debug 声明。
        Some(initial + 1)
    };
    if let Some(empty) = flag.checked_sub(1)
        && matches!(builder.run[empty], HirStmt::LocalDecl(decl) if decl.bindings == [candidate.flag] && decl.values.is_empty())
    {
        let HirStmt::LocalDecl(decl) = builder.run[empty] else {
            return None;
        };
        if !builder.facts.is_phi_carrier_temp(candidate.flag_value)
            || original_nil.contains(&candidate.flag)
            || decl.initializer_merge_transaction.is_some()
            || decl.generic_for_initializer_producer.is_some()
        {
            return None;
        }
        builder.finish_event(empty)?;
    }
    let argument = builder.expr(
        &HirExpr::LocalRef(candidate.flag),
        initial,
        slot + 1,
        None,
        false,
        true,
        Some(candidate.flag_value),
    )?;
    builder.finish_event(initial)?;
    if let Some(empty) = empty_result {
        builder.finish_event(empty)?;
    }
    let mut rebuilt = call.clone();
    rebuilt.args.fixed[0] = argument;
    Some(rebuilt)
}
