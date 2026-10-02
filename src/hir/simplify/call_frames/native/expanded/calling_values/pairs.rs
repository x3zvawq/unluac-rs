//! 配对先读取捕获状态、再返回比较结果和同一读取值的连续展开窗口。
//! 输入准备、读取决策、纯返回程序和第二返回 COPY 均沿原 SSA 与指令身份连接。

use super::*;
use crate::hir::promotion::value_programs::{Operation, Predicate, Region};
use crate::transformer::{InstrRef, Reg};

pub(super) fn body(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<Body> {
    let (item, fallback) = crate::hir::luau_inlining::calling_read_pair(proto)?;
    let [HirStmt::LocalDecl(decl), HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let HirExpr::Call(call) = &decl.values.fixed[0] else {
        return None;
    };
    let HirExpr::LogicalAnd(and) = &ret.values.fixed[0] else {
        return None;
    };
    let HirExpr::Binary(compare) = &and.rhs else {
        return None;
    };
    let frame = facts.native_call_frame(call)?;
    let layout = facts.native_binary_layout(compare)?;
    let first = facts.fixed_return_input(ret, 0)?;
    let second = facts.fixed_return_input(ret, 1)?;
    let source = ret.frame_source?;
    let copy = facts.value_result_copy_at(crate::hir::HirSourceSite {
        proto: proto.id,
        instr: InstrRef(source.instr.index().checked_sub(1)?),
    })?;
    if frame.home != HomeSlotKey::new(4, 0)
        || !matches!(frame.results, Some(ResultPack::Fixed(pack)) if pack.start.index() == 4 && pack.len == 1)
        || facts.trusted_local_home_slot(item) != Some(HomeSlotKey::new(4, 0))
        || !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(pack) if pack.start.index() == 5 && pack.len == 2)
        || facts.copy_value_prewrite(first)?.1 != HomeSlotKey::new(5, 0)
        || copy.target != second
        || copy.source != facts.operation_result_temp(call.source_site?)
        || copy.source_home != HomeSlotKey::new(4, 0)
        || copy.target_home != HomeSlotKey::new(6, 0)
        || layout.lhs != Some(HomeSlotKey::new(1, 0))
        || layout.rhs != Some(HomeSlotKey::new(6, 0))
    {
        return None;
    }
    Some(Body {
        kind: Kind::Pair,
        fallback: fallback.clone(),
        selection_hit: None,
        read_tag: None,
        names: proto.param_debug_hints.clone(),
        item: Some((item, proto.local_debug_hints[item.index()].clone())),
    })
}

#[derive(Debug)]
pub(super) struct Candidate {
    pub start: usize,
    pub sink: usize,
    pub source: crate::hir::HirSourceSite,
    pub end: InstrRef,
    pub item_pc: u32,
    pub base: HomeSlotKey,
    pub results: [LocalId; 2],
    pub result_values: [TempId; 2],
    pub argument: Option<ArgumentCopy>,
    pub flag: LocalId,
    pub item: LocalId,
    pub item_value: TempId,
    pub counter: LocalId,
    pub index: LocalId,
    pub table: LocalId,
    pub increment: i64,
    pub key: i64,
    pub hit: Literal,
    pub fallback: Option<Literal>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ArgumentCopy {
    pub body_pc: u32,
    pub local: LocalId,
    pub input: TempId,
    pub source: TempId,
}

pub(in crate::hir::simplify::call_frames::native::expanded) fn scalar_write(
    stmt: &HirStmt,
) -> bool {
    match stmt {
        HirStmt::LocalDecl(decl) => {
            decl.initializer_merge_transaction.is_none()
                && decl.generic_for_initializer_producer.is_none()
        }
        HirStmt::Assign(assign) => {
            !assign.is_phi_transfer
                && !assign.luau_function_declaration
                && !assign.luau_compound_global
                && assign.upvalue_write_source.is_none()
                && assign.parallel_nil_frame.is_none()
                && assign.initializer_merge_transaction.is_none()
                && assign.generic_for_initializer_producer.is_none()
                && assign.root_release.is_none()
                && assign.method_rewrite_transaction.is_none()
        }
        _ => false,
    }
}

fn snapshot(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    programs: &BTreeMap<InstrRef, Option<&Region>>,
    window: [&HirStmt; 6],
    start: usize,
    sink: usize,
) -> Option<Candidate> {
    let (value, HirExpr::LocalRef(value_source)) = scalar_local(window[0])? else {
        return None;
    };
    let read = reading::match_read(facts, window[1], window[2])?;
    let reading::Value::Used {
        local: read_item,
        temp: read_value,
    } = read.value
    else {
        return None;
    };
    let (initial, HirExpr::LocalRef(flag)) = scalar_local(window[3])? else {
        return None;
    };
    let (first, HirExpr::LogicalAnd(result)) = scalar_local(window[4])? else {
        return None;
    };
    let (second, HirExpr::LocalRef(item_source)) = scalar_local(window[5])? else {
        return None;
    };
    let HirExpr::Binary(compare) = &result.rhs else {
        return None;
    };
    let HirExpr::LogicalOr(or) = &compare.rhs else {
        return None;
    };
    let program = (*programs.get(&read.end)?)?;
    let original = |instr| crate::hir::HirSourceSite {
        proto: proto.id,
        instr,
    };
    let input_copy = facts.binary_operand_copy(compare, 0)?;
    let source = facts.binary_operand_copy_instruction(compare, 0)?;
    let tail_copy = facts.value_result_copy_at(original(program.end))?;
    let base = facts.trusted_temp_home_slot(program.result)?;
    let flag_home = facts.trusted_local_home_slot(*flag)?;
    let value_home = input_copy.target_home;
    let read_home = read.home;
    let fallback = Literal::from_expr(&or.rhs)?;
    let compare_site = compare.source_site?;
    let compare_layout = facts.native_binary_layout(compare)?;
    if window.iter().any(|stmt| !scalar_write(stmt))
        || result.lhs != HirExpr::LocalRef(initial)
        || compare.op != HirBinaryOpKind::Eq
        || compare.lhs != HirExpr::LocalRef(value)
        || or.lhs != HirExpr::LocalRef(read_item)
        || *item_source != read_item
        || read.source.instr.index() != source.index() + 1
        || read.begin > source
        || compare_site.instr.index() != program.source.index() + 5
        || facts.promoted_local_for_temp(program.initial?) != Some(initial)
        || facts.promoted_local_for_temp(program.result) != Some(first)
        || facts.promoted_local_for_temp(input_copy.target) != Some(value)
        || facts.promoted_local_for_temp(input_copy.source?) != Some(*value_source)
        || facts.promoted_local_for_temp(tail_copy.target) != Some(second)
        || tail_copy.source != Some(read_value)
        || tail_copy.source_home != read_home
        || tail_copy.target_home.slot() != base.slot() + 1
        || value_home.slot() != base.slot() + 2
        || read_home.slot() != base.slot() + 3
        || input_copy.source_home.slot() >= base.slot()
        || flag_home.slot() >= base.slot()
        || read.inputs.iter().any(|home| home.slot() >= base.slot())
        || compare_layout.lhs != Some(value_home)
        || compare_layout
            .rhs
            .is_none_or(|home| home.slot() != base.slot() + 4)
    {
        return None;
    }
    let shape = &program.program.shape;
    if !matches!(shape.as_slice(), [Operation::Copy,
        Operation::Branch { predicate: Predicate::Truthy, negated: true, operands: a, truthy: 9, falsy: 2 },
        Operation::Copy,
        Operation::Branch { predicate: Predicate::Truthy, negated: false, operands: b, truthy: 5, falsy: 4 },
        Operation::Load(value),
        Operation::Branch { predicate: Predicate::Eq, negated: false, operands: c, truthy: 8, falsy: 6 },
        Operation::Load(Literal::Boolean(false)), Operation::Jump(9), Operation::Load(Literal::Boolean(true))]
        if a.as_slice() == [None] && b.as_slice() == [None] && c.as_slice() == [None, None] && value == &fallback)
        || program.end.index() != program.source.index() + 9
        || !program.program.registers.iter().map(Vec::as_slice).eq([
            &[Reg(base.slot()), Reg(flag_home.slot())] as &[Reg],
            &[Reg(base.slot())],
            &[Reg(base.slot() + 4), Reg(read_home.slot())],
            &[Reg(base.slot() + 4)],
            &[Reg(base.slot() + 4)],
            &[Reg(value_home.slot()), Reg(base.slot() + 4)],
            &[Reg(base.slot())],
            &[],
            &[Reg(base.slot())],
        ])
        || program.inputs.len() != 3
        || program.inputs.get(&Reg(read_home.slot())) != Some(&read_value)
        || program.inputs.get(&Reg(value_home.slot())) != Some(&input_copy.target)
        || facts.promoted_local_for_temp(*program.inputs.get(&Reg(flag_home.slot()))?)
            != Some(*flag)
    {
        return None;
    }
    Some(Candidate {
        start,
        sink,
        source: original(source),
        end: InstrRef(program.end.index() + 1),
        item_pc: read.end_pc,
        base,
        results: [first, second],
        result_values: [program.result, tail_copy.target],
        argument: Some(ArgumentCopy {
            body_pc: facts.binary_operand_copy_after_pc(compare, 0)?,
            local: value,
            input: input_copy.target,
            source: input_copy.source?,
        }),
        flag: *flag,
        item: read_item,
        item_value: read_value,
        counter: read.counter,
        index: read.index,
        table: read.table,
        increment: read.increment,
        key: read.key,
        hit: read.hit,
        fallback: Some(fallback),
    })
}

pub(super) fn candidates(proto: &HirProto, facts: &ProtoPromotionFacts) -> Vec<Candidate> {
    let mut programs = BTreeMap::new();
    for region in facts
        .value_programs()
        .filter(|region| region.initial.is_some())
    {
        programs
            .entry(region.source)
            .and_modify(|entry| *entry = None)
            .or_insert(Some(region));
    }
    let mut points = Vec::new();
    prefix::coordinates::visit(&proto.body, &mut 0, &mut |index, kind, stmt| {
        points.push((kind == PointKind::Statement).then_some((index, stmt)));
    });
    let mut candidates = points
        .windows(6)
        .filter_map(|window| {
            let [Some(a), Some(b), Some(c), Some(d), Some(e), Some(f)] = window else {
                return None;
            };
            snapshot(
                proto,
                facts,
                &programs,
                [a.1, b.1, c.1, d.1, e.1, f.1],
                a.0,
                f.0,
            )
        })
        .collect::<Vec<_>>();
    let original_nil = facts
        .nil_write_groups()
        .flat_map(|group| {
            group
                .iter()
                .filter_map(|temp| facts.promoted_local_for_temp(*temp))
        })
        .collect();
    for width in [4, 5] {
        candidates.extend(points.windows(width).filter_map(|window| {
            let stmts = window
                .iter()
                .map(|point| point.map(|(_, stmt)| stmt))
                .collect::<Option<Vec<_>>>()?;
            folded_pairs::candidate(
                proto,
                facts,
                &stmts,
                window[0]?.0,
                window[width - 1]?.0,
                &original_nil,
            )
        }));
    }
    candidates
}

pub(super) fn plans(
    invocations: &[index::PairInvocation],
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
) -> Vec<Plan> {
    let Some(callees) = context.expanded_callees else {
        return Vec::new();
    };
    let mut points = Vec::new();
    prefix::coordinates::visit(&context.proto.body, &mut 0, &mut |index, kind, stmt| {
        points.push((kind == PointKind::Statement).then_some((index, stmt)));
    });
    let writebacks = points
        .windows(2)
        .filter_map(|window| {
            let [Some((a, left)), Some((b, right))] = window else {
                return None;
            };
            (*b == a + 1).then_some((*a, [*left, *right]))
        })
        .collect::<BTreeMap<_, _>>();
    let by_source = invocations
        .iter()
        .map(|invocation| (invocation.candidate.source, invocation))
        .collect::<BTreeMap<_, _>>();
    // 前缀投影会改变 DFS 坐标，必须在最终草稿上重新取得当前窗口。
    candidates(context.proto, facts)
        .into_iter()
        .filter_map(|candidate| {
            let invocation = by_source.get(&candidate.source)?;
            let callee = callees.get(&(
                HirLuauInliningBody::CallingReadPair {
                    template: invocation.callee.child.index(),
                },
                "".into(),
            ))?;
            let value = invocation.value.clone();
            if callee.local != invocation.callee.local
                || candidate.result_values != invocation.candidate.result_values
                || candidate.argument != invocation.candidate.argument
                || candidate
                    .argument
                    .iter()
                    .map(|arg| arg.local)
                    .chain([candidate.item])
                    .any(|local| {
                        context.proto.local_debug_hints[local.index()].is_some()
                            || context.proto.local_debug_scopes[local.index()].is_some()
                    })
                || context.barred.contains(&candidate.base)
                || context.closed.contains(&candidate.base)
            {
                return None;
            }
            let call = factories::factory_call(
                callee.local,
                Some(candidate.source),
                vec![
                    HirExpr::LocalRef(candidate.flag),
                    value,
                    HirExpr::LocalRef(invocation.reader.local),
                    HirExpr::Boolean(candidate.argument.is_some()),
                ]
                .into(),
            );
            let mut plan = factories::invocation(
                callee,
                candidate.source,
                candidate.base,
                candidate.results[0],
                candidate.start,
                candidate.sink,
            );
            plan.values = HirValuePack {
                fixed: Vec::new(),
                tail: Some(HirPackTail::exact(call, 2)),
            };
            plan.result_locals = candidate.results.to_vec();
            if let Some(tail) = writebacks.get(&(candidate.sink + 1)) {
                factories::pair_writeback(&mut plan, *tail, facts);
            }
            // 原 counter 写与索引读取已经与实际 reader 完整配对；不能把它们当作可丢弃的中转。
            plan.replayed_effects = plan.removed.clone();
            Some(plan)
        })
        .collect()
}
