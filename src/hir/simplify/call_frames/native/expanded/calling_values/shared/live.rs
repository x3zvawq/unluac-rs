//! 连接急切读取与动态 guard 的原封闭返回程序。
//! 参数 COPY、共享 item 和结果预写均使用冻结 SSA 身份，当前树仍须完整匹配。

use super::super::super::value_uses::ValueUses;
use super::*;
use crate::hir::promotion::value_programs::Region;
use crate::transformer::Reg;

pub(in crate::hir::simplify::call_frames::native::expanded::calling_values) struct Return {
    pub initial: LocalId,
    pub flag: LocalId,
    pub flag_value: TempId,
    pub release: Option<LocalId>,
    pub consumer_declaration: Option<LocalId>,
    pub expression: HirExpr,
    pub hit: Literal,
    pub fallback: Literal,
}

fn comparison(stmt: &HirStmt) -> Option<&crate::hir::HirBinaryExpr> {
    let value = match stmt {
        HirStmt::If(branch) => &branch.cond,
        _ => scalar_local(stmt)?.1,
    };
    match value {
        HirExpr::Binary(binary) => Some(binary),
        _ => None,
    }
}

/// 只借用紧邻消费语句的原比较输入；身份来自 use 对应的 SSA Phi，而非表达式外形。
fn result_expression<'a>(
    stmt: &'a HirStmt,
    facts: &ProtoPromotionFacts,
    result: TempId,
) -> Option<(ResultTarget, &'a HirExpr)> {
    if let Some((local, expression @ HirExpr::LogicalAnd(_))) = scalar_local(stmt) {
        return (pairs::scalar_write(stmt) && facts.promoted_local_for_temp(result) == Some(local))
            .then_some((ResultTarget::Local(local), expression));
    }
    let binary = comparison(stmt)?;
    let operand =
        (0..2).find(|&operand| facts.binary_phi_operand(binary, operand) == Some(result))?;
    Some((
        ResultTarget::ComparisonOperand(binary.source_site?, operand),
        [&binary.lhs, &binary.rhs][operand],
    ))
}

pub(super) fn replace_comparison(
    stmt: &mut HirStmt,
    source: crate::hir::HirSourceSite,
    operand: usize,
    expected: &HirExpr,
    value: HirExpr,
) -> Option<()> {
    let expression = match stmt {
        HirStmt::If(branch) => &mut branch.cond,
        HirStmt::LocalDecl(decl) if decl.bindings.len() == 1 && decl.values.tail.is_none() => {
            let [value] = decl.values.fixed.as_mut_slice() else {
                return None;
            };
            value
        }
        HirStmt::Assign(assign) if assign.targets.len() == 1 && assign.values.tail.is_none() => {
            let [value] = assign.values.fixed.as_mut_slice() else {
                return None;
            };
            value
        }
        _ => return None,
    };
    let HirExpr::Binary(binary) = expression else {
        return None;
    };
    if binary.source_site != Some(source) {
        return None;
    }
    let input = [&mut binary.lhs, &mut binary.rhs]
        .into_iter()
        .nth(operand)?;
    if input != expected {
        return None;
    }
    *input = value;
    Some(())
}

fn candidate(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    programs: &BTreeMap<InstrRef, Option<&Region>>,
    original_nil: &BTreeSet<LocalId>,
    window: &[&HirStmt],
) -> Option<Candidate> {
    let (value, HirExpr::LocalRef(value_source)) = scalar_local(window.first()?)? else {
        return None;
    };
    let read = reading::match_read(facts, window.get(1)?, window.get(2)?)?;
    let reading::Value::Used {
        local: item,
        temp: item_value,
    } = read.value
    else {
        return None;
    };
    let (release, initial_index) = match window.get(3)? {
        HirStmt::LocalRootRelease(local) => (Some(*local), 4),
        _ => (None, 3),
    };
    let (initial, HirExpr::LocalRef(flag)) = scalar_local(window.get(initial_index)?)? else {
        return None;
    };
    let program = (*programs.get(&read.end)?)?;
    // 外层布尔结果的空声明没有原 VM 写入；保留给分支参数 owner，不将其误认作共享返回值。
    let consumer_declaration = match window.get(initial_index + 1)? {
        HirStmt::LocalDecl(decl)
            if decl.bindings.len() == 1
                && decl.generic_for_initializer_producer.is_none()
                && removable_empty_declaration(proto, original_nil, decl) =>
        {
            Some(decl.bindings[0])
        }
        _ => None,
    };
    let result_index = initial_index + 1 + usize::from(consumer_declaration.is_some());
    let (target, expression) = result_expression(window.get(result_index)?, facts, program.result)?;
    if consumer_declaration.is_some() && !matches!(target, ResultTarget::ComparisonOperand(..)) {
        return None;
    }
    let HirExpr::LogicalAnd(final_) = expression else {
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
    let HirExpr::LogicalOr(or) = &compare.rhs else {
        return None;
    };
    let HirExpr::LogicalAnd(pick) = &or.lhs else {
        return None;
    };
    let input_copy = facts.binary_operand_copy(compare, 0)?;
    let source = facts.binary_operand_copy_instruction(compare, 0)?;
    let base = facts.trusted_temp_home_slot(program.result)?;
    let flag_home = facts.trusted_local_home_slot(*flag)?;
    let value_home = input_copy.target_home;
    let hit = Literal::from_expr(&pick.rhs)?;
    let fallback = Literal::from_expr(&or.rhs)?;
    let first_layout = facts.native_binary_layout(compare)?;
    let second_layout = facts.native_binary_layout(check)?;
    // 候选拒绝[ProofIncomplete:SharedFrame]：当前叶与原比较、预写和读取的身份必须一致。
    // 独立的 item/参数读取不能随展开体退休；按当前 proto 一次索引引用数。
    if [0, 1, 2, initial_index]
        .iter()
        .any(|&i| !pairs::scalar_write(window[i]))
        || guard.lhs != HirExpr::LocalRef(initial)
        || compare.op != HirBinaryOpKind::Eq
        || compare.lhs != HirExpr::LocalRef(value)
        || pick.lhs != HirExpr::LocalRef(item)
        || check.op != HirBinaryOpKind::Eq
        || check.lhs != HirExpr::LocalRef(item)
        || check.rhs != HirExpr::LocalRef(value)
        || proto.local_debug_hints[initial.index()].is_some()
        || proto.local_debug_scopes[initial.index()].is_some()
        || read.source.instr.index() != source.index() + 1
        || read.begin > source
        || compare.source_site?.instr.index() != program.source.index() + 7
        || check.source_site?.instr.index() != program.source.index() + 8
        || facts.promoted_local_for_temp(program.initial?) != Some(initial)
        || facts.promoted_local_for_temp(input_copy.target) != Some(value)
        || facts.promoted_local_for_temp(input_copy.source?) != Some(*value_source)
        || value_home.slot() != base.slot() + 1
        || read.home.slot() != base.slot() + 2
        || input_copy.source_home.slot() >= base.slot()
        || flag_home.slot() >= base.slot()
        || read.inputs.iter().any(|home| home.slot() >= base.slot())
        || first_layout.lhs != Some(value_home)
        || first_layout.rhs != Some(HomeSlotKey::new(base.slot() + 3, 0))
        || second_layout.lhs != Some(read.home)
        || second_layout.rhs != Some(value_home)
    {
        return None;
    }
    if !matches_return(
        program,
        ReturnSlots {
            base,
            flag: flag_home,
            value: value_home,
            item: read.home,
            selection: HomeSlotKey::new(base.slot() + 3, 0),
        },
        &hit,
        &fallback,
    ) || program.inputs.get(&Reg(read.home.slot())) != Some(&item_value)
        || program.inputs.get(&Reg(value_home.slot())) != Some(&input_copy.target)
    {
        return None;
    }
    let flag_value = *program.inputs.get(&Reg(flag_home.slot()))?;
    if facts.promoted_local_for_temp(flag_value) != Some(*flag) {
        return None;
    }
    Some(Candidate {
        source: crate::hir::HirSourceSite {
            proto: proto.id,
            instr: source,
        },
        argument: pairs::ArgumentCopy {
            body_pc: facts.binary_operand_copy_after_pc(compare, 0)?,
            local: value,
            input: input_copy.target,
            source: input_copy.source?,
        },
        read,
        result: program.result,
        target,
        end: program.end,
        live: Some(Return {
            initial,
            flag: *flag,
            flag_value,
            release,
            consumer_declaration,
            expression: expression.clone(),
            hit,
            fallback,
        }),
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
    let uses = ValueUses::new(proto);
    let original_nil = facts
        .nil_write_groups()
        .flat_map(|group| {
            group
                .iter()
                .filter_map(|temp| facts.promoted_local_for_temp(*temp))
        })
        .collect::<BTreeSet<_>>();
    let mut output = Vec::new();
    let mut pending = vec![uses.tree.root_block()];
    while let Some(block) = pending.pop() {
        let ids = uses.tree.block(block);
        let statements = ids
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
            if let Some((local, _)) = scalar_local(statements[index]) {
                definitions.entry(local).or_default().push(index);
            }
        }
        for index in 0..statements.len().saturating_sub(4) {
            let Some(candidate) =
                candidate(proto, facts, &programs, &original_nil, &statements[index..])
            else {
                continue;
            };
            let live = candidate.live.as_ref().unwrap();
            let reading::Value::Used { local: item, .. } = candidate.read.value else {
                unreachable!()
            };
            let sink = index
                + 4
                + usize::from(live.release.is_some())
                + usize::from(live.consumer_declaration.is_some());
            let closed = |local, begin, expected| {
                let end = definitions
                    .get(&local)
                    .and_then(|sites| sites.get(sites.partition_point(|&site| site <= sink)))
                    // 后继覆盖的 RHS 仍属于旧值版本；跨子块的写不能作为无条件覆盖。
                    .map_or(uses.count, |&end| positions[end] + 1);
                uses.reads(local, positions[begin], end) == expected
            };
            if !closed(candidate.argument.local, index, 2)
                || !closed(item, index + 2, 2)
                || candidate.target.local() != Some(live.initial)
                    && !closed(
                        live.initial,
                        index + 3 + usize::from(live.release.is_some()),
                        1,
                    )
            {
                continue;
            }
            output.push(candidate);
        }
    }
    output
}

pub(super) fn prepare(
    draft: &mut HirProto,
    original: &HirProto,
    templates: &Templates,
    invocation: &index::SharedInvocation,
) -> Option<()> {
    let candidate = &invocation.candidate;
    let reading::Value::Used { local, temp } = candidate.read.value else {
        return None;
    };
    if original.local_debug_hints[local.index()].is_none()
        && original.local_debug_scopes[local.index()].is_none()
    {
        return Some(());
    }
    let scope = original
        .debug_scopes
        .get(original.local_debug_scopes[local.index()]?)?
        .as_ref()?;
    let name = &templates.bodies[invocation.callee.child.index()]
        .as_ref()?
        .item
        .as_ref()?
        .1;
    // 候选拒绝[PolicyBoundary:DebugIdentity]：只吸收原共享读取在该次展开中的 item 身份。
    if scope.start_pc != candidate.read.end_pc
        || scope.end_instr != Some(candidate.end)
        || scope.initializer_temp.or(scope.initializer_phi) != Some(temp)
        || name.is_none()
        || &original.local_debug_hints[local.index()] != name
    {
        return None;
    }
    draft.local_debug_hints[local.index()] = None;
    draft.local_debug_scopes[local.index()] = None;
    draft.temp_debug_locals[temp.index()] = None;
    draft.temp_debug_scopes[temp.index()] = None;
    Some(())
}
