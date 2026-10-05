//! 恢复二维数值查找展开体及其外层观察帧。
//! 当前 HIR 证明完整状态更新顺序，原读操作和返回 COPY 证明物理帧；最终源码仍须强制内联。

use super::super::assignments::plain_copy;
use super::*;
use crate::hir::common::{
    HirBinaryExpr, HirBinaryOpKind, HirOperationSources, HirSourceSite, HirTableAccess,
};
use crate::hir::luau_inlining::{NestedSearchTemplate, nested_search_count, small_integer};

pub(super) struct Recovered {
    pub draft: Option<HirProto>,
    pub obligations: Vec<(HirSourceSite, LocalId)>,
    pub plans: Vec<Plan>,
    pub result_slots: BTreeMap<HirSourceSite, usize>,
}

fn update(stmt: &HirStmt, state: LocalId) -> Option<(LocalId, &HirBinaryExpr, i64)> {
    let (target, condition, value) = if let HirStmt::If(branch) = stmt {
        let [assignment] = branch.then_block.stmts.as_slice() else {
            return None;
        };
        let (target, value) = scalar_local(assignment)?;
        if target != state
            || !plain_copy(assignment)
            || branch
                .else_block
                .as_ref()
                .is_some_and(|other| !other.stmts.is_empty())
        {
            return None;
        }
        (target, &branch.cond, value)
    } else {
        let (target, HirExpr::LogicalOr(other)) = scalar_local(stmt)? else {
            return None;
        };
        let HirExpr::LogicalAnd(selected) = &other.lhs else {
            return None;
        };
        if other.rhs != HirExpr::LocalRef(state) || !plain_copy(stmt) {
            return None;
        }
        (target, &selected.lhs, &selected.rhs)
    };
    let HirExpr::Binary(binary) = condition else {
        return None;
    };
    (binary.op == HirBinaryOpKind::Eq).then_some((target, binary, small_integer(value)?))
}

struct Cell<'a> {
    next: usize,
    row: Option<LocalId>,
    access: &'a HirTableAccess,
    column: &'a HirTableAccess,
    compare: &'a HirBinaryExpr,
    target: LocalId,
    value: i64,
}

fn cell(stmts: &[HirStmt], position: usize, state: LocalId) -> Option<Cell<'_>> {
    let (row, prepared, next) =
        if let Some((row, HirExpr::TableAccess(access))) = scalar_local(stmts.get(position)?) {
            if !plain_copy(&stmts[position]) {
                return None;
            }
            (Some(row), Some(access.as_ref()), position + 1)
        } else {
            (None, None, position)
        };
    let (target, compare, value) = update(stmts.get(next)?, state)?;
    let HirExpr::TableAccess(column) = &compare.lhs else {
        return None;
    };
    let access = match (&column.base, row, prepared) {
        (HirExpr::TableAccess(access), None, None) => access.as_ref(),
        (HirExpr::LocalRef(local), Some(row), Some(access)) if *local == row => access,
        _ => return None,
    };
    Some(Cell {
        next: next + 1,
        row,
        access,
        column,
        compare,
        target,
        value,
    })
}

pub(super) fn plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    templates: &[Option<NestedSearchTemplate>],
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
        .flat_map(|known| known.values())
    {
        if let HirLuauInliningBody::NestedSearch { template } = callee.body
            && let Some(body) = &templates[template]
        {
            callees
                .entry(body.clone())
                .and_modify(|known| *known = None)
                .or_insert(Some(callee));
        }
    }
    if callees.is_empty() {
        return result;
    }
    let uses = value_uses::ValueUses::new(context.proto);
    let ids = uses.tree.block(uses.tree.root_block());
    let stmts = &context.proto.body.stmts;
    let coordinate = |index: usize| uses.points[ids[index].index()].0;
    let mut start = 0;
    while start + 5 < stmts.len() {
        let candidate = (|| {
            let (state, initial) = scalar_local(&stmts[start])?;
            let first = cell(stmts, start + 1, state)?;
            let HirExpr::LocalRef(input) = first.access.base else {
                return None;
            };
            let HirExpr::String(needle) = &first.compare.rhs else {
                return None;
            };
            let first_value = first.value;
            let template = NestedSearchTemplate {
                initial: small_integer(initial)?,
                scale: first_value.checked_sub(1)?,
                needle: needle.clone(),
            };
            let callee = *callees.get(&template)?.as_ref()?;
            let state_home = facts.trusted_local_home_slot(state)?;
            let base = state_home.slot().checked_sub(3)?;
            let home = |offset| HomeSlotKey::new(base + offset, 0);
            // 原循环按值捕获的旧 binding 可已离开作用域；按各次原 Def 核对引用别名，
            // 不把整函数的历史捕获槽集合当作这次写入仍有活动 cell 的证明。
            if !plain_copy(&stmts[start])
                || callee.declaration >= start
                || facts.trusted_local_home_slot(input)?.slot() >= base
                || !facts.local_definitions_reference_unaliased(input)
                || uses.writes(input) != 1
                || uses.writes(callee.local) != 1
                || (base..=base + 5).any(|slot| context.closed.contains(&HomeSlotKey::new(slot, 0)))
            {
                return None;
            }
            // 候选拒绝[ProofIncomplete]：完整索引序列、状态和返回 COPY 必须共同匹配。
            let mut cells = Vec::new();
            let mut rows = BTreeSet::new();
            let mut position = start + 1;
            let mut final_state = state;
            let mut previous = callee.creation.instr;
            // pinned 编译器每层最多展开 25 次；限制候选工作量，不随源码长度重复回扫。
            while position + 1 < stmts.len() && cells.len() < 25 * 25 {
                let Some(current) = cell(stmts, position, state) else {
                    break;
                };
                let Cell {
                    next,
                    row,
                    access,
                    column,
                    compare,
                    target,
                    value,
                } = current;
                if let Some(row) = row {
                    if facts.trusted_local_home_slot(row) != Some(home(5)) {
                        return None;
                    }
                    rows.insert(row);
                }
                let (
                    HirOperationSources::Single(row_site),
                    HirOperationSources::Single(column_site),
                ) = (&access.sources, &column.sources)
                else {
                    return None;
                };
                let row_layout = facts.native_table_read_layout(access)?;
                let column_layout = facts.native_table_read_layout(column)?;
                let compare_site = compare.source_site?;
                let i = small_integer(&access.key)?;
                let j = small_integer(&column.key)?;
                if access.base != HirExpr::LocalRef(input)
                    || compare.rhs != HirExpr::String(template.needle.clone())
                    || template.value(i, j) != Some(value)
                    || row_layout.base != facts.trusted_local_home_slot(input)?
                    || row_layout.key.is_some()
                    || !facts.operation_result_reference_unaliased(*row_site)
                    || !facts.operation_result_reference_unaliased(*column_site)
                    || facts.table_read_result_home(access) != Some(home(5))
                    || column_layout.base != home(5)
                    || column_layout.key.is_some()
                    || facts.table_read_base_value(column) != facts.operation_result_temp(*row_site)
                    || facts.table_read_result_home(column) != Some(home(4))
                    || facts.binary_value_operand(compare, 0)
                        != facts.operation_result_temp(*column_site)
                    || facts.native_binary_layout(compare)?.lhs != Some(home(4))
                    || facts.native_binary_layout(compare)?.rhs.is_some()
                    || previous >= row_site.instr
                    || row_site.instr >= column_site.instr
                    || column_site.instr >= compare_site.instr
                {
                    return None;
                }
                cells.push((i, j));
                previous = compare_site.instr;
                final_state = target;
                position = next;
                if target != state {
                    break;
                }
            }
            let &(limit, last_column) = cells.last()?;
            let count = nested_search_count(limit)?;
            if limit != last_column
                || cells.len() != count * count
                || cells.iter().enumerate().any(|(index, &(i, j))| {
                    i != (index / count + 1) as i64 || j != (index % count + 1) as i64
                })
            {
                return None;
            }
            let (boolean, HirExpr::Binary(compare)) = scalar_local(stmts.get(position)?)? else {
                return None;
            };
            let (callable, global) = scalar_local(stmts.get(position + 1)?)?;
            let HirStmt::CallStmt(observe) = stmts.get(position + 2)? else {
                return None;
            };
            let copy = facts.binary_operand_copy(compare, 0)?;
            let source = HirSourceSite {
                proto: context.proto.id,
                instr: facts.binary_operand_copy_instruction(compare, 0)?,
            };
            let assertion = counter_while::assertion_frame(
                &observe.call,
                &stmts[position + 1],
                &stmts[position],
                facts,
            )?;
            if compare.lhs != HirExpr::LocalRef(final_state)
                || copy.source_home != home(3)
                || copy.target_home != home(2)
                || facts.trusted_local_home_slot(final_state)
                    != Some(if final_state == state {
                        home(3)
                    } else {
                        home(2)
                    })
                || previous >= source.instr
                || source.instr >= compare.source_site?.instr
                || facts.trusted_local_home_slot(boolean) != Some(home(1))
                || facts.trusted_local_home_slot(callable) != Some(home(0))
                || !matches!(global, HirExpr::GlobalRef(value) if value.key.as_utf8() == Some("assert") && facts.global_read_frame(value, DecompileDialect::Luau) == Some(home(0)))
                || assertion.base != home(0)
                || !facts.temp_definition_reference_unaliased(copy.target)
                || !facts.temp_definition_reference_unaliased(
                    facts.native_fastcall_frame(&observe.call)?.callee,
                )
                || !plain_copy(&stmts[position])
                || !plain_copy(&stmts[position + 1])
            {
                return None;
            }
            let begin = coordinate(start);
            let end = coordinate(position + 2);
            for local in rows.iter().copied().chain([state, final_state, boolean]) {
                if uses.reads(local, 0, begin) != 0
                    || uses.reads(local, end + 1, uses.count) != 0
                    || !facts.local_definitions_reference_unaliased(local)
                {
                    return None;
                }
            }
            let mut debug = None;
            for local in rows.iter().copied().chain([final_state, boolean]) {
                if local != state
                    && (context.proto.local_debug_hints[local.index()].is_some()
                        || context.proto.local_debug_scopes[local.index()].is_some())
                {
                    return None;
                }
            }
            if context.proto.local_debug_hints[state.index()].is_some()
                || context.proto.local_debug_scopes[state.index()].is_some()
            {
                let scope = context.proto.debug_scopes
                    [context.proto.local_debug_scopes[state.index()]?]
                .as_ref()?;
                let initial = scope.initializer_temp?;
                // 候选拒绝[ProofIncomplete:Binding]：只转交 child 角色及完整原区间确认的 debug 身份。
                if context.proto.local_debug_hints[state.index()] != callee.result_name
                    || callee.result_name.is_none()
                    || facts.promoted_local_for_temp(initial) != Some(state)
                    || facts.trusted_temp_home_slot(initial) != Some(home(3))
                    || facts.operation_result_temp(HirSourceSite {
                        proto: context.proto.id,
                        instr: scope.initializer_end_instr?,
                    }) != Some(initial)
                    || scope.initializer_end_instr?
                        >= match first.access.sources {
                            HirOperationSources::Single(site) => site.instr,
                            _ => return None,
                        }
                    || scope.end_instr?.index() != source.instr.index() + 1
                    || scope.initializer_phi.is_some()
                    || scope.branch_initializer.is_some()
                    || scope.ends_before_return
                {
                    return None;
                }
                debug = Some((state, initial));
            }
            let invocation = factories::factory_call(
                callee.local,
                Some(source),
                vec![HirExpr::LocalRef(input), HirExpr::Integer(limit)].into(),
            );
            let mut comparison = compare.clone();
            comparison.lhs = invocation;
            let mut call = observe.call.clone();
            call.callee = global.clone();
            call.args = vec![HirExpr::Binary(comparison)].into();
            let mut plan = factories::invocation(callee, source, home(0), state, begin, end);
            plan.result_locals.clear();
            plan.values = vec![HirExpr::Call(Box::new(call))].into();
            plan.replayed_effects = (begin..coordinate(position)).collect();
            Some((position + 3, source, base + 2, plan, debug, callee.local))
        })();
        if let Some((next, source, slot, plan, debug, callee)) = candidate {
            if let Some((local, initial)) = debug {
                let draft = result.draft.get_or_insert_with(|| context.proto.clone());
                draft.local_debug_hints[local.index()] = None;
                draft.local_debug_scopes[local.index()] = None;
                draft.temp_debug_locals[initial.index()] = None;
                draft.temp_debug_scopes[initial.index()] = None;
                result.obligations.push((source, callee));
            }
            result.plans.push(plan);
            result.result_slots.insert(source, slot);
            start = next;
        } else {
            start += 1;
        }
    }
    result
}
