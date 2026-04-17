//! 这个文件负责把“已经明显跨语句存活的 temp”提升成 HIR local。
//!
//! 我们这里故意不去猜所有 temp 都是不是源码变量，而是只抓一类非常稳的形状：
//! 当前 block 顶层先有一次初始化，后面这批 SSA temp 通过简单别名链继续流动，并且
//! 在后续语句里继续被读/写。对这类值，继续保留 `t12 / t13 / ...` 只会让 HIR 充满
//! 版本噪音，把它们折回同一个 `LocalId` 更接近源码，也能为后续 AST/Naming 铺路。
//!
//! 另外，如果某个 local 已经被 closure capture 观察到，后续来自同一寄存器槽位的
//! 新 def 不该再长成新的 local，而应继续写回原绑定。否则 closure 会继续指向旧 local，
//! 后半段写回却被拆到新绑定里，直接改掉源码语义。
//!
//! 提升完成后，同一个 block 里还会执行两步后处理：
//! 1. branch-value 折叠：`local X; if cond then X=a else X=b end` → `local X = expr`
//! 2. 相邻 local-assign 合并：`local X; X = expr` → `local X = expr`
//!
//! 这两步原先分别在独立的 `branch_value_exprs` pass 和 AST `statement_merge` 里执行，
//! 整合到提升出口后可以减少跨 pass 迭代和跨层机械修补。

use std::collections::{BTreeMap, BTreeSet};

use super::branch_value_folding::{
    fold_branch_value_locals_in_block, matches_local_lvalue,
};
use super::temp_touch::{
    collect_temp_refs_in_stmts, expr_touches_any_temp,
    stmt_consumes_temps_only_in_control_head, stmt_contains_nested_nonlocal_control,
    stmt_touches_any_temp, stmts_touch_temp,
};
use crate::hir::common::{
    HirAssign, HirBlock, HirCallExpr, HirExpr, HirLValue, HirLocalDecl,
    HirProto, HirStmt, HirTableConstructor, HirTableField, HirTableKey, LocalId, TempId,
};
use crate::hir::promotion::ProtoPromotionFacts;

/// 对单个 proto 执行保守的 temp -> local 提升。
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn promote_temps_to_locals_in_proto(proto: &mut HirProto) -> bool {
    promote_temps_to_locals_in_proto_with_facts(proto, &ProtoPromotionFacts::default())
}

/// 对单个 proto 执行带 promotion facts 的 temp -> local 提升。
pub(super) fn promote_temps_to_locals_in_proto_with_facts(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
) -> bool {
    let mut next_local_index = proto.locals.len();
    let mut new_locals = Vec::new();
    let mut new_local_debug_hints = Vec::new();
    let mut ctx = PromotionCtx {
        facts,
        temp_debug_locals: &proto.temp_debug_locals,
        next_local_index: &mut next_local_index,
        new_locals: &mut new_locals,
        new_local_debug_hints: &mut new_local_debug_hints,
    };
    let result = promote_block(
        &mut ctx,
        &mut proto.body,
        &BTreeMap::new(),
        &BTreeMap::new(),
        &BTreeSet::new(),
    );
    proto.locals.extend(new_locals);
    proto.local_debug_hints.extend(new_local_debug_hints);
    result.changed
}

#[derive(Debug, Clone)]
struct PromotionPlan {
    decl_index: usize,
    local: LocalId,
    home_slot: Option<usize>,
    temps: BTreeSet<TempId>,
    removable_aliases: BTreeSet<usize>,
    init: PromotionInit,
    action: PromotionAction,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum PromotionInit {
    FromAssign,
    Empty,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum PromotionAction {
    AllocateLocal,
    ReuseExistingLocal,
}

#[derive(Debug, Clone, Default)]
struct FallthroughSummary {
    falls_through: bool,
    assigned_temps: BTreeSet<TempId>,
}

struct PromotionResult {
    changed: bool,
    trailing_mapping: BTreeMap<TempId, LocalId>,
}

struct PromotionCtx<'a> {
    facts: &'a ProtoPromotionFacts,
    temp_debug_locals: &'a [Option<String>],
    next_local_index: &'a mut usize,
    new_locals: &'a mut Vec<LocalId>,
    new_local_debug_hints: &'a mut Vec<Option<String>>,
}

struct PlanAllocator<'a> {
    temp_debug_locals: &'a [Option<String>],
    plans: &'a mut Vec<PromotionPlan>,
    reserved_temps: &'a mut BTreeSet<TempId>,
    reserved_alias_indices: &'a mut BTreeSet<usize>,
    next_local_index: &'a mut usize,
    new_locals: &'a mut Vec<LocalId>,
    new_local_debug_hints: &'a mut Vec<Option<String>>,
}

impl PlanAllocator<'_> {
    fn allocate_local(
        &mut self,
        decl_index: usize,
        home_slot: Option<usize>,
        temps: BTreeSet<TempId>,
        removable_aliases: BTreeSet<usize>,
        init: PromotionInit,
    ) {
        let local = LocalId(*self.next_local_index);
        *self.next_local_index += 1;
        self.new_locals.push(local);
        self.new_local_debug_hints
            .push(debug_hint_for_temp_group(self.temp_debug_locals, &temps));
        self.reserved_temps.extend(temps.iter().copied());
        self.reserved_alias_indices
            .extend(removable_aliases.iter().copied());
        self.plans.push(PromotionPlan {
            decl_index,
            local,
            home_slot,
            temps,
            removable_aliases,
            init,
            action: PromotionAction::AllocateLocal,
        });
    }

    fn reuse_existing_local(
        &mut self,
        decl_index: usize,
        local: LocalId,
        home_slot: Option<usize>,
        temps: BTreeSet<TempId>,
        removable_aliases: BTreeSet<usize>,
        init: PromotionInit,
    ) {
        self.reserved_temps.extend(temps.iter().copied());
        self.reserved_alias_indices
            .extend(removable_aliases.iter().copied());
        self.plans.push(PromotionPlan {
            decl_index,
            local,
            home_slot,
            temps,
            removable_aliases,
            init,
            action: PromotionAction::ReuseExistingLocal,
        });
    }
}

fn promote_block(
    ctx: &mut PromotionCtx<'_>,
    block: &mut HirBlock,
    inherited: &BTreeMap<TempId, LocalId>,
    inherited_sticky_slots: &BTreeMap<usize, LocalId>,
    outer_used_temps: &BTreeSet<TempId>,
) -> PromotionResult {
    // 预计算后缀 temp 引用集：suffix_temps[i] 包含 stmts[i..] 中出现的所有 temp。
    // 当递归进入子作用域（while/if/for 等）时，合并 outer_used_temps 和
    // suffix_temps[i+1] 传给子 promote_block，防止子作用域将外层仍需引用的 temp
    // 错误地提升为块级局部变量。
    let suffix_temps = compute_suffix_temp_refs(&block.stmts);

    let plans = collect_plans(ctx, block, inherited, inherited_sticky_slots, outer_used_temps);
    let plan_by_decl = plans.iter().fold(
        BTreeMap::<usize, Vec<&PromotionPlan>>::new(),
        |mut grouped, plan| {
            grouped.entry(plan.decl_index).or_default().push(plan);
            grouped
        },
    );
    let removable = plans
        .iter()
        .flat_map(|plan| plan.removable_aliases.iter().copied())
        .collect::<BTreeSet<_>>();

    let mut changed = !plans.is_empty();
    let mut mapping = inherited.clone();
    let mut slot_candidates = inherited_sticky_slots.clone();
    let mut active_sticky_slots = inherited_sticky_slots.clone();
    let original_stmts = std::mem::take(&mut block.stmts);
    let mut rewritten = Vec::with_capacity(original_stmts.len());

    for (index, mut stmt) in original_stmts.into_iter().enumerate() {
        let mut replaced_stmt = false;
        if let Some(plans) = plan_by_decl.get(&index) {
            let mapping_before_decl = mapping.clone();
            for plan in plans {
                if let Some(anchor_stmt) =
                    rewrite_plan_anchor_stmt(&stmt, plan, &mapping_before_decl)
                {
                    rewritten.push(anchor_stmt);
                }
                for temp in &plan.temps {
                    mapping.insert(*temp, plan.local);
                }
                if let Some(slot) = plan.home_slot
                    && matches!(plan.action, PromotionAction::AllocateLocal)
                {
                    slot_candidates.entry(slot).or_insert(plan.local);
                }
                replaced_stmt |= plan_replaces_original_stmt(plan);
            }
        }
        activate_captured_slots_in_stmt(
            &stmt,
            ctx.facts,
            &slot_candidates,
            &mut active_sticky_slots,
        );
        if replaced_stmt {
            continue;
        }

        if removable.contains(&index) {
            continue;
        }

        // 子作用域的 outer temps = 当前块后续语句的 temp 引用 ∪ 来自祖先作用域的保护集
        let child_outer_temps = merge_temp_sets(outer_used_temps, &suffix_temps[index + 1]);
        let stmt_changed = rewrite_stmt(
            ctx,
            &mut stmt,
            &mapping,
            &active_sticky_slots,
            &child_outer_temps,
        );
        changed |= stmt_changed;
        rewritten.push(stmt);
    }

    block.stmts = rewritten;

    // 互递归前向引用修补：closure capture 可能引用在当前语句之后才被提升的 temp，
    // 第一次遍历时该 temp 还不在 mapping 里。用最终映射对 closure capture 做一次
    // 定向重写，避免留下悬空的 TempRef。
    if mapping.len() > inherited.len() {
        for stmt in &mut block.stmts {
            rewrite_forward_capture_refs(stmt, &mapping);
        }
    }

    // 后处理：把 `local X; if cond then X=a else X=b end` 收回值表达式
    changed |= fold_branch_value_locals_in_block(&mut block.stmts);
    // 后处理：把相邻的 `local X; X = expr` 合并成 `local X = expr`
    changed |= merge_adjacent_local_assigns_in_block(&mut block.stmts);

    PromotionResult {
        changed,
        trailing_mapping: mapping,
    }
}

/// 计算后缀 temp 引用集。suffix[i] = stmts[i..] 中出现的所有 temp 的集合。
fn compute_suffix_temp_refs(stmts: &[HirStmt]) -> Vec<BTreeSet<TempId>> {
    let mut suffix = vec![BTreeSet::new(); stmts.len() + 1];
    for i in (0..stmts.len()).rev() {
        suffix[i] = suffix[i + 1].clone();
        let stmt_temps = collect_temp_refs_in_stmts(std::slice::from_ref(&stmts[i]));
        suffix[i].extend(stmt_temps);
    }
    suffix
}

/// 合并两个 temp 集合，返回并集。
fn merge_temp_sets(a: &BTreeSet<TempId>, b: &BTreeSet<TempId>) -> BTreeSet<TempId> {
    a.union(b).copied().collect()
}

// ── 后处理：相邻 local-assign 合并 ───────────────────────────────────

/// 扫描 block 中相邻的 `local X; X = expr` 形状，合并成 `local X = expr`。
///
/// 这对应 AST readability `statement_merge` 的 `try_merge_local_decl_with_assign` 规则，
/// 在 HIR 层提前执行可以减少流到 AST 层的机械拆分数量。
fn merge_adjacent_local_assigns_in_block(stmts: &mut Vec<HirStmt>) -> bool {
    let mut changed = false;
    let mut index = 0;

    while index + 1 < stmts.len() {
        let Some(merged) = try_merge_empty_local_with_assign(&stmts[index], &stmts[index + 1])
        else {
            index += 1;
            continue;
        };

        stmts[index] = HirStmt::LocalDecl(Box::new(merged));
        stmts.remove(index + 1);
        changed = true;
    }

    changed
}

fn try_merge_empty_local_with_assign(
    decl_stmt: &HirStmt,
    assign_stmt: &HirStmt,
) -> Option<HirLocalDecl> {
    let HirStmt::LocalDecl(local_decl) = decl_stmt else {
        return None;
    };
    let HirStmt::Assign(assign) = assign_stmt else {
        return None;
    };
    if !local_decl.values.is_empty() || local_decl.bindings.is_empty() {
        return None;
    }
    if local_decl.bindings.len() != assign.targets.len() || assign.values.is_empty() {
        return None;
    }
    if !local_decl
        .bindings
        .iter()
        .zip(assign.targets.iter())
        .all(|(binding, target)| matches_local_lvalue(target, *binding))
    {
        return None;
    }
    Some(HirLocalDecl {
        bindings: local_decl.bindings.clone(),
        values: assign.values.clone(),
    })
}

fn collect_plans(
    ctx: &mut PromotionCtx<'_>,
    block: &HirBlock,
    inherited: &BTreeMap<TempId, LocalId>,
    inherited_sticky_slots: &BTreeMap<usize, LocalId>,
    outer_used_temps: &BTreeSet<TempId>,
) -> Vec<PromotionPlan> {
    if block.stmts.iter().any(|stmt| {
        matches!(
            stmt,
            HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_) | HirStmt::Unstructured(_)
        )
    }) {
        return Vec::new();
    }

    let facts = ctx.facts;
    let temp_debug_locals = ctx.temp_debug_locals;
    let mut plans = Vec::new();
    let mut reserved_temps = inherited.keys().copied().collect::<BTreeSet<_>>();
    let mut reserved_alias_indices = BTreeSet::new();
    let mut slot_candidates = inherited_sticky_slots.clone();
    let mut sticky_slots = inherited_sticky_slots.clone();

    for (decl_index, stmt) in block.stmts.iter().enumerate() {
        if reserved_alias_indices.contains(&decl_index) {
            activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
            continue;
        }

        let Some(root_temp) = simple_temp_assign_target(stmt) else {
            activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
            continue;
        };
        if reserved_temps.contains(&root_temp) {
            activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
            continue;
        }
        // 外层作用域仍在引用的 temp 不能在子作用域提升为块级 local，
        // 否则外层读到的是一个永远未被赋值的孤儿 temp。
        if outer_used_temps.contains(&root_temp) {
            activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
            continue;
        }
        // 目标 temp 自己又出现在 RHS 里时，这条赋值表达的是“沿用同一状态槽位继续更新”，
        // 不能在 locals pass 里把它误提升成新的 block-local。否则像 loop carried state
        // 或分支内的状态写回，会被拆成 `local next = step(state)`，原状态槽位反而失去写回。
        if stmt_self_updates_temp(stmt, root_temp) {
            activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
            continue;
        }

        let mut group = BTreeSet::from([root_temp]);
        let mut removable_aliases = BTreeSet::new();
        let mut has_future_touch = false;

        for future_index in decl_index + 1..block.stmts.len() {
            if removable_aliases.contains(&future_index) {
                continue;
            }
            let future_stmt = &block.stmts[future_index];

            if let Some(alias_temp) = alias_temp_for_group(future_stmt, &group)
                && !reserved_temps.contains(&alias_temp)
                && !group.contains(&alias_temp)
                && !stmts_touch_temp(&block.stmts[decl_index + 1..future_index], alias_temp)
            {
                group.insert(alias_temp);
                removable_aliases.insert(future_index);
                continue;
            }

            if stmt_touches_any_temp(future_stmt, &group) {
                has_future_touch = true;
            }
        }

        let sticky_local = facts
            .home_slot(root_temp)
            .and_then(|slot| sticky_slots.get(&slot).copied());

        if sticky_local.is_none() && !has_future_touch {
            activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
            continue;
        }
        if sticky_local.is_none() {
            // 只在控制头里单次消费的 temp，更像机械性的结构参数而不是源码级 local。
            let touching_stmt_indices = (decl_index + 1..block.stmts.len())
                .filter(|future_index| !removable_aliases.contains(future_index))
                .filter(|future_index| stmt_touches_any_temp(&block.stmts[*future_index], &group))
                .collect::<Vec<_>>();
            if touching_stmt_indices.len() == 1
                && stmt_consumes_temps_only_in_control_head(
                    &block.stmts[touching_stmt_indices[0]],
                    &group,
                )
            {
                activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
                continue;
            }
            if touching_stmt_indices
                .iter()
                .copied()
                .any(|stmt_index| stmt_contains_nested_nonlocal_control(&block.stmts[stmt_index]))
            {
                activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
                continue;
            }
        }

        let mut allocator = PlanAllocator {
            temp_debug_locals,
            plans: &mut plans,
            reserved_temps: &mut reserved_temps,
            reserved_alias_indices: &mut reserved_alias_indices,
            next_local_index: ctx.next_local_index,
            new_locals: ctx.new_locals,
            new_local_debug_hints: ctx.new_local_debug_hints,
        };
        if let Some(local) = sticky_local {
            allocator.reuse_existing_local(
                decl_index,
                local,
                facts.home_slot(root_temp),
                group.clone(),
                removable_aliases,
                PromotionInit::FromAssign,
            );
        } else {
            let slot = facts.home_slot(root_temp);
            allocator.allocate_local(
                decl_index,
                slot,
                group.clone(),
                removable_aliases,
                PromotionInit::FromAssign,
            );
            if let Some(slot) = slot
                && let Some(local) = allocator.plans.last().map(|plan| plan.local)
            {
                slot_candidates.entry(slot).or_insert(local);
            }
        }

        activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
    }

    let mut sticky_slots = inherited_sticky_slots.clone();
    for (decl_index, stmt) in block.stmts.iter().enumerate() {
        let merge_temps = if_merge_candidate_temps(
            stmt,
            &block.stmts[..decl_index],
            &block.stmts[decl_index + 1..],
            &reserved_temps,
        );

        for temp in merge_temps {
            let mut allocator = PlanAllocator {
                temp_debug_locals,
                plans: &mut plans,
                reserved_temps: &mut reserved_temps,
                reserved_alias_indices: &mut reserved_alias_indices,
                next_local_index: ctx.next_local_index,
                new_locals: ctx.new_locals,
                new_local_debug_hints: ctx.new_local_debug_hints,
            };
            if let Some(local) = facts
                .home_slot(temp)
                .and_then(|slot| sticky_slots.get(&slot).copied())
            {
                allocator.reuse_existing_local(
                    decl_index,
                    local,
                    facts.home_slot(temp),
                    BTreeSet::from([temp]),
                    BTreeSet::new(),
                    PromotionInit::Empty,
                );
            } else {
                let slot = facts.home_slot(temp);
                allocator.allocate_local(
                    decl_index,
                    slot,
                    BTreeSet::from([temp]),
                    BTreeSet::new(),
                    PromotionInit::Empty,
                );
                if let Some(slot) = slot
                    && let Some(local) = allocator.plans.last().map(|plan| plan.local)
                {
                    slot_candidates.entry(slot).or_insert(local);
                }
            }
        }
        activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
    }

    plans
}

fn activate_captured_slots_in_stmt(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
    slot_candidates: &BTreeMap<usize, LocalId>,
    sticky_slots: &mut BTreeMap<usize, LocalId>,
) {
    let mut captured_slots = BTreeSet::new();
    facts.collect_captured_home_slots_in_stmt(stmt, &mut captured_slots);
    for slot in captured_slots {
        if let Some(local) = slot_candidates.get(&slot).copied() {
            sticky_slots.insert(slot, local);
        }
    }
}

fn simple_temp_assign_target(stmt: &HirStmt) -> Option<TempId> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(temp)] = assign.targets.as_slice() else {
        return None;
    };
    let [_value] = assign.values.as_slice() else {
        return None;
    };
    Some(*temp)
}

fn alias_temp_for_group(stmt: &HirStmt, group: &BTreeSet<TempId>) -> Option<TempId> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(alias)] = assign.targets.as_slice() else {
        return None;
    };
    let [HirExpr::TempRef(source)] = assign.values.as_slice() else {
        return None;
    };
    group.contains(source).then_some(*alias)
}

fn stmt_self_updates_temp(stmt: &HirStmt, temp: TempId) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    matches!(assign.targets.as_slice(), [HirLValue::Temp(id)] if *id == temp)
        && assign
            .values
            .iter()
            .any(|value| expr_touches_any_temp(value, &BTreeSet::from([temp])))
}

fn if_merge_candidate_temps(
    stmt: &HirStmt,
    prior_stmts: &[HirStmt],
    future_stmts: &[HirStmt],
    reserved_temps: &BTreeSet<TempId>,
) -> Vec<TempId> {
    let HirStmt::If(if_stmt) = stmt else {
        return Vec::new();
    };
    let Some(else_block) = &if_stmt.else_block else {
        return Vec::new();
    };

    let then_summary = summarize_block_fallthrough_assignments(&if_stmt.then_block);
    let else_summary = summarize_block_fallthrough_assignments(else_block);
    let Some(common_temps) =
        intersect_fallthrough_assignment_sets([then_summary.as_ref(), else_summary.as_ref()])
    else {
        return Vec::new();
    };

    common_temps
        .into_iter()
        .filter(|temp| !reserved_temps.contains(temp))
        .filter(|temp| !stmts_touch_temp(prior_stmts, *temp))
        .filter(|temp| stmts_touch_temp(future_stmts, *temp))
        .collect()
}

fn summarize_block_fallthrough_assignments(block: &HirBlock) -> Option<FallthroughSummary> {
    let mut assigned_temps = BTreeSet::new();
    let mut falls_through = true;

    for stmt in &block.stmts {
        if !falls_through {
            break;
        }

        let stmt_summary = summarize_stmt_fallthrough_assignments(stmt)?;
        if stmt_summary.falls_through {
            assigned_temps.extend(stmt_summary.assigned_temps);
        } else {
            falls_through = false;
        }
    }

    Some(FallthroughSummary {
        falls_through,
        assigned_temps,
    })
}

fn summarize_stmt_fallthrough_assignments(stmt: &HirStmt) -> Option<FallthroughSummary> {
    match stmt {
        HirStmt::LocalDecl(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Label(_) => Some(FallthroughSummary {
            falls_through: true,
            assigned_temps: BTreeSet::new(),
        }),
        HirStmt::Assign(assign) => Some(FallthroughSummary {
            falls_through: true,
            assigned_temps: assign
                .targets
                .iter()
                .filter_map(|target| match target {
                    HirLValue::Temp(temp) => Some(*temp),
                    HirLValue::Local(_)
                    | HirLValue::Upvalue(_)
                    | HirLValue::Global(_)
                    | HirLValue::TableAccess(_) => None,
                })
                .collect(),
        }),
        HirStmt::TableSetList(_) => None,
        HirStmt::Return(_) | HirStmt::Goto(_) | HirStmt::Break | HirStmt::Continue => {
            Some(FallthroughSummary {
                falls_through: false,
                assigned_temps: BTreeSet::new(),
            })
        }
        HirStmt::If(if_stmt) => {
            let else_block = if_stmt.else_block.as_ref()?;
            let then_summary = summarize_block_fallthrough_assignments(&if_stmt.then_block)?;
            let else_summary = summarize_block_fallthrough_assignments(else_block)?;
            let assigned_temps =
                intersect_fallthrough_assignment_sets([Some(&then_summary), Some(&else_summary)])
                    .unwrap_or_default();

            Some(FallthroughSummary {
                falls_through: then_summary.falls_through || else_summary.falls_through,
                assigned_temps,
            })
        }
        HirStmt::Block(block) => summarize_block_fallthrough_assignments(block),
        HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Unstructured(_) => None,
    }
}

fn intersect_fallthrough_assignment_sets<'a>(
    summaries: impl IntoIterator<Item = Option<&'a FallthroughSummary>>,
) -> Option<BTreeSet<TempId>> {
    let mut fallthrough_sets = summaries
        .into_iter()
        .flatten()
        .filter(|summary| summary.falls_through)
        .map(|summary| summary.assigned_temps.clone());
    let mut intersection = fallthrough_sets.next()?;
    for set in fallthrough_sets {
        intersection = intersection
            .intersection(&set)
            .copied()
            .collect::<BTreeSet<_>>();
    }
    Some(intersection)
}

fn rewrite_plan_anchor_stmt(
    stmt: &HirStmt,
    plan: &PromotionPlan,
    mapping: &BTreeMap<TempId, LocalId>,
) -> Option<HirStmt> {
    let values = match plan.init {
        PromotionInit::FromAssign => {
            let HirStmt::Assign(assign) = stmt else {
                return None;
            };
            let [HirLValue::Temp(_temp)] = assign.targets.as_slice() else {
                return None;
            };

            assign
                .values
                .iter()
                .cloned()
                .map(|mut expr| {
                    rewrite_expr(&mut expr, mapping);
                    expr
                })
                .collect::<Vec<_>>()
        }
        PromotionInit::Empty => Vec::new(),
    };

    match (plan.action, plan.init) {
        (PromotionAction::AllocateLocal, _) => Some(HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![plan.local],
            values,
        }))),
        (PromotionAction::ReuseExistingLocal, PromotionInit::FromAssign) => {
            Some(HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(plan.local)],
                values,
            })))
        }
        (PromotionAction::ReuseExistingLocal, PromotionInit::Empty) => None,
    }
}

fn plan_replaces_original_stmt(plan: &PromotionPlan) -> bool {
    matches!(plan.init, PromotionInit::FromAssign)
}

fn rewrite_stmt(
    ctx: &mut PromotionCtx<'_>,
    stmt: &mut HirStmt,
    mapping: &BTreeMap<TempId, LocalId>,
    sticky_slots: &BTreeMap<usize, LocalId>,
    outer_used_temps: &BTreeSet<TempId>,
) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            let mut changed = false;
            for expr in &mut local_decl.values {
                changed |= rewrite_expr(expr, mapping);
            }
            changed
        }
        HirStmt::Assign(assign) => {
            let mut targets_changed = false;
            for target in &mut assign.targets {
                targets_changed |= rewrite_lvalue(target, mapping);
            }
            let mut values_changed = false;
            for expr in &mut assign.values {
                values_changed |= rewrite_expr(expr, mapping);
            }
            targets_changed || values_changed
        }
        HirStmt::TableSetList(set_list) => {
            let base_changed = rewrite_expr(&mut set_list.base, mapping);
            let mut values_changed = false;
            for expr in &mut set_list.values {
                values_changed |= rewrite_expr(expr, mapping);
            }
            let trailing_changed = set_list
                .trailing_multivalue
                .as_mut()
                .is_some_and(|expr| rewrite_expr(expr, mapping));
            base_changed || values_changed || trailing_changed
        }
        HirStmt::ErrNil(err_nil) => rewrite_expr(&mut err_nil.value, mapping),
        HirStmt::ToBeClosed(to_be_closed) => rewrite_expr(&mut to_be_closed.value, mapping),
        HirStmt::CallStmt(call_stmt) => rewrite_call_expr(&mut call_stmt.call, mapping),
        HirStmt::Return(ret) => {
            let mut changed = false;
            for expr in &mut ret.values {
                changed |= rewrite_expr(expr, mapping);
            }
            changed
        }
        HirStmt::If(if_stmt) => {
            let cond_changed = rewrite_expr(&mut if_stmt.cond, mapping);
            let then_changed =
                promote_block(ctx, &mut if_stmt.then_block, mapping, sticky_slots, outer_used_temps)
                    .changed;
            let else_changed = if_stmt.else_block.as_mut().is_some_and(|else_block| {
                promote_block(ctx, else_block, mapping, sticky_slots, outer_used_temps).changed
            });
            cond_changed || then_changed || else_changed
        }
        HirStmt::While(while_stmt) => {
            let cond_changed = rewrite_expr(&mut while_stmt.cond, mapping);
            let body_changed =
                promote_block(ctx, &mut while_stmt.body, mapping, sticky_slots, outer_used_temps)
                    .changed;
            cond_changed || body_changed
        }
        HirStmt::Repeat(repeat_stmt) => {
            // `repeat ... until` 的条件和 loop body 共享同一个词法作用域。
            // body 里刚刚提升出来的 local 如果不继续带到条件里，条件就会继续挂着旧 temp，
            // 最后得到“body 已经是 l2，until 里还是 t3”这种半截 HIR。
            let body_result =
                promote_block(ctx, &mut repeat_stmt.body, mapping, sticky_slots, outer_used_temps);
            let cond_changed = rewrite_expr(&mut repeat_stmt.cond, &body_result.trailing_mapping);
            body_result.changed || cond_changed
        }
        HirStmt::NumericFor(numeric_for) => {
            let start_changed = rewrite_expr(&mut numeric_for.start, mapping);
            let limit_changed = rewrite_expr(&mut numeric_for.limit, mapping);
            let step_changed = rewrite_expr(&mut numeric_for.step, mapping);
            let body_changed =
                promote_block(ctx, &mut numeric_for.body, mapping, sticky_slots, outer_used_temps)
                    .changed;
            start_changed || limit_changed || step_changed || body_changed
        }
        HirStmt::GenericFor(generic_for) => {
            let mut iterator_changed = false;
            for expr in &mut generic_for.iterator {
                iterator_changed |= rewrite_expr(expr, mapping);
            }
            let body_changed =
                promote_block(ctx, &mut generic_for.body, mapping, sticky_slots, outer_used_temps)
                    .changed;
            iterator_changed || body_changed
        }
        HirStmt::Block(block) => {
            promote_block(ctx, block, mapping, sticky_slots, outer_used_temps).changed
        }
        HirStmt::Unstructured(unstructured) => {
            promote_block(ctx, &mut unstructured.body, mapping, sticky_slots, outer_used_temps)
                .changed
        }
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn debug_hint_for_temp_group(
    temp_debug_locals: &[Option<String>],
    temps: &BTreeSet<TempId>,
) -> Option<String> {
    temps
        .iter()
        .find_map(|temp| temp_debug_locals.get(temp.index()).cloned().flatten())
}

fn rewrite_call_expr(call: &mut HirCallExpr, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    let callee_changed = rewrite_expr(&mut call.callee, mapping);
    let mut args_changed = false;
    for arg in &mut call.args {
        args_changed |= rewrite_expr(arg, mapping);
    }
    callee_changed || args_changed
}

fn rewrite_expr(expr: &mut HirExpr, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    match expr {
        HirExpr::TempRef(temp) => {
            if let Some(local) = mapping.get(temp) {
                *expr = HirExpr::LocalRef(*local);
                true
            } else {
                false
            }
        }
        HirExpr::TableAccess(access) => {
            let base_changed = rewrite_expr(&mut access.base, mapping);
            let key_changed = rewrite_expr(&mut access.key, mapping);
            base_changed || key_changed
        }
        HirExpr::Unary(unary) => rewrite_expr(&mut unary.expr, mapping),
        HirExpr::Binary(binary) => {
            let lhs_changed = rewrite_expr(&mut binary.lhs, mapping);
            let rhs_changed = rewrite_expr(&mut binary.rhs, mapping);
            lhs_changed || rhs_changed
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            let lhs_changed = rewrite_expr(&mut logical.lhs, mapping);
            let rhs_changed = rewrite_expr(&mut logical.rhs, mapping);
            lhs_changed || rhs_changed
        }
        HirExpr::Decision(decision) => {
            let mut changed = false;
            for node in &mut decision.nodes {
                let test_changed = rewrite_expr(&mut node.test, mapping);
                let truthy_changed = rewrite_decision_target(&mut node.truthy, mapping);
                let falsy_changed = rewrite_decision_target(&mut node.falsy, mapping);
                changed |= test_changed || truthy_changed || falsy_changed;
            }
            changed
        }
        HirExpr::Call(call) => rewrite_call_expr(call, mapping),
        HirExpr::TableConstructor(table) => rewrite_table_constructor(table, mapping),
        HirExpr::Closure(closure) => {
            let mut changed = false;
            for capture in &mut closure.captures {
                changed |= rewrite_expr(&mut capture.value, mapping);
            }
            changed
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}

fn rewrite_decision_target(
    target: &mut crate::hir::common::HirDecisionTarget,
    mapping: &BTreeMap<TempId, LocalId>,
) -> bool {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => rewrite_expr(expr, mapping),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => false,
    }
}

fn rewrite_table_constructor(
    table: &mut HirTableConstructor,
    mapping: &BTreeMap<TempId, LocalId>,
) -> bool {
    let mut fields_changed = false;
    for field in &mut table.fields {
        let field_changed = match field {
            HirTableField::Array(expr) => rewrite_expr(expr, mapping),
            HirTableField::Record(field) => {
                let key_changed = match &mut field.key {
                    HirTableKey::Name(_) => false,
                    HirTableKey::Expr(expr) => rewrite_expr(expr, mapping),
                };
                let value_changed = rewrite_expr(&mut field.value, mapping);
                key_changed || value_changed
            }
        };
        fields_changed |= field_changed;
    }
    let trailing_changed = table
        .trailing_multivalue
        .as_mut()
        .is_some_and(|expr| rewrite_expr(expr, mapping));

    fields_changed || trailing_changed
}

fn rewrite_lvalue(lvalue: &mut HirLValue, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    match lvalue {
        HirLValue::Temp(temp) => {
            if let Some(local) = mapping.get(temp) {
                *lvalue = HirLValue::Local(*local);
                true
            } else {
                false
            }
        }
        HirLValue::TableAccess(access) => {
            let base_changed = rewrite_expr(&mut access.base, mapping);
            let key_changed = rewrite_expr(&mut access.key, mapping);
            base_changed || key_changed
        }
        HirLValue::Local(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => false,
    }
}

/// 对语句中 closure capture 里残留的 TempRef 做定向重写。
///
/// 互递归/前向声明模式下（`local a, b; a = function() b()… end; b = function() a()… end`），
/// 第一次遍历 promote_block 时 b 的 temp 尚未加入 mapping，导致 a 的 capture 仍是
/// TempRef。这里用最终 mapping 补一次定向重写，只处理 closure capture 这一种残留，
/// 避免做全量二次遍历。
fn rewrite_forward_capture_refs(stmt: &mut HirStmt, mapping: &BTreeMap<TempId, LocalId>) {
    match stmt {
        HirStmt::Assign(assign) => {
            for expr in &mut assign.values {
                rewrite_closure_capture_temps(expr, mapping);
            }
        }
        HirStmt::LocalDecl(local_decl) => {
            for expr in &mut local_decl.values {
                rewrite_closure_capture_temps(expr, mapping);
            }
        }
        _ => {}
    }
}

fn rewrite_closure_capture_temps(expr: &mut HirExpr, mapping: &BTreeMap<TempId, LocalId>) {
    if let HirExpr::Closure(closure) = expr {
        for capture in &mut closure.captures {
            rewrite_expr(&mut capture.value, mapping);
        }
    }
}

#[cfg(test)]
mod tests;
