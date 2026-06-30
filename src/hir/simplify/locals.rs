//! 这个文件负责把“已经明显跨语句存活的 temp”提升成 HIR local，并收回由此暴露的
//! 函数入口参数别名。
//!
//! 我们这里故意不去猜所有 temp 都是不是源码变量，而是只抓一类非常稳的形状：
//! 当前 block 顶层先有一次初始化，后面这批 SSA temp 通过简单别名链继续流动，并且
//! 在后续语句里继续被读/写。对这类值，继续保留 `t12 / t13 / ...` 只会让 HIR 充满
//! 版本噪音，把它们折回同一个 `LocalId` 更接近源码，也能为后续 AST/Naming 铺路。
//! 如果整条 temp 链只被一个后续语句消费，则仍把它视为寄存器级中转值，不在这里提升；
//! 后续 temp-inline / table-constructor 会结合具体消费站点继续收敛。
//!
//! 另外，如果某个 local 已经被 closure capture 观察到，后续来自同一词法槽位的
//! 新 def 不该再长成新的 local，而应继续写回原绑定。这里的“同一词法槽位”会把
//! `close from rX` 纳入身份；close 后复用同一个寄存器号不能再写回旧 upvalue。
//! 否则 closure 会继续指向旧 local，后半段写回却被拆到新绑定里，或把 close 后的
//! 普通临时值误写进已关闭 upvalue，直接改掉源码语义。
//! fallback label/goto 还可能让 loop 回边快照在文本上早于 temp 定义出现；这种 temp
//! 不能在定义点提升成 `local`，否则前缀快照会读到尚未初始化的局部变量。
//! 参数别名收敛是 locals 的收尾步骤：如果提升后只得到 `local L = param` / `local L; L = param`
//! 这类函数入口机械别名，且后续不会观察到参数原值和 alias local 的差异，就直接把
//! 后续读写改回参数身份。它不重新推断 phi 或 loop state，只处理 locals 自己稳定暴露的
//! binding 形状。
//!
mod branch_merge;
mod param_alias;
mod rewrite;

use std::collections::{BTreeMap, BTreeSet};

use super::temp_touch::{
    TempRefScopeTracker, TempTouchIndex, collect_temp_refs_by_stmt, expr_touches_any_temp,
    stmt_consumes_temps_only_in_control_head, stmt_contains_nested_nonlocal_control,
};
use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirLValue, HirLocalDecl, HirProto, HirStmt, LocalId, TempId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

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
    let alias_changed = param_alias::coalesce_param_aliases_in_proto(proto);
    result.changed || alias_changed
}

#[derive(Debug, Clone)]
struct PromotionPlan {
    decl_index: usize,
    local: LocalId,
    home_slot: Option<HomeSlotKey>,
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
        home_slot: Option<HomeSlotKey>,
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
        home_slot: Option<HomeSlotKey>,
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
    inherited_sticky_slots: &BTreeMap<HomeSlotKey, LocalId>,
    outer_used_temps: &BTreeSet<TempId>,
) -> PromotionResult {
    // 递归进入子作用域时，把当前语句之后仍被外层引用的 temp 传给子 block。
    // tracker 用引用计数维护后缀集合，避免为每个 index 克隆一份成长中的 BTreeSet。
    let stmt_temp_refs = collect_temp_refs_by_stmt(&block.stmts);
    let mut temp_refs = TempRefScopeTracker::new(&stmt_temp_refs);

    let plans = collect_plans(
        ctx,
        block,
        &stmt_temp_refs,
        inherited,
        inherited_sticky_slots,
        outer_used_temps,
    );
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
        temp_refs.enter_stmt(index);
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
            temp_refs.leave_stmt(index);
            continue;
        }

        if removable.contains(&index) {
            temp_refs.leave_stmt(index);
            continue;
        }

        // 子作用域的 outer temps = 当前块后续语句的 temp 引用 ∪ 来自祖先作用域的保护集
        let child_outer_temps = temp_refs.outer_with_suffix(outer_used_temps);
        let stmt_changed = rewrite_stmt(
            ctx,
            &mut stmt,
            &mapping,
            &active_sticky_slots,
            &child_outer_temps,
        );
        changed |= stmt_changed;
        rewritten.push(stmt);
        temp_refs.leave_stmt(index);
    }

    block.stmts = rewritten;

    // 互递归前向引用修补：closure capture 可能引用在当前语句之后才被提升的 temp，
    // 第一次遍历时该 temp 还不在 mapping 里。用最终映射对 closure capture 做一次
    // 定向重写，避免留下悬空的 TempRef。
    if mapping.len() > inherited.len() {
        for stmt in &mut block.stmts {
            rewrite::forward_capture_refs(stmt, &mapping);
        }
    }

    PromotionResult {
        changed,
        trailing_mapping: mapping,
    }
}

fn collect_plans(
    ctx: &mut PromotionCtx<'_>,
    block: &HirBlock,
    stmt_temp_refs: &[BTreeSet<TempId>],
    inherited: &BTreeMap<TempId, LocalId>,
    inherited_sticky_slots: &BTreeMap<HomeSlotKey, LocalId>,
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
    let temp_touches = TempTouchIndex::new(stmt_temp_refs);
    let mut reserved_temps = inherited.keys().copied().collect::<BTreeSet<_>>();
    let mut reserved_alias_indices = BTreeSet::new();
    let mut slot_candidates = inherited_sticky_slots.clone();
    let mut sticky_slots = inherited_sticky_slots.clone();

    for (decl_index, stmt) in block.stmts.iter().enumerate() {
        if reserved_alias_indices.contains(&decl_index) {
            activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
            continue;
        }

        let mut sticky_slots_for_stmt = sticky_slots.clone();
        activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots_for_stmt);

        let Some(root_temp) = simple_temp_assign_target(stmt) else {
            sticky_slots = sticky_slots_for_stmt;
            continue;
        };
        if reserved_temps.contains(&root_temp) {
            sticky_slots = sticky_slots_for_stmt;
            continue;
        }
        if temp_touches.touches_before(decl_index, root_temp) {
            sticky_slots = sticky_slots_for_stmt;
            continue;
        }
        // 外层作用域仍在引用的 temp 不能在子作用域提升为块级 local，
        // 否则外层读到的是一个永远未被赋值的孤儿 temp。
        if outer_used_temps.contains(&root_temp) {
            sticky_slots = sticky_slots_for_stmt;
            continue;
        }
        // 目标 temp 自己又出现在 RHS 里时，这条赋值表达的是“沿用同一状态槽位继续更新”，
        // 不能在 locals pass 里把它误提升成新的 block-local。否则像 loop carried state
        // 或分支内的状态写回，会被拆成 `local next = step(state)`，原状态槽位反而失去写回。
        if stmt_self_updates_temp(stmt, root_temp) {
            sticky_slots = sticky_slots_for_stmt;
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
                && !temp_touches.touches_in_range(decl_index + 1, future_index, alias_temp)
            {
                group.insert(alias_temp);
                removable_aliases.insert(future_index);
                continue;
            }

            if temp_touches.stmt_touches_any(future_index, &group) {
                has_future_touch = true;
            }
        }

        let sticky_local = facts
            .home_slot(root_temp)
            .and_then(|slot| sticky_slots_for_stmt.get(&slot).copied());

        if sticky_local.is_none() && !has_future_touch {
            sticky_slots = sticky_slots_for_stmt;
            continue;
        }
        if sticky_local.is_none() {
            // 只在控制头里单次消费的 temp，更像机械性的结构参数而不是源码级 local。
            let touching_stmt_indices = (decl_index + 1..block.stmts.len())
                .filter(|future_index| !removable_aliases.contains(future_index))
                .filter(|future_index| temp_touches.stmt_touches_any(*future_index, &group))
                .collect::<Vec<_>>();
            // 只有一次后续消费的全局别名或字符串常量，必须结合消费站点判定：
            // 全局别名只有作为表字段安装的 base，字符串常量只有作为调用实参，
            // 才更像寄存器级脚手架而不是源码 local。数字/布尔/nil 等也可能是
            // 捕获 local 的重绑定值，仍按原规则保守提升。
            if touching_stmt_indices.len() == 1
                && (stmt_consumes_temps_only_in_control_head(
                    &block.stmts[touching_stmt_indices[0]],
                    &group,
                ) || single_use_seed_can_stay_temp(
                    stmt,
                    root_temp,
                    &block.stmts[touching_stmt_indices[0]],
                ))
            {
                sticky_slots = sticky_slots_for_stmt;
                continue;
            }
            if touching_stmt_indices
                .iter()
                .copied()
                .any(|stmt_index| stmt_contains_nested_nonlocal_control(&block.stmts[stmt_index]))
            {
                sticky_slots = sticky_slots_for_stmt;
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

        sticky_slots = sticky_slots_for_stmt;
    }

    let mut sticky_slots = inherited_sticky_slots.clone();
    for (decl_index, stmt) in block.stmts.iter().enumerate() {
        let merge_temps =
            branch_merge::candidate_temps(stmt, &temp_touches, decl_index, &reserved_temps);

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
    slot_candidates: &BTreeMap<HomeSlotKey, LocalId>,
    sticky_slots: &mut BTreeMap<HomeSlotKey, LocalId>,
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

fn single_use_seed_can_stay_temp(def_stmt: &HirStmt, temp: TempId, use_stmt: &HirStmt) -> bool {
    let Some(value) = single_temp_assign_value(def_stmt, temp) else {
        return false;
    };
    match value {
        HirExpr::GlobalRef(_) => stmt_uses_temp_as_assign_table_base(use_stmt, temp),
        HirExpr::String(_) => stmt_uses_temp_as_assign_call_arg(use_stmt, temp),
        _ => false,
    }
}

fn single_temp_assign_value(stmt: &HirStmt, temp: TempId) -> Option<&HirExpr> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(target)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    if *target != temp {
        return None;
    }
    Some(value)
}

fn stmt_uses_temp_as_assign_table_base(stmt: &HirStmt, temp: TempId) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    assign
        .targets
        .iter()
        .any(|target| lvalue_uses_temp_as_table_base(target, temp))
}

fn lvalue_uses_temp_as_table_base(lvalue: &HirLValue, temp: TempId) -> bool {
    let HirLValue::TableAccess(access) = lvalue else {
        return false;
    };
    expr_is_temp_ref(&access.base, temp) || expr_uses_temp_as_table_access_base(&access.base, temp)
}

fn stmt_uses_temp_as_assign_call_arg(stmt: &HirStmt, temp: TempId) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    assign
        .values
        .iter()
        .any(|value| expr_uses_temp_as_call_arg(value, temp))
}

fn expr_uses_temp_as_call_arg(expr: &HirExpr, temp: TempId) -> bool {
    match expr {
        HirExpr::Call(call) => call.args.iter().any(|arg| expr_is_temp_ref(arg, temp)),
        HirExpr::TableAccess(access) => {
            expr_uses_temp_as_call_arg(&access.base, temp)
                || expr_uses_temp_as_call_arg(&access.key, temp)
        }
        _ => false,
    }
}

fn expr_uses_temp_as_table_access_base(expr: &HirExpr, temp: TempId) -> bool {
    let HirExpr::TableAccess(access) = expr else {
        return false;
    };
    expr_is_temp_ref(&access.base, temp) || expr_uses_temp_as_table_access_base(&access.base, temp)
}

fn expr_is_temp_ref(expr: &HirExpr, temp: TempId) -> bool {
    matches!(expr, HirExpr::TempRef(other) if *other == temp)
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
                    rewrite::expr(&mut expr, mapping);
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
    sticky_slots: &BTreeMap<HomeSlotKey, LocalId>,
    outer_used_temps: &BTreeSet<TempId>,
) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            let mut changed = false;
            for expr in &mut local_decl.values {
                changed |= rewrite::expr(expr, mapping);
            }
            changed
        }
        HirStmt::Assign(assign) => {
            let mut targets_changed = false;
            for target in &mut assign.targets {
                targets_changed |= rewrite::lvalue(target, mapping);
            }
            let mut values_changed = false;
            for expr in &mut assign.values {
                values_changed |= rewrite::expr(expr, mapping);
            }
            targets_changed || values_changed
        }
        HirStmt::TableSetList(set_list) => {
            let base_changed = rewrite::expr(&mut set_list.base, mapping);
            let mut values_changed = false;
            for expr in &mut set_list.values {
                values_changed |= rewrite::expr(expr, mapping);
            }
            let trailing_changed = set_list
                .trailing_multivalue
                .as_mut()
                .is_some_and(|expr| rewrite::expr(expr, mapping));
            base_changed || values_changed || trailing_changed
        }
        HirStmt::ErrNil(err_nil) => rewrite::expr(&mut err_nil.value, mapping),
        HirStmt::ToBeClosed(to_be_closed) => rewrite::expr(&mut to_be_closed.value, mapping),
        HirStmt::CallStmt(call_stmt) => rewrite::call_expr(&mut call_stmt.call, mapping),
        HirStmt::Return(ret) => {
            let mut changed = false;
            for expr in &mut ret.values {
                changed |= rewrite::expr(expr, mapping);
            }
            changed
        }
        HirStmt::If(if_stmt) => {
            let cond_changed = rewrite::expr(&mut if_stmt.cond, mapping);
            let then_changed = promote_block(
                ctx,
                &mut if_stmt.then_block,
                mapping,
                sticky_slots,
                outer_used_temps,
            )
            .changed;
            let else_changed = if_stmt.else_block.as_mut().is_some_and(|else_block| {
                promote_block(ctx, else_block, mapping, sticky_slots, outer_used_temps).changed
            });
            cond_changed || then_changed || else_changed
        }
        HirStmt::While(while_stmt) => {
            let cond_changed = rewrite::expr(&mut while_stmt.cond, mapping);
            let body_changed = promote_block(
                ctx,
                &mut while_stmt.body,
                mapping,
                sticky_slots,
                outer_used_temps,
            )
            .changed;
            cond_changed || body_changed
        }
        HirStmt::Repeat(repeat_stmt) => {
            // `repeat ... until` 的条件和 loop body 共享同一个词法作用域。
            // body 里刚刚提升出来的 local 如果不继续带到条件里，条件就会继续挂着旧 temp，
            // 最后得到“body 已经是 l2，until 里还是 t3”这种半截 HIR。
            let body_result = promote_block(
                ctx,
                &mut repeat_stmt.body,
                mapping,
                sticky_slots,
                outer_used_temps,
            );
            let cond_changed = rewrite::expr(&mut repeat_stmt.cond, &body_result.trailing_mapping);
            body_result.changed || cond_changed
        }
        HirStmt::NumericFor(numeric_for) => {
            let start_changed = rewrite::expr(&mut numeric_for.start, mapping);
            let limit_changed = rewrite::expr(&mut numeric_for.limit, mapping);
            let step_changed = rewrite::expr(&mut numeric_for.step, mapping);
            let body_changed = promote_block(
                ctx,
                &mut numeric_for.body,
                mapping,
                sticky_slots,
                outer_used_temps,
            )
            .changed;
            start_changed || limit_changed || step_changed || body_changed
        }
        HirStmt::GenericFor(generic_for) => {
            let mut iterator_changed = false;
            for expr in &mut generic_for.iterator {
                iterator_changed |= rewrite::expr(expr, mapping);
            }
            let body_changed = promote_block(
                ctx,
                &mut generic_for.body,
                mapping,
                sticky_slots,
                outer_used_temps,
            )
            .changed;
            iterator_changed || body_changed
        }
        HirStmt::Block(block) => {
            promote_block(ctx, block, mapping, sticky_slots, outer_used_temps).changed
        }
        HirStmt::Unstructured(unstructured) => {
            promote_block(
                ctx,
                &mut unstructured.body,
                mapping,
                sticky_slots,
                outer_used_temps,
            )
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
