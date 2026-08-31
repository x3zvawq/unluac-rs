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
//! 不同 home slot 上的 move alias 是当时值的快照，不能与来源槽位后续的状态合并；
//! 没有 trusted home slot 的 phi temp 可以单独提升，但不能吸收 move alias：缺少未污染的
//! 物理身份时无法证明两个槽位的 GC root、capture cell 与跨块 value epoch 相同。
//! 对没有 debug local 证据、home-slot 定义和根 block 直接 temp 绑定压力都已经超过
//! 源码局部槽上限的大函数，同一 `(slot, close epoch)` 会复用一个 local；两个门同时
//! 成立才能证明这是源码层的局部数压力，而不是单纯由 SSA 拆分制造的定义数。物理覆盖
//! 保证旧值已死，close epoch 与 capture sticky 事实继续隔离不同词法身份。候选扩张只沿
//! temp occurrence index 访问真实 touch，不按“每个定义 × 全部后缀语句”重复扫描。
//! 没有 debug/capture 身份且只被写入、从未被表达式读取的 temp 链继续保留为 temp，交给
//! dead-temp 清理删除纯写入；把这类链提升成 local 只会把可删除的 SSA 壳固化到源码里。
//! carried-local fixed point 若已让某个 binding 吸收不同或未知 home，后续 promotion 仍可
//! 建立源码 local，但不能借原始槽号复用 sticky/debug local：raw home 只登记给 capture/TBC
//! 保护，组内所有 temp 的 trusted home 完全一致时才参与正向复用，taint 再传播到新 local；
//! 含引用 capture 的 temp 组若不能证明同槽，则保持 temp，避免丢失 capture cell 身份。
//! promotion plan 会在候选形成时冻结初始化值；apply 只消费已验证的 plan，不再重新匹配
//! anchor 语句。`while` 条件里的 temp 则作为跨迭代消费者保护到 body，避免把回边写回
//! 误删成一次性的 move alias。
//!
mod branch_merge;
mod entry_nil;
mod param_alias;
mod rewrite;

use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use super::mention::{
    stmts_reference_captured_bindings, stmts_to_be_closed_temps, stmts_value_captured_bindings,
};
use super::root_lifetimes::{
    collect_call_root_lifetimes, collect_gc_fence_indices, collect_lookup_gc_root_lifetimes,
};
use super::temp_touch::{
    TempRefScopeTracker, TempTouchIndex, collect_temp_reads_by_stmt, collect_temp_refs_by_stmt,
    collect_temp_refs_in_expr, expr_touches_any_temp, stmt_consumes_temps_only_in_control_head,
    stmt_contains_nested_nonlocal_control,
};
use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirLValue, HirLocalDecl, HirProto, HirStmt, HirValuePack,
    LocalId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

/// 对单个 proto 执行带 promotion facts 的 temp -> local 提升。
pub(super) fn promote_temps_to_locals_in_proto_with_facts(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    let compact_home_slots = hir_block_local_pressure(&proto.body) > crate::SOURCE_LOCAL_LIMIT
        && facts.home_slot_definition_count() > crate::SOURCE_LOCAL_LIMIT
        && proto.temp_debug_locals.iter().all(Option::is_none);
    if compact_home_slots {
        facts.enable_home_slot_compaction();
    }
    let mut next_local_index = proto.locals.len();
    let mut new_locals = Vec::new();
    let mut new_local_debug_hints = Vec::new();
    let mut physical_root_locals = BTreeSet::new();
    let mut promoted_bindings = Vec::new();
    let mut direct_seed_promotions = Vec::new();
    let mut debug_scope_locals = BTreeMap::new();
    let mut identity_sensitive_temps = stmts_reference_captured_bindings(&proto.body.stmts).temps;
    identity_sensitive_temps.extend(stmts_value_captured_bindings(&proto.body.stmts).temps);
    let to_be_closed_temps = stmts_to_be_closed_temps(&proto.body.stmts);
    identity_sensitive_temps.extend(to_be_closed_temps.iter().copied());
    let result = {
        let mut ctx = PromotionCtx {
            facts,
            safety,
            temp_debug_locals: &proto.temp_debug_locals,
            temp_debug_scopes: &proto.temp_debug_scopes,
            next_local_index: &mut next_local_index,
            new_locals: &mut new_locals,
            new_local_debug_hints: &mut new_local_debug_hints,
            physical_root_locals: &mut physical_root_locals,
            promoted_bindings: &mut promoted_bindings,
            direct_seed_promotions: &mut direct_seed_promotions,
            identity_sensitive_temps: &identity_sensitive_temps,
            to_be_closed_temps: &to_be_closed_temps,
            debug_scope_locals: &mut debug_scope_locals,
            compact_home_slots,
        };
        let empty_mapping = Rc::new(BTreeMap::new());
        promote_block(
            &mut ctx,
            &mut proto.body,
            &empty_mapping,
            &BTreeMap::new(),
            &|_| false,
        )
    };
    for (temp, local) in promoted_bindings.iter().copied() {
        if let Some(home_slot) = facts.home_slot(temp) {
            facts.record_local_home_slot(local, home_slot);
        }
    }
    for (temp, local) in promoted_bindings.iter().copied() {
        facts.record_entry_nil_phi_promotion(temp, local);
    }
    for (temp, local) in direct_seed_promotions {
        facts.record_direct_table_seed_promotion(temp, local);
    }
    for (temp, local) in promoted_bindings {
        facts.record_temp_to_local_merge(temp, local);
    }
    proto.locals.extend(new_locals);
    proto.local_debug_hints.extend(new_local_debug_hints);
    proto.physical_root_locals.extend(physical_root_locals);
    let entry_nil_changed = entry_nil::prune_redundant_entry_nil_writes(proto, facts, safety);
    let alias_changed = param_alias::coalesce_param_aliases_in_proto(proto, facts, safety);
    result.changed || entry_nil_changed || alias_changed
}

fn hir_block_local_pressure(block: &HirBlock) -> usize {
    block
        .stmts
        .iter()
        .map(|stmt| match stmt {
            HirStmt::Assign(assign) => assign
                .targets
                .iter()
                .filter(|target| matches!(target, HirLValue::Temp(_)))
                .count(),
            HirStmt::LocalDecl(local) => local.bindings.len(),
            _ => 0,
        })
        .sum()
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
    batch_empty_decl: bool,
}

#[derive(Debug, Clone)]
enum PromotionInit {
    FromAssign(HirValuePack),
    Empty,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum PromotionAction {
    AllocateLocal,
    ReuseExistingLocal,
}

struct PromotionResult {
    changed: bool,
    trailing_mapping: LocalMapping,
}

type LocalMapping = Rc<BTreeMap<TempId, LocalId>>;

struct PromotionGroup {
    temps: BTreeSet<TempId>,
    removable_aliases: BTreeSet<usize>,
    touching_stmt_indices: BTreeSet<usize>,
}

fn trusted_home_slot_for_group(
    temps: &BTreeSet<TempId>,
    facts: &ProtoPromotionFacts,
) -> Option<HomeSlotKey> {
    let mut slots = temps.iter().map(|temp| facts.trusted_temp_home_slot(*temp));
    let slot = slots.next().flatten()?;
    slots
        .all(|candidate| candidate == Some(slot))
        .then_some(slot)
}

struct PromotionCtx<'a> {
    facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
    temp_debug_locals: &'a [Option<String>],
    temp_debug_scopes: &'a [Option<usize>],
    next_local_index: &'a mut usize,
    new_locals: &'a mut Vec<LocalId>,
    new_local_debug_hints: &'a mut Vec<Option<String>>,
    physical_root_locals: &'a mut BTreeSet<LocalId>,
    promoted_bindings: &'a mut Vec<(TempId, LocalId)>,
    direct_seed_promotions: &'a mut Vec<(TempId, LocalId)>,
    identity_sensitive_temps: &'a BTreeSet<TempId>,
    to_be_closed_temps: &'a BTreeSet<TempId>,
    debug_scope_locals: &'a mut BTreeMap<(HomeSlotKey, usize), LocalId>,
    compact_home_slots: bool,
}

struct PlanAllocator<'a> {
    temp_debug_locals: &'a [Option<String>],
    temp_debug_scopes: &'a [Option<usize>],
    plans: &'a mut Vec<PromotionPlan>,
    reserved_temps: &'a mut BTreeSet<TempId>,
    reserved_alias_indices: &'a mut BTreeSet<usize>,
    next_local_index: &'a mut usize,
    new_locals: &'a mut Vec<LocalId>,
    new_local_debug_hints: &'a mut Vec<Option<String>>,
    promoted_bindings: &'a mut Vec<(TempId, LocalId)>,
    direct_seed_promotions: &'a mut Vec<(TempId, LocalId)>,
    debug_scope_locals: &'a mut BTreeMap<(HomeSlotKey, usize), LocalId>,
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
        if let Some(home_slot) = home_slot
            && let Some(scope) = debug_scope_for_temp_group(self.temp_debug_scopes, &temps)
        {
            self.debug_scope_locals.insert((home_slot, scope), local);
        }
        self.reserved_temps.extend(temps.iter().copied());
        self.promoted_bindings
            .extend(temps.iter().map(|temp| (*temp, local)));
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
            batch_empty_decl: false,
        });
    }

    fn allocate_batched_empty_local(
        &mut self,
        decl_index: usize,
        home_slot: HomeSlotKey,
        temp: TempId,
    ) -> LocalId {
        let local = LocalId(*self.next_local_index);
        *self.next_local_index += 1;
        self.new_locals.push(local);
        self.new_local_debug_hints.push(
            self.temp_debug_locals
                .get(temp.index())
                .cloned()
                .unwrap_or_default(),
        );
        self.reserved_temps.insert(temp);
        self.promoted_bindings.push((temp, local));
        self.plans.push(PromotionPlan {
            decl_index,
            local,
            home_slot: Some(home_slot),
            temps: BTreeSet::from([temp]),
            removable_aliases: BTreeSet::new(),
            init: PromotionInit::Empty,
            action: PromotionAction::AllocateLocal,
            batch_empty_decl: true,
        });
        local
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
        self.promoted_bindings
            .extend(temps.iter().map(|temp| (*temp, local)));
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
            batch_empty_decl: false,
        });
    }
}

fn promote_block(
    ctx: &mut PromotionCtx<'_>,
    block: &mut HirBlock,
    inherited: &LocalMapping,
    inherited_sticky_slots: &BTreeMap<HomeSlotKey, LocalId>,
    outer_uses_temp: &dyn Fn(TempId) -> bool,
) -> PromotionResult {
    promote_block_with_protection(
        ctx,
        block,
        inherited,
        inherited_sticky_slots,
        outer_uses_temp,
        &BTreeSet::new(),
        &BTreeSet::new(),
    )
}

fn promote_block_with_protection(
    ctx: &mut PromotionCtx<'_>,
    block: &mut HirBlock,
    inherited: &LocalMapping,
    inherited_sticky_slots: &BTreeMap<HomeSlotKey, LocalId>,
    outer_uses_temp: &dyn Fn(TempId) -> bool,
    current_plan_protected_temps: &BTreeSet<TempId>,
    descendant_protected_temps: &BTreeSet<TempId>,
) -> PromotionResult {
    record_gc_fenced_call_roots(block, ctx.physical_root_locals);

    // 每轮控制头等 block 外消费者先保护当前 block；递归进入子作用域时再叠加当前语句
    // 之后的引用。tracker 用引用计数维护后缀集合，避免按 index 克隆完整集合。
    let stmt_temp_refs = collect_temp_refs_by_stmt(&block.stmts);
    let mut temp_refs = TempRefScopeTracker::new(&stmt_temp_refs);

    let block_uses_outer_temp =
        |temp| outer_uses_temp(temp) || current_plan_protected_temps.contains(&temp);
    let plans = collect_plans(
        ctx,
        block,
        &stmt_temp_refs,
        inherited.as_ref(),
        inherited_sticky_slots,
        &block_uses_outer_temp,
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
    let mut mapping = Rc::clone(inherited);
    let mut slot_candidates = inherited_sticky_slots.clone();
    let mut active_sticky_slots = inherited_sticky_slots.clone();
    let original_stmts = std::mem::take(&mut block.stmts);
    let mut rewritten = Vec::with_capacity(original_stmts.len());

    for (index, mut stmt) in original_stmts.into_iter().enumerate() {
        temp_refs.enter_stmt(index);
        let mut replaced_stmt = false;
        if let Some(plans) = plan_by_decl.get(&index) {
            assert!(
                plans
                    .iter()
                    .filter(|plan| plan_replaces_original_stmt(plan))
                    .count()
                    <= 1,
                "one anchor cannot own multiple evaluating promotion plans"
            );
            let has_batch_empty_decl = plans.iter().any(|plan| plan.batch_empty_decl);
            if has_batch_empty_decl {
                assert!(
                    plans.iter().all(|plan| {
                        matches!(plan.init, PromotionInit::Empty)
                            && (plan.batch_empty_decl
                                == matches!(plan.action, PromotionAction::AllocateLocal))
                    }),
                    "batched physical roots may share their anchor only with empty handoffs"
                );
                rewritten.push(HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: plans
                        .iter()
                        .filter(|plan| plan.batch_empty_decl)
                        .map(|plan| plan.local)
                        .collect(),
                    values: HirValuePack::fixed(Vec::new()),
                })));
            } else {
                for plan in plans {
                    if let Some(anchor_stmt) = rewrite_plan_anchor_stmt(plan, mapping.as_ref()) {
                        rewritten.push(anchor_stmt);
                    }
                }
            }
            let mapping = Rc::make_mut(&mut mapping);
            for plan in plans {
                for temp in &plan.temps {
                    mapping.insert(*temp, plan.local);
                }
                if let Some(slot) = plan.home_slot
                    && matches!(plan.action, PromotionAction::AllocateLocal)
                {
                    slot_candidates.insert(slot, plan.local);
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
        let child_uses_outer_temp = |temp| {
            block_uses_outer_temp(temp)
                || descendant_protected_temps.contains(&temp)
                || temp_refs.suffix_contains(temp)
        };
        let stmt_changed = rewrite_stmt(
            ctx,
            &mut stmt,
            &mapping,
            &active_sticky_slots,
            &child_uses_outer_temp,
        );
        changed |= stmt_changed;
        if is_redundant_binding_self_assign(&stmt) {
            changed = true;
            temp_refs.leave_stmt(index);
            continue;
        }
        rewritten.push(stmt);
        temp_refs.leave_stmt(index);
    }

    block.stmts = rewritten;

    // 互递归前向引用修补：closure capture 可能引用在当前语句之后才被提升的 temp，
    // 第一次遍历时该 temp 还不在 mapping 里。用最终映射对 closure capture 做一次
    // 定向重写，避免留下悬空的 TempRef。
    if mapping.len() > inherited.len() {
        for stmt in &mut block.stmts {
            rewrite::forward_capture_refs(stmt, mapping.as_ref());
        }
    }

    PromotionResult {
        changed,
        trailing_mapping: mapping,
    }
}

fn record_gc_fenced_call_roots(block: &HirBlock, roots: &mut BTreeSet<LocalId>) {
    let mut active = BTreeSet::new();
    let fences = collect_gc_fence_indices(&block.stmts);
    for (index, stmt) in block.stmts.iter().enumerate() {
        if fences.contains(&index) {
            // Call local 的普通读取已结束时，fixed result 仍在原 VM home 里充当 root；lookup
            // 必须由 per-home overwrite collector 提供事实，不能在 fixed point 中 blanket 标记。
            roots.extend(active.iter().copied());
        }

        match stmt {
            HirStmt::Assign(assign) => {
                for target in &assign.targets {
                    if let HirLValue::Local(local) = target {
                        active.remove(local);
                    }
                }
                if let ([HirLValue::Local(local)], [HirExpr::Call(_)], None) = (
                    assign.targets.as_slice(),
                    assign.values.fixed.as_slice(),
                    &assign.values.tail,
                ) {
                    active.insert(*local);
                }
            }
            HirStmt::LocalDecl(decl) => {
                for local in &decl.bindings {
                    active.remove(local);
                }
                if let ([local], [HirExpr::Call(_)], None) = (
                    decl.bindings.as_slice(),
                    decl.values.fixed.as_slice(),
                    &decl.values.tail,
                ) {
                    active.insert(*local);
                }
            }
            _ => {}
        }
    }
}

fn collect_plans(
    ctx: &mut PromotionCtx<'_>,
    block: &HirBlock,
    stmt_temp_refs: &[BTreeSet<TempId>],
    inherited: &BTreeMap<TempId, LocalId>,
    inherited_sticky_slots: &BTreeMap<HomeSlotKey, LocalId>,
    outer_uses_temp: &dyn Fn(TempId) -> bool,
) -> Vec<PromotionPlan> {
    if block
        .stmts
        .iter()
        .any(|stmt| matches!(stmt, HirStmt::Goto(_) | HirStmt::Label(_)))
    {
        // 分析停用[ProofIncomplete]：当前 promotion 只有结构化作用域后缀事实，没有 label/goto 的 reaching-def 与声明可见区间；应接入 CFG dominance 后按可证明区间继续提升。
        return Vec::new();
    }

    let facts = ctx.facts;
    let temp_debug_locals = ctx.temp_debug_locals;
    let temp_debug_scopes = ctx.temp_debug_scopes;
    let stmt_temp_reads = collect_temp_reads_by_stmt(&block.stmts);
    let mut plans = Vec::new();
    let temp_touches = TempTouchIndex::new(stmt_temp_refs);
    let call_root_lifetimes = collect_call_root_lifetimes(
        &block.stmts,
        facts,
        ctx.safety,
        true,
        |temp| {
            // 候选拒绝[SemanticBarrier:Resource]：TBC producer 若提前声明 owner，会改变 close 起点与被关闭的值。
            // 候选拒绝[ProofIncomplete]：capture producer 仍缺少按 capture mode/cell epoch 的分组声明证明。
            // 候选拒绝[PolicyBoundary]：debug temp 的源码身份不由匿名 physical-root owner 取代。
            !ctx.identity_sensitive_temps.contains(&temp)
                && temp_debug_locals
                    .get(temp.index())
                    .is_none_or(Option::is_none)
        },
        |temp| {
            // 候选拒绝[SemanticBarrier:Resource]：TBC overwrite 必须在原位置建立新的 close owner，不能复用更早声明的 root local。
            // 候选拒绝[PolicyBoundary]：debug overwrite 继续由 debug-scope owner 选名；普通 capture 可精确复用同 home local。
            !ctx.to_be_closed_temps.contains(&temp)
                && temp_debug_locals
                    .get(temp.index())
                    .is_none_or(Option::is_none)
        },
    );
    let lookup_gc_root_lifetimes =
        collect_lookup_gc_root_lifetimes(&block.stmts, facts, ctx.safety, |temp| {
            !ctx.identity_sensitive_temps.contains(&temp)
                && !inherited.contains_key(&temp)
                && !outer_uses_temp(temp)
                && temp_debug_locals
                    .get(temp.index())
                    .is_none_or(Option::is_none)
        });
    let mut reserved_temps = BTreeSet::new();
    let mut reserved_alias_indices = BTreeSet::new();
    let mut slot_candidates = inherited_sticky_slots.clone();
    let mut sticky_slots = inherited_sticky_slots.clone();
    let mut physical_root_locals = BTreeMap::<usize, LocalId>::new();
    let mut physical_root_locals_by_home = BTreeMap::<(usize, HomeSlotKey), LocalId>::new();
    for (decl_index, stmt) in block.stmts.iter().enumerate() {
        if reserved_alias_indices.contains(&decl_index) {
            activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
            continue;
        }

        activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);

        let has_grouped_targets = matches!(stmt, HirStmt::If(_))
            || matches!(stmt, HirStmt::Assign(assign) if assign.targets.len() > 1);
        let physical_root_pairs = call_root_lifetimes
            .overwrite_pairs(decl_index)
            .filter(|_| has_grouped_targets)
            .map(|pair| (pair.root_index(), pair.home()))
            .chain(
                lookup_gc_root_lifetimes
                    .overwrite_pairs(decl_index)
                    .map(|pair| (pair.root_index(), pair.home())),
            )
            .collect::<Vec<_>>();
        let physical_root_handoffs = physical_root_pairs
            .iter()
            .map(|(root_index, home)| {
                let local = physical_root_locals_by_home
                    .get(&(*root_index, *home))
                    .copied()
                    .or_else(|| physical_root_locals.get(root_index).copied())
                    .unwrap_or_else(|| {
                        panic!(
                            "physical root producer {root_index} must be promoted before overwrite {decl_index} for home {home:?}"
                        )
                    });
                let temps = temp_assign_targets_for_home(stmt, facts, *home).unwrap_or_else(|| {
                    panic!(
                        "physical root overwrite {decl_index} must retain a target for home {home:?} (producer {root_index})"
                    )
                });
                (temps, *home, local)
            })
            .collect::<Vec<_>>();
        // 多 home overwrite 必须整条语句一起提交；任一 producer/target 无法对应时，不能只
        // 改写部分 target，留下一半仍写 temp、一半已写 local 的物理生命周期。
        for (temps, home, local) in physical_root_handoffs {
            let mut allocator = PlanAllocator {
                temp_debug_locals,
                temp_debug_scopes,
                plans: &mut plans,
                reserved_temps: &mut reserved_temps,
                reserved_alias_indices: &mut reserved_alias_indices,
                next_local_index: ctx.next_local_index,
                new_locals: ctx.new_locals,
                new_local_debug_hints: ctx.new_local_debug_hints,
                promoted_bindings: ctx.promoted_bindings,
                direct_seed_promotions: ctx.direct_seed_promotions,
                debug_scope_locals: ctx.debug_scope_locals,
            };
            // 原 scalar/parallel-nil/branch 语句继续留在原位；这里只把已证明 home 的
            // 全部 target 原子映射到既有 root local，不重新求值 RHS。
            allocator.reuse_existing_local(
                decl_index,
                local,
                Some(home),
                temps,
                BTreeSet::new(),
                PromotionInit::Empty,
            );
            if call_root_lifetimes.is_root(decl_index)
                || lookup_gc_root_lifetimes.is_root(decl_index)
            {
                // A scalar overwrite can terminate one physical-root transaction and produce
                // the next one in the same local. Preserve that chained owner for its later pair.
                physical_root_locals_by_home.insert((decl_index, home), local);
                slot_candidates.retain(|_, candidate| *candidate != local);
            }
        }

        let call_root_homes = call_root_lifetimes
            .root_homes(decl_index)
            .collect::<BTreeSet<_>>();
        if !call_root_homes.is_empty()
            && let HirStmt::Assign(assign) = stmt
            && assign.targets.len() > 1
        {
            let targets = assign
                .targets
                .iter()
                .map(|target| {
                    let HirLValue::Temp(temp) = target else {
                        panic!("multi-call root producer must retain only temp targets");
                    };
                    let home = facts
                        .trusted_temp_home_slot(*temp)
                        .expect("multi-call root producer target must retain its trusted home");
                    (*temp, home)
                })
                .collect::<Vec<_>>();
            assert_eq!(
                targets
                    .iter()
                    .map(|(_, home)| *home)
                    .collect::<BTreeSet<_>>()
                    .len(),
                targets.len(),
                "multi-call root producer homes must stay distinct"
            );
            let mut allocator = PlanAllocator {
                temp_debug_locals,
                temp_debug_scopes,
                plans: &mut plans,
                reserved_temps: &mut reserved_temps,
                reserved_alias_indices: &mut reserved_alias_indices,
                next_local_index: ctx.next_local_index,
                new_locals: ctx.new_locals,
                new_local_debug_hints: ctx.new_local_debug_hints,
                promoted_bindings: ctx.promoted_bindings,
                direct_seed_promotions: ctx.direct_seed_promotions,
                debug_scope_locals: ctx.debug_scope_locals,
            };
            for (temp, home) in targets {
                let existing_local = inherited.get(&temp).copied().or_else(|| {
                    physical_root_locals_by_home
                        .get(&(decl_index, home))
                        .copied()
                });
                let local = if let Some(local) = existing_local {
                    local
                } else if allocator.reserved_temps.contains(&temp) {
                    allocator
                        .plans
                        .iter()
                        .rev()
                        .find(|plan| plan.decl_index == decl_index && plan.temps.contains(&temp))
                        .map(|plan| plan.local)
                        .expect("reserved multi-call target must retain its promotion owner")
                } else {
                    allocator.allocate_batched_empty_local(decl_index, home, temp)
                };
                if call_root_homes.contains(&home) {
                    physical_root_locals_by_home.insert((decl_index, home), local);
                    slot_candidates.retain(|_, candidate| *candidate != local);
                }
            }
            continue;
        }

        let Some(root_temp) = simple_temp_assign_target(stmt) else {
            continue;
        };
        if inherited.contains_key(&root_temp) || reserved_temps.contains(&root_temp) {
            // 已被祖先映射或当前 plan 认领的 temp 不再形成新候选。
            continue;
        }
        if temp_touches.touches_before(decl_index, root_temp) {
            // 候选拒绝[ProofIncomplete]：候选定义前已有同 temp touch，但当前线性索引没有 reaching-def/循环迭代事实，无法证明从此处分裂源码 binding 仍覆盖全部路径。
            continue;
        }
        // 目标 temp 自己又出现在 RHS 里时，这条赋值表达的是“沿用同一状态槽位继续更新”，
        // 不能在 locals pass 里把它误提升成新的 block-local。否则像 loop carried state
        // 或分支内的状态写回，会被拆成 `local next = step(state)`，原状态槽位反而失去写回。
        if stmt_self_updates_temp(stmt, root_temp) {
            // 候选拒绝[SemanticBarrier:Lifetime]：`while c do t = t + 1 end; return t` 若在循环体新建 local，会丢失每轮对外层状态 t 的写回。
            continue;
        }

        let is_reserved = |temp| inherited.contains_key(&temp) || reserved_temps.contains(&temp);
        let PromotionGroup {
            temps: group,
            removable_aliases,
            touching_stmt_indices,
        } = collect_promotion_group(
            block,
            decl_index,
            root_temp,
            facts,
            &is_reserved,
            &temp_touches,
        );

        // 别名扩张后的任一 temp 仍被外层读取时，整个组都不能在子作用域提升；
        // 只检查 root 会让内层 local 吞掉外层 loop state 的别名。
        if group.iter().copied().any(outer_uses_temp) {
            // 候选拒绝[SemanticBarrier:Scope]：`while c do t = next end; return t` 若在循环体声明 t 的替代 local，循环外仍会读取未写回的旧 binding。
            continue;
        }

        let home_slot = trusted_home_slot_for_group(&group, facts);
        if home_slot.is_none()
            && group
                .iter()
                .any(|temp| ctx.identity_sensitive_temps.contains(temp))
        {
            // 候选拒绝[SemanticBarrier:Capture/Resource]：`f` 引用捕获 t0、move 后 `g` 捕获 t1、再覆盖 t0 时，缺同一 trusted home 却合并会让 f/g 错误共享 cell；TBC 同理会更换 close owner。
            // 候选拒绝[ProofIncomplete]：该 blanket 也包含按值 capture 与无 alias 的单节点组；应按 capture kind、组大小与实际 home 收窄。
            continue;
        }
        let sticky_local = home_slot.and_then(|slot| sticky_slots.get(&slot).copied());
        let debug_local = home_slot.and_then(|slot| {
            debug_scope_for_temp_group(temp_debug_scopes, &group)
                .and_then(|scope| ctx.debug_scope_locals.get(&(slot, scope)).copied())
        });
        let preceding_lookup_root = home_slot
            .and_then(|home| lookup_gc_root_lifetimes.overwrite_pair_for_home(decl_index, home))
            .map(|pair| pair.root_index());
        let preceding_call_root = home_slot
            .and_then(|home| call_root_lifetimes.overwrite_pair_for_home(decl_index, home))
            .map(|pair| pair.root_index())
            .or_else(|| call_root_lifetimes.unambiguous_root_for_overwrite(decl_index));
        let preceding_physical_root = preceding_call_root
            .or(preceding_lookup_root)
            .or_else(|| call_root_lifetimes.root_for_protected(decl_index));
        let preceding_physical_root_local = preceding_physical_root.and_then(|root| {
            home_slot
                .and_then(|home| physical_root_locals_by_home.get(&(root, home)).copied())
                .or_else(|| physical_root_locals.get(&root).copied())
        });
        let force_physical_root_local = call_root_lifetimes.is_root(decl_index)
            || lookup_gc_root_lifetimes.is_root(decl_index)
            || preceding_physical_root_local.is_some();
        let reusable_local = sticky_local
            .or(debug_local)
            .or(preceding_physical_root_local)
            .or_else(|| {
                ctx.compact_home_slots
                    .then(|| home_slot.and_then(|slot| slot_candidates.get(&slot).copied()))
                    .flatten()
            });

        if sticky_local.is_none()
            && !force_physical_root_local
            && touching_stmt_indices.is_empty()
            && debug_hint_for_temp_group(temp_debug_locals, &group).is_none()
        {
            // 候选拒绝[LayerBoundary]：零后续 touch 且无 debug identity 的匿名 temp 属于 dead-temps 的 effect-preserving 删除职责，locals 不把死 SSA 壳固化为 local。
            continue;
        }
        if sticky_local.is_none()
            && !force_physical_root_local
            && debug_hint_for_temp_group(temp_debug_locals, &group).is_none()
            && std::iter::once(decl_index)
                .chain(touching_stmt_indices.iter().copied())
                .all(|index| stmt_temp_reads[index].is_disjoint(&group))
        {
            // 候选拒绝[LayerBoundary]：只有写 touch、没有表达式读取且无 debug/capture/physical-root 身份的链交给 dead-temps 清理。
            continue;
        }
        if sticky_local.is_none() && !force_physical_root_local {
            let first_touch_index = touching_stmt_indices.first().copied();
            // 只在控制头里单次消费的 temp，更像机械性的结构参数而不是源码级 local。
            // 只有一次后续消费的全局别名或字符串常量，必须结合消费站点判定：
            // 全局别名只有作为表字段安装的 base，字符串常量只有作为调用实参，
            // 才更像寄存器级脚手架而不是源码 local。数字/布尔/nil 等也可能是
            // 捕获 local 的重绑定值，仍按原规则保守提升。
            if touching_stmt_indices.len() == 1
                && (stmt_consumes_temps_only_in_control_head(
                    &block.stmts[first_touch_index.expect("single touch must exist")],
                    &group,
                ) || single_use_seed_can_stay_temp(
                    stmt,
                    root_temp,
                    &block.stmts[first_touch_index.expect("single touch must exist")],
                ))
            {
                // 候选拒绝[PolicyBoundary]：只在控制头消费一次的匿名 temp 保持低密度展示；这不是运行语义边界。
                // 候选拒绝[LayerBoundary]：单次 global table-base/string call-arg seed 由 table-constructors 或 temp-inline 的具体消费站点收敛。
                continue;
            }
            if touching_stmt_indices
                .iter()
                .copied()
                .any(|stmt_index| stmt_contains_nested_nonlocal_control(&block.stmts[stmt_index]))
            {
                // 候选拒绝[ProofIncomplete]：候选 touch 位于含 nested exit/control 的语句时，当前顶层索引缺少必达路径与声明支配事实；应复用结构化 CFG exit summary。
                continue;
            }
        }

        let mut allocator = PlanAllocator {
            temp_debug_locals,
            temp_debug_scopes,
            plans: &mut plans,
            reserved_temps: &mut reserved_temps,
            reserved_alias_indices: &mut reserved_alias_indices,
            next_local_index: ctx.next_local_index,
            new_locals: ctx.new_locals,
            new_local_debug_hints: ctx.new_local_debug_hints,
            promoted_bindings: ctx.promoted_bindings,
            direct_seed_promotions: ctx.direct_seed_promotions,
            debug_scope_locals: ctx.debug_scope_locals,
        };
        let init = PromotionInit::FromAssign(
            simple_temp_assign_values(stmt)
                .expect("promotion root must retain its validated single-assignment shape"),
        );
        let selected_local = if let Some(local) = reusable_local {
            allocator.reuse_existing_local(
                decl_index,
                local,
                home_slot,
                group.clone(),
                removable_aliases,
                init,
            );
            local
        } else {
            allocator.allocate_local(
                decl_index,
                home_slot,
                group.clone(),
                removable_aliases,
                init,
            );
            let local = allocator
                .plans
                .last()
                .expect("allocated promotion plan must exist")
                .local;
            if let Some(slot) = home_slot {
                slot_candidates.insert(slot, local);
            }
            if ctx.facts.is_direct_table_seed_temp(root_temp) {
                allocator.direct_seed_promotions.push((root_temp, local));
            }
            local
        };
        if call_root_lifetimes.is_root(decl_index) || lookup_gc_root_lifetimes.is_root(decl_index) {
            physical_root_locals.insert(decl_index, selected_local);
            // This local must stay dedicated to the root result until its proven physical
            // overwrite partner reuses it. Home-slot compaction may otherwise lend the same
            // source local to a simultaneously-live value before that overwrite occurs.
            slot_candidates.retain(|_, candidate| *candidate != selected_local);
        }
    }

    // The AST cleanup pass cannot infer physical-slot lifetime from ordinary binding mentions.
    // Carry the proven root identity across the HIR -> AST boundary explicitly.
    ctx.physical_root_locals
        .extend(physical_root_locals.values().copied());
    ctx.physical_root_locals
        .extend(physical_root_locals_by_home.values().copied());

    let mut sticky_slots = inherited_sticky_slots.clone();
    for (decl_index, stmt) in block.stmts.iter().enumerate() {
        let is_reserved = |temp| inherited.contains_key(&temp) || reserved_temps.contains(&temp);
        let mut merge_temps = branch_merge::candidate_temps(
            stmt,
            &temp_touches,
            decl_index,
            &is_reserved,
            ctx.safety,
        );
        if (call_root_lifetimes
            .overwrite_pairs(decl_index)
            .next()
            .is_some()
            || lookup_gc_root_lifetimes
                .overwrite_pairs(decl_index)
                .next()
                .is_some())
            && let Some(branch_temps) = branch_merge::definite_if_arm_temp_writes(stmt)
        {
            for temp in branch_temps {
                if !merge_temps.contains(&temp) && !is_reserved(temp) {
                    merge_temps.push(temp);
                }
            }
        }

        for temp in merge_temps {
            // 分支合流也不能在子作用域重新声明外层仍在使用的状态 temp。
            if outer_uses_temp(temp) {
                // 候选拒绝[SemanticBarrier:Scope]：分支后的 temp 若仍由外层读取，在子 block 前声明替代 local 会让该读取继续观察旧 binding。
                continue;
            }
            let home_slot = facts.trusted_temp_home_slot(temp);
            if home_slot.is_none() && ctx.identity_sensitive_temps.contains(&temp) {
                // 候选拒绝[ProofIncomplete]：单个 branch result 被 capture/TBC 观察但缺 trusted home 时，当前没有 cell/close-owner provenance；按值 capture 应再按快照点证明后放行。
                continue;
            }
            let preceding_lookup_root = home_slot
                .and_then(|home| lookup_gc_root_lifetimes.overwrite_pair_for_home(decl_index, home))
                .map(|pair| pair.root_index());
            let preceding_call_root = home_slot
                .and_then(|home| call_root_lifetimes.overwrite_pair_for_home(decl_index, home))
                .map(|pair| pair.root_index())
                .or_else(|| call_root_lifetimes.unambiguous_root_for_overwrite(decl_index));
            let preceding_physical_root_local = preceding_call_root
                .or(preceding_lookup_root)
                .and_then(|root| {
                    home_slot
                        .and_then(|home| physical_root_locals_by_home.get(&(root, home)).copied())
                        .or_else(|| physical_root_locals.get(&root).copied())
                });
            let mut allocator = PlanAllocator {
                temp_debug_locals,
                temp_debug_scopes,
                plans: &mut plans,
                reserved_temps: &mut reserved_temps,
                reserved_alias_indices: &mut reserved_alias_indices,
                next_local_index: ctx.next_local_index,
                new_locals: ctx.new_locals,
                new_local_debug_hints: ctx.new_local_debug_hints,
                promoted_bindings: ctx.promoted_bindings,
                direct_seed_promotions: ctx.direct_seed_promotions,
                debug_scope_locals: ctx.debug_scope_locals,
            };
            if let Some(local) = preceding_physical_root_local.or_else(|| {
                home_slot.and_then(|slot| {
                    sticky_slots
                        .get(&slot)
                        .copied()
                        .or_else(|| {
                            debug_scope_for_temp_group(temp_debug_scopes, &BTreeSet::from([temp]))
                                .and_then(|scope| {
                                    allocator.debug_scope_locals.get(&(slot, scope)).copied()
                                })
                        })
                        .or_else(|| {
                            ctx.compact_home_slots
                                .then(|| slot_candidates.get(&slot).copied())
                                .flatten()
                        })
                })
            }) {
                allocator.reuse_existing_local(
                    decl_index,
                    local,
                    home_slot,
                    BTreeSet::from([temp]),
                    BTreeSet::new(),
                    PromotionInit::Empty,
                );
            } else {
                allocator.allocate_local(
                    decl_index,
                    home_slot,
                    BTreeSet::from([temp]),
                    BTreeSet::new(),
                    PromotionInit::Empty,
                );
                if let Some(slot) = home_slot
                    && let Some(local) = allocator.plans.last().map(|plan| plan.local)
                {
                    slot_candidates.insert(slot, local);
                }
            }
        }
        activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
    }

    plans
}

fn collect_promotion_group(
    block: &HirBlock,
    decl_index: usize,
    root_temp: TempId,
    facts: &ProtoPromotionFacts,
    is_reserved: &dyn Fn(TempId) -> bool,
    temp_touches: &TempTouchIndex<'_>,
) -> PromotionGroup {
    let root_slot = facts.trusted_temp_home_slot(root_temp);
    let mut temps = BTreeSet::from([root_temp]);
    let mut removable_aliases = BTreeSet::new();
    let mut touching_stmt_indices = BTreeSet::new();
    let mut pending_indices = BTreeSet::new();
    temp_touches.extend_touch_indices_after(decl_index + 1, root_temp, &mut pending_indices);

    while let Some(future_index) = pending_indices.pop_first() {
        if removable_aliases.contains(&future_index) {
            continue;
        }
        let future_stmt = &block.stmts[future_index];
        let alias = alias_temp_for_group(future_stmt, &temps).filter(|alias_temp| {
            let alias_slot = facts.trusted_temp_home_slot(*alias_temp);
            let shared_home = root_slot.zip(alias_slot);
            // 已认领或已在组内的 alias 不再形成新候选。
            // 候选拒绝[ProofIncomplete]：move 任一端缺 trusted home 时，当前事实不能证明物理 GC root、capture cell 与跨块 value epoch 相同。
            // 候选拒绝[SemanticBarrier:Lifetime]：两个已知不同 home 的 move 是独立 GC root；合并后覆盖 source 会让 alias 对象提前不可达。
            // 候选拒绝[SemanticBarrier:ValueFlow]：`next=f(carried); carried=next` 中 alias 在 root 定义前已被读取；删除写回会让下一轮继续读取入口 seed。
            !is_reserved(*alias_temp)
                && !temps.contains(alias_temp)
                && shared_home.is_some_and(|(root, alias)| root == alias)
                // `next = f(carried); carried = next` 是 loop 回边写回，不是可删除
                // alias。若 alias 的旧值已在 root 定义语句中参与求值，合并二者会删掉
                // 下一轮所需的写回，只留下每轮都读取入口 seed 的局部变量。
                && !temp_touches.touches_in_range(decl_index, future_index, *alias_temp)
        });
        if let Some(alias_temp) = alias {
            temps.insert(alias_temp);
            removable_aliases.insert(future_index);
            temp_touches.extend_touch_indices_after(
                future_index + 1,
                alias_temp,
                &mut pending_indices,
            );
        } else {
            touching_stmt_indices.insert(future_index);
        }
    }

    PromotionGroup {
        temps,
        removable_aliases,
        touching_stmt_indices,
    }
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
    let [_value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    Some(*temp)
}

fn temp_assign_targets_for_home(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
    home: HomeSlotKey,
) -> Option<BTreeSet<TempId>> {
    let temps = match stmt {
        HirStmt::Assign(assign) => assign
            .targets
            .iter()
            .filter_map(|target| {
                let HirLValue::Temp(temp) = target else {
                    return None;
                };
                (facts.trusted_temp_home_slot(*temp) == Some(home)).then_some(*temp)
            })
            .collect::<BTreeSet<_>>(),
        HirStmt::If(if_stmt) => {
            let else_block = if_stmt.else_block.as_ref()?;
            BTreeSet::from([
                scalar_temp_assign_target_for_home(&if_stmt.then_block, facts, home)?,
                scalar_temp_assign_target_for_home(else_block, facts, home)?,
            ])
        }
        _ => return None,
    };
    (!temps.is_empty()).then_some(temps)
}

fn scalar_temp_assign_target_for_home(
    block: &HirBlock,
    facts: &ProtoPromotionFacts,
    home: HomeSlotKey,
) -> Option<TempId> {
    let [HirStmt::Assign(assign)] = block.stmts.as_slice() else {
        return None;
    };
    let ([HirLValue::Temp(temp)], [_], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    (facts.trusted_temp_home_slot(*temp) == Some(home)).then_some(*temp)
}

fn is_redundant_binding_self_assign(stmt: &HirStmt) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    matches!(
        (assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
        ([HirLValue::Temp(target)], [HirExpr::TempRef(value)], None) if target == value
    ) || matches!(
        (assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
        ([HirLValue::Local(target)], [HirExpr::LocalRef(value)], None) if target == value
    )
}

fn alias_temp_for_group(stmt: &HirStmt, group: &BTreeSet<TempId>) -> Option<TempId> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(alias)] = assign.targets.as_slice() else {
        return None;
    };
    let [HirExpr::TempRef(source)] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
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
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    if *target != temp {
        return None;
    }
    Some(value)
}

fn simple_temp_assign_values(stmt: &HirStmt) -> Option<HirValuePack> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(_)] = assign.targets.as_slice() else {
        return None;
    };
    let [_] = assign.values.fixed.as_slice() else {
        return None;
    };
    assign.values.tail.is_none().then(|| assign.values.clone())
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
    plan: &PromotionPlan,
    mapping: &BTreeMap<TempId, LocalId>,
) -> Option<HirStmt> {
    let values = match &plan.init {
        PromotionInit::FromAssign(values) => {
            let mut values = values.clone();
            rewrite::value_pack(&mut values, mapping);
            values
        }
        PromotionInit::Empty => crate::hir::common::HirValuePack::fixed(Vec::new()),
    };

    match (plan.action, &plan.init) {
        (PromotionAction::AllocateLocal, _) => Some(HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![plan.local],
            values,
        }))),
        (PromotionAction::ReuseExistingLocal, PromotionInit::FromAssign(_)) => {
            Some(HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(plan.local)],
                values,
            })))
        }
        (PromotionAction::ReuseExistingLocal, PromotionInit::Empty) => None,
    }
}

fn plan_replaces_original_stmt(plan: &PromotionPlan) -> bool {
    matches!(plan.init, PromotionInit::FromAssign(_))
}

fn rewrite_stmt(
    ctx: &mut PromotionCtx<'_>,
    stmt: &mut HirStmt,
    mapping: &LocalMapping,
    sticky_slots: &BTreeMap<HomeSlotKey, LocalId>,
    outer_uses_temp: &dyn Fn(TempId) -> bool,
) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            rewrite::value_pack(&mut local_decl.values, mapping.as_ref())
        }
        HirStmt::GlobalDecl(global_decl) => {
            rewrite::value_pack(&mut global_decl.values, mapping.as_ref())
        }
        HirStmt::Assign(assign) => {
            let mut targets_changed = false;
            for target in &mut assign.targets {
                targets_changed |= rewrite::lvalue(target, mapping.as_ref());
            }
            let values_changed = rewrite::value_pack(&mut assign.values, mapping.as_ref());
            targets_changed || values_changed
        }
        HirStmt::TableSetList(set_list) => {
            let base_changed = rewrite::expr(&mut set_list.base, mapping.as_ref());
            let values_changed = rewrite::value_pack(&mut set_list.values, mapping.as_ref());
            base_changed || values_changed
        }
        HirStmt::ErrNil(err_nil) => rewrite::expr(&mut err_nil.value, mapping.as_ref()),
        HirStmt::ToBeClosed(to_be_closed) => {
            rewrite::expr(&mut to_be_closed.value, mapping.as_ref())
        }
        HirStmt::CallStmt(call_stmt) => rewrite::call_expr(&mut call_stmt.call, mapping.as_ref()),
        HirStmt::Return(ret) => rewrite::value_pack(&mut ret.values, mapping.as_ref()),
        HirStmt::If(if_stmt) => {
            let cond_changed = rewrite::expr(&mut if_stmt.cond, mapping.as_ref());
            let then_changed = promote_block(
                ctx,
                &mut if_stmt.then_block,
                mapping,
                sticky_slots,
                outer_uses_temp,
            )
            .changed;
            let else_changed = if_stmt.else_block.as_mut().is_some_and(|else_block| {
                promote_block(ctx, else_block, mapping, sticky_slots, outer_uses_temp).changed
            });
            cond_changed || then_changed || else_changed
        }
        HirStmt::While(while_stmt) => {
            let cond_changed = rewrite::expr(&mut while_stmt.cond, mapping.as_ref());
            // while 条件在每轮 body 之前重新读取；body 内的回边 alias 不能吞掉条件状态。
            let condition_temps = collect_temp_refs_in_expr(&while_stmt.cond);
            let body_changed = promote_block_with_protection(
                ctx,
                &mut while_stmt.body,
                mapping,
                sticky_slots,
                outer_uses_temp,
                &condition_temps,
                &condition_temps,
            )
            .changed;
            cond_changed || body_changed
        }
        HirStmt::Repeat(repeat_stmt) => {
            // `repeat ... until` 的条件和 loop body 共享同一个词法作用域。
            // body 里刚刚提升出来的 local 如果不继续带到条件里，条件就会继续挂着旧 temp，
            // 最后得到“body 已经是 l2，until 里还是 t3”这种半截 HIR。条件引用同时是
            // 更深子块的外部消费者，不能让嵌套 block 抢先声明同一个 temp。
            let condition_temps = collect_temp_refs_in_expr(&repeat_stmt.cond);
            let body_result = promote_block_with_protection(
                ctx,
                &mut repeat_stmt.body,
                mapping,
                sticky_slots,
                outer_uses_temp,
                &BTreeSet::new(),
                &condition_temps,
            );
            let cond_changed =
                rewrite::expr(&mut repeat_stmt.cond, body_result.trailing_mapping.as_ref());
            body_result.changed || cond_changed
        }
        HirStmt::NumericFor(numeric_for) => {
            let start_changed = rewrite::expr(&mut numeric_for.start, mapping.as_ref());
            let limit_changed = rewrite::expr(&mut numeric_for.limit, mapping.as_ref());
            let step_changed = rewrite::expr(&mut numeric_for.step, mapping.as_ref());
            let body_changed = promote_block(
                ctx,
                &mut numeric_for.body,
                mapping,
                sticky_slots,
                outer_uses_temp,
            )
            .changed;
            start_changed || limit_changed || step_changed || body_changed
        }
        HirStmt::GenericFor(generic_for) => {
            let iterator_changed = rewrite::value_pack(&mut generic_for.iterator, mapping.as_ref());
            let body_changed = promote_block(
                ctx,
                &mut generic_for.body,
                mapping,
                sticky_slots,
                outer_uses_temp,
            )
            .changed;
            iterator_changed || body_changed
        }
        HirStmt::Block(block) => {
            promote_block(ctx, block, mapping, sticky_slots, outer_uses_temp).changed
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

fn debug_scope_for_temp_group(
    temp_debug_scopes: &[Option<usize>],
    temps: &BTreeSet<TempId>,
) -> Option<usize> {
    let mut scopes = temps
        .iter()
        .filter_map(|temp| temp_debug_scopes.get(temp.index()).copied().flatten());
    let scope = scopes.next()?;
    scopes.all(|candidate| candidate == scope).then_some(scope)
}
