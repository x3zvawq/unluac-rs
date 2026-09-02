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
//! 不能在定义点提升成 `local`，否则前缀快照会读到尚未初始化的局部变量。首个 label/goto
//! 之前、不再跨边界存活的 GC-inert 只读链则不受回边影响，可以继续消除前缀版本噪音。
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

use super::label_refs::count_label_references;
use super::lexical_cfg::LexicalCfg;
use super::mention::{
    stmt_writes_temp, stmts_reference_captured_bindings, stmts_to_be_closed_temps,
    stmts_value_captured_bindings,
};
use super::root_lifetimes::{
    CallRootLifetimeIndices, LookupGcRootLifetimeIndices, collect_call_result_local_roots,
    collect_call_root_lifetimes, collect_lookup_gc_root_lifetimes,
};
use super::temp_touch::{
    TempRefScopeTracker, TempTouchIndex, collect_temp_reads_by_stmt, collect_temp_refs_by_stmt,
    collect_temp_refs_in_expr, expr_touches_any_temp, stmt_consumes_temps_only_in_control_head,
    stmt_contains_nested_nonlocal_control,
};
use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirInitializerMergeTransactionId, HirLValue, HirLocalDecl,
    HirProto, HirProtoRef, HirStmt, HirValuePack, LocalId, TempId,
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
    let mut new_local_debug_scopes = Vec::new();
    let mut physical_root_locals = BTreeSet::new();
    let mut promoted_bindings = Vec::new();
    let mut direct_seed_promotions = Vec::new();
    let mut debug_scope_locals = BTreeMap::new();
    let reference_captured_temps = stmts_reference_captured_bindings(&proto.body.stmts).temps;
    let mut identity_sensitive_temps = reference_captured_temps.clone();
    identity_sensitive_temps.extend(stmts_value_captured_bindings(&proto.body.stmts).temps);
    let to_be_closed_temps = stmts_to_be_closed_temps(&proto.body.stmts);
    let label_refs = count_label_references(&proto.body.stmts);
    identity_sensitive_temps.extend(to_be_closed_temps.iter().copied());
    let mut cell_sensitive_temps = reference_captured_temps;
    cell_sensitive_temps.extend(to_be_closed_temps.iter().copied());
    let result = {
        let mut ctx = PromotionCtx {
            proto_id: proto.id,
            facts,
            safety,
            temp_debug_locals: &proto.temp_debug_locals,
            temp_debug_scopes: &proto.temp_debug_scopes,
            next_local_index: &mut next_local_index,
            new_locals: &mut new_locals,
            new_local_debug_hints: &mut new_local_debug_hints,
            new_local_debug_scopes: &mut new_local_debug_scopes,
            physical_root_locals: &mut physical_root_locals,
            physical_root_temps: &proto.physical_root_temps,
            promoted_bindings: &mut promoted_bindings,
            direct_seed_promotions: &mut direct_seed_promotions,
            identity_sensitive_temps: &identity_sensitive_temps,
            cell_sensitive_temps: &cell_sensitive_temps,
            to_be_closed_temps: &to_be_closed_temps,
            label_refs: &label_refs,
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
    for (temp, local) in promoted_bindings.iter().copied() {
        // temp-inline 的负向语义结论属于 binding，而不是 TempId 的展示形式。promotion
        // 可能把多个 canonical temp 合并进同一个 local，因此按映射逐项取并集。
        proto.inline_dispositions.promote_temp_to_local(temp, local);
    }
    for (temp, local) in direct_seed_promotions {
        facts.record_direct_table_seed_promotion(temp, local);
    }
    for (temp, local) in promoted_bindings {
        facts.record_temp_to_local_merge(temp, local);
    }
    proto.locals.extend(new_locals);
    proto.local_debug_hints.extend(new_local_debug_hints);
    proto.local_debug_scopes.extend(new_local_debug_scopes);
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

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum MoveHomeRelation {
    SameExact,
    ProvenDistinct,
    MayDiffer,
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

struct MultiHomeCallRootHandoff {
    alias_index: usize,
    temp: TempId,
    home: HomeSlotKey,
    local: LocalId,
    values: HirValuePack,
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

/// 缺物理 home 时，只有无 alias 的单节点 ByValue capture 可以继续提升。
///
/// closure 在原求值点读取该 local 并立刻保存值快照，不会持续观察 cell；引用捕获与
/// TBC 则分别观察后续写入和 close owner，多节点组也可能把不同物理 epoch 合成一个 local。
fn identity_sensitive_group_requires_home(
    group: &BTreeSet<TempId>,
    identity_sensitive: &BTreeSet<TempId>,
    cell_sensitive: &BTreeSet<TempId>,
) -> bool {
    group.iter().any(|temp| identity_sensitive.contains(temp))
        && (group.len() != 1 || group.iter().any(|temp| cell_sensitive.contains(temp)))
}

fn capture_kind_allows_call_root_owner(
    temp: TempId,
    identity_sensitive: &BTreeSet<TempId>,
    cell_sensitive: &BTreeSet<TempId>,
    to_be_closed: &BTreeSet<TempId>,
) -> bool {
    !to_be_closed.contains(&temp)
        && (!identity_sensitive.contains(&temp) || cell_sensitive.contains(&temp))
}

struct PromotionCtx<'a> {
    proto_id: HirProtoRef,
    facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
    temp_debug_locals: &'a [Option<String>],
    temp_debug_scopes: &'a [Option<usize>],
    next_local_index: &'a mut usize,
    new_locals: &'a mut Vec<LocalId>,
    new_local_debug_hints: &'a mut Vec<Option<String>>,
    new_local_debug_scopes: &'a mut Vec<Option<usize>>,
    physical_root_locals: &'a mut BTreeSet<LocalId>,
    physical_root_temps: &'a BTreeSet<TempId>,
    promoted_bindings: &'a mut Vec<(TempId, LocalId)>,
    direct_seed_promotions: &'a mut Vec<(TempId, LocalId)>,
    identity_sensitive_temps: &'a BTreeSet<TempId>,
    cell_sensitive_temps: &'a BTreeSet<TempId>,
    to_be_closed_temps: &'a BTreeSet<TempId>,
    label_refs: &'a BTreeMap<crate::hir::common::HirLabelId, usize>,
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
    new_local_debug_scopes: &'a mut Vec<Option<usize>>,
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
        self.new_local_debug_scopes
            .push(debug_scope_for_temp_group(self.temp_debug_scopes, &temps));
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
        self.new_local_debug_scopes.push(
            self.temp_debug_scopes
                .get(temp.index())
                .copied()
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
    let empty = BTreeSet::new();
    promote_block_with_protection(
        ctx,
        block,
        inherited,
        inherited_sticky_slots,
        outer_uses_temp,
        BlockProtection {
            current_plan_temps: &empty,
            descendant_temps: &empty,
            trailing_root_condition: None,
        },
    )
}

struct BlockProtection<'a> {
    current_plan_temps: &'a BTreeSet<TempId>,
    descendant_temps: &'a BTreeSet<TempId>,
    trailing_root_condition: Option<&'a HirExpr>,
}

fn promote_block_with_protection(
    ctx: &mut PromotionCtx<'_>,
    block: &mut HirBlock,
    inherited: &LocalMapping,
    inherited_sticky_slots: &BTreeMap<HomeSlotKey, LocalId>,
    outer_uses_temp: &dyn Fn(TempId) -> bool,
    protection: BlockProtection<'_>,
) -> PromotionResult {
    ctx.physical_root_locals
        .extend(collect_call_result_local_roots(
            &block.stmts,
            protection.trailing_root_condition,
            ctx.safety,
        ));

    // 每轮控制头等 block 外消费者先保护当前 block；递归进入子作用域时再叠加当前语句
    // 之后的引用。tracker 用引用计数维护后缀集合，避免按 index 克隆完整集合。
    let stmt_temp_refs = collect_temp_refs_by_stmt(&block.stmts);
    let mut temp_refs = TempRefScopeTracker::new(&stmt_temp_refs);

    let block_uses_outer_temp =
        |temp| outer_uses_temp(temp) || protection.current_plan_temps.contains(&temp);
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
        let mut batched_decl_output_index = None;
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
                batched_decl_output_index = Some(rewritten.len());
                rewritten.push(HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: plans
                        .iter()
                        .filter(|plan| plan.batch_empty_decl)
                        .map(|plan| plan.local)
                        .collect(),
                    values: HirValuePack::fixed(Vec::new()),
                    initializer_merge_transaction: None,
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
                || protection.descendant_temps.contains(&temp)
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
        if let Some(decl_index) = batched_decl_output_index {
            let HirStmt::LocalDecl(local_decl) = &mut rewritten[decl_index] else {
                unreachable!("batched declaration output must remain a local declaration");
            };
            certify_batched_initializer_merge_transaction(ctx.proto_id, local_decl, &mut stmt);
        }
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

fn certify_batched_initializer_merge_transaction(
    proto_id: HirProtoRef,
    local_decl: &mut HirLocalDecl,
    stmt: &mut HirStmt,
) {
    let HirStmt::Assign(assign) = stmt else {
        return;
    };
    if local_decl.bindings.len() < 2
        || local_decl.bindings.len() != assign.targets.len()
        || !local_decl
            .bindings
            .iter()
            .zip(&assign.targets)
            .all(|(binding, target)| matches!(target, HirLValue::Local(local) if local == binding))
        || !assign.values.fixed.is_empty()
        || !matches!(
            assign.values.tail.as_ref(),
            Some(tail)
                if tail.exact_width() == Some(local_decl.bindings.len())
                    && matches!(tail.as_expr(), HirExpr::Call(_))
        )
    {
        return;
    }

    // batch declaration 的首个 local 是本 proto 中刚分配且不会复用的身份；只把它用作
    // opaque transaction token 的唯一序号，不把 LocalId 本身暴露成 rewrite authority。
    let token = HirInitializerMergeTransactionId::new(proto_id, local_decl.bindings[0].index());
    local_decl.initializer_merge_transaction = Some(token);
    assign.initializer_merge_transaction = Some(token);
}

fn collect_plans(
    ctx: &mut PromotionCtx<'_>,
    block: &HirBlock,
    stmt_temp_refs: &[BTreeSet<TempId>],
    inherited: &BTreeMap<TempId, LocalId>,
    inherited_sticky_slots: &BTreeMap<HomeSlotKey, LocalId>,
    outer_uses_temp: &dyn Fn(TempId) -> bool,
) -> Vec<PromotionPlan> {
    let label_flow_boundary = block
        .stmts
        .iter()
        .position(stmt_contains_nested_nonlocal_control);
    let linear_prefix_end = label_flow_boundary.unwrap_or(block.stmts.len());
    let lifetime_stmts = &block.stmts[..linear_prefix_end];
    let label_cfg = LexicalCfg::analyze(&block.stmts, ctx.label_refs, ctx.safety).ok();
    let has_label_flow =
        label_cfg.as_ref().is_some_and(LexicalCfg::has_label_flow) || label_flow_boundary.is_some();

    let facts = ctx.facts;
    let temp_debug_locals = ctx.temp_debug_locals;
    let temp_debug_scopes = ctx.temp_debug_scopes;
    let stmt_temp_reads = collect_temp_reads_by_stmt(&block.stmts);
    let mut plans = Vec::new();
    let temp_touches = TempTouchIndex::new(stmt_temp_refs);
    let call_root_lifetimes = collect_call_root_lifetimes(
        lifetime_stmts,
        facts,
        ctx.safety,
        true,
        |temp| {
            // 候选拒绝[SemanticBarrier:Resource]：TBC producer 若提前声明 owner，会改变 close 起点与被关闭的值。
            // 候选接受：call-root collector 只认 trusted exact `(slot, close epoch)`；ByReference
            // capture 因而绑定同一 cell，后续 exact-home overwrite 继续复用该 owner。
            // 候选拒绝[SemanticBarrier:Capture]：Luau ByValue capture 是 VM 值快照；若匿名
            // root local 后续按同槽复用，源码 closure 会改为观察 replacement（regress_219）。
            // 候选拒绝[PolicyBoundary]：debug temp 的源码身份不由匿名 physical-root owner 取代。
            capture_kind_allows_call_root_owner(
                temp,
                ctx.identity_sensitive_temps,
                ctx.cell_sensitive_temps,
                ctx.to_be_closed_temps,
            ) && temp_debug_locals
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
        collect_lookup_gc_root_lifetimes(lifetime_stmts, facts, ctx.safety, |temp| {
            !ctx.identity_sensitive_temps.contains(&temp)
                && !inherited.contains_key(&temp)
                && !outer_uses_temp(temp)
                && temp_debug_locals
                    .get(temp.index())
                    .is_none_or(Option::is_none)
        });
    let label_flow_proof = LabelFlowGroupProof {
        block,
        linear_prefix_end,
        cfg: label_cfg.as_ref(),
        facts,
        call_roots: &call_root_lifetimes,
        lookup_roots: &lookup_gc_root_lifetimes,
        safety: ctx.safety,
    };
    let mut reserved_temps = BTreeSet::new();
    let mut reserved_alias_indices = BTreeSet::new();
    let mut slot_candidates = inherited_sticky_slots.clone();
    let mut sticky_slots = inherited_sticky_slots.clone();
    let mut physical_root_locals_by_home = BTreeMap::<(usize, HomeSlotKey), LocalId>::new();
    for (decl_index, stmt) in block.stmts.iter().enumerate() {
        if reserved_alias_indices.contains(&decl_index) {
            activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);
            continue;
        }

        activate_captured_slots_in_stmt(stmt, facts, &slot_candidates, &mut sticky_slots);

        if let Some(root_temp) = simple_temp_assign_target(stmt)
            && let Some(handoffs) = multi_home_call_root_handoffs(
                block,
                decl_index,
                root_temp,
                facts,
                &call_root_lifetimes,
                &physical_root_locals_by_home,
            )
        {
            // 一个 call 后的连续 MOVE 共同结束多个旧 root home。先完整匹配所有 pair、
            // old owner 与 HIR copy，再一次登记 plans；不能只复用任意一个 home，或在
            // 半数匹配后提交，否则会把同一个 VM overwrite transaction 拆开。
            for handoff in handoffs {
                let mut allocator = PlanAllocator {
                    temp_debug_locals,
                    temp_debug_scopes,
                    plans: &mut plans,
                    reserved_temps: &mut reserved_temps,
                    reserved_alias_indices: &mut reserved_alias_indices,
                    next_local_index: ctx.next_local_index,
                    new_locals: ctx.new_locals,
                    new_local_debug_hints: ctx.new_local_debug_hints,
                    new_local_debug_scopes: ctx.new_local_debug_scopes,
                    promoted_bindings: ctx.promoted_bindings,
                    direct_seed_promotions: ctx.direct_seed_promotions,
                    debug_scope_locals: ctx.debug_scope_locals,
                };
                allocator.reuse_existing_local(
                    handoff.alias_index,
                    handoff.local,
                    Some(handoff.home),
                    BTreeSet::from([handoff.temp]),
                    BTreeSet::new(),
                    PromotionInit::FromAssign(handoff.values),
                );
            }
        }

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
                new_local_debug_scopes: ctx.new_local_debug_scopes,
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
                new_local_debug_scopes: ctx.new_local_debug_scopes,
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
            // 候选拒绝[SemanticBarrier:ValueFlow]：backedge/goto 可让文本前方读取同一
            // TempId 的入口或上一轮值；在此定义点新建 local 会把该读取切到未初始化 binding。
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
        let promotion_group = collect_promotion_group(
            block,
            decl_index,
            root_temp,
            facts,
            &is_reserved,
            &temp_touches,
        );

        if has_label_flow {
            match label_flow_proof.group_safety(decl_index, root_temp, &promotion_group) {
                Ok(()) => {}
                Err(LabelFlowGroupFailure::ControlFlow) => {
                    // 候选拒绝[SemanticBarrier:Scope]：若入口 goto 绕过 temp 定义抵达后缀
                    // label，新声明会令该入口跳入 local scope，且后续读取观察未初始化值。
                    continue;
                }
                Err(LabelFlowGroupFailure::Lifetime) => {
                    // 候选拒绝[SemanticBarrier:Lifetime]：label island 前最后一个 GC-bearing
                    // temp 值若没有同 home 的已配对覆盖，提升后的 lexical local 会把它保活到
                    // block 末尾；后续显式 GC/弱引用可观察原 VM root 已被覆盖的差异。
                    continue;
                }
            }
        }
        let PromotionGroup {
            temps: group,
            removable_aliases,
            touching_stmt_indices,
        } = promotion_group;
        let group_has_physical_root = group
            .iter()
            .any(|temp| ctx.physical_root_temps.contains(temp));
        // 别名扩张后的任一 temp 仍被外层读取时，整个组都不能在子作用域提升；
        // 只检查 root 会让内层 local 吞掉外层 loop state 的别名。
        if group.iter().copied().any(outer_uses_temp) {
            // 候选拒绝[SemanticBarrier:Scope]：`while c do t = next end; return t` 若在循环体声明 t 的替代 local，循环外仍会读取未写回的旧 binding。
            continue;
        }

        let home_slot = trusted_home_slot_for_group(&group, facts);
        if home_slot.is_none()
            && identity_sensitive_group_requires_home(
                &group,
                ctx.identity_sensitive_temps,
                ctx.cell_sensitive_temps,
            )
        {
            // 候选拒绝[SemanticBarrier:Capture]：`f` 引用捕获 t0、move 后 `g` 捕获 t1、再覆盖 t0 时，缺同一 trusted home 却合并会让 f/g 错误共享 cell；
            // 候选拒绝[SemanticBarrier:Resource]：TBC 跨同样的不可信合并会更换 close owner。
            // 单节点 ByValue capture 已按快照点放行；多节点组仍可能合并异槽 value epoch。
            continue;
        }
        let sticky_local = home_slot.and_then(|slot| sticky_slots.get(&slot).copied());
        let debug_local = home_slot.and_then(|slot| {
            debug_scope_for_temp_group(temp_debug_scopes, &group)
                .and_then(|scope| ctx.debug_scope_locals.get(&(slot, scope)).copied())
        });
        let preceding_lookup_root = home_slot
            .and_then(|home| lookup_gc_root_lifetimes.overwrite_pair_for_home(decl_index, home))
            .map(|pair| (pair.root_index(), pair.home()));
        let preceding_call_root = home_slot
            .and_then(|home| call_root_lifetimes.overwrite_pair_for_home(decl_index, home))
            .or_else(|| call_root_lifetimes.unambiguous_overwrite_pair(decl_index))
            .map(|pair| (pair.root_index(), pair.home()));
        let preceding_physical_root = preceding_call_root.or(preceding_lookup_root).or_else(|| {
            call_root_lifetimes
                .root_for_protected(decl_index)
                .zip(home_slot)
        });
        let preceding_physical_root_local =
            preceding_physical_root.and_then(|(root, root_home)| {
                physical_root_locals_by_home
                    .get(&(root, root_home))
                    .copied()
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
            // 零后续 touch 的匿名 temp 没有跨语句值流，不是
            // locals 的源码 binding 候选。dead-temps 只会另行删除其中 discard-safe、无受保护
            // raw-home 的子集；其余形状不能借一个并不覆盖它们的 owner 伪装成 LayerBoundary。
            continue;
        }
        if sticky_local.is_none()
            && !force_physical_root_local
            && debug_hint_for_temp_group(temp_debug_locals, &group).is_none()
            && std::iter::once(decl_index)
                .chain(touching_stmt_indices.iter().copied())
                .all(|index| stmt_temp_reads[index].is_disjoint(&group))
        {
            // 只有写 touch、没有表达式读取的链不承载可恢复的
            // 跨语句 binding。dead-temps 仍按自己的 discard-safe/raw-home 合同清理可删写入；
            // locals 不把未被读取的 SSA 版本固化成源码 local。
            continue;
        }
        if sticky_local.is_none() && !force_physical_root_local {
            let first_touch_index = touching_stmt_indices.first().copied();
            // 只在控制头里单次消费的 temp，更像机械性的结构参数而不是源码级 local。
            // 只有一次后续消费的全局别名或字符串常量，必须结合消费站点判定：
            // 全局别名只有作为表字段安装的 base，字符串常量只有作为调用实参，
            // 才更像寄存器级脚手架而不是源码 local。数字/布尔/nil 等也可能是
            // 捕获 local 的重绑定值，仍按原规则保守提升。
            if touching_stmt_indices.len() == 1 {
                let use_stmt = &block.stmts[first_touch_index.expect("single touch must exist")];
                if stmt_consumes_temps_only_in_control_head(use_stmt, &group) {
                    // 候选拒绝[PolicyBoundary]：只在控制头消费一次的匿名 temp 保持低密度展示；这不是运行语义边界。
                    continue;
                }
                if single_use_seed_can_stay_temp(stmt, root_temp, use_stmt) {
                    // 候选拒绝[LayerBoundary]：global table-base 与 string call-arg 分别属于
                    // temp-inline 的 AccessBase / CallArg 站点。该 Normal owner 在 locals 之前
                    // 已执行具体求值顺序、lifetime 与展示策略 gate；locals 不把其拒绝结果改成
                    // 一个更长寿的 local。成功内联产生 TempChain/LocalBinding invalidation 后，
                    // table-constructors 才可能消费随之暴露的表构造形状。
                    continue;
                }
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
            new_local_debug_scopes: ctx.new_local_debug_scopes,
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
        let collected_root =
            call_root_lifetimes.is_root(decl_index) || lookup_gc_root_lifetimes.is_root(decl_index);
        if (collected_root || group_has_physical_root)
            && let Some(home) = home_slot
        {
            // Root ownership is keyed by both producer epoch and physical home. A value may be
            // copied through several homes; indexing only by its producer would let a later
            // endpoint reuse an unrelated local and collapse callee/argument identities.
            physical_root_locals_by_home.insert((decl_index, home), selected_local);
        }
        if collected_root || (group_has_physical_root && home_slot.is_some()) {
            // This local must stay dedicated to the root result until its proven physical
            // overwrite partner reuses it. Home-slot compaction may otherwise lend the same
            // source local to a simultaneously-live value before that overwrite occurs.
            slot_candidates.retain(|_, candidate| *candidate != selected_local);
        }
    }

    // The AST cleanup pass cannot infer physical-slot lifetime from ordinary binding mentions.
    // Carry the proven root identity across the HIR -> AST boundary explicitly.
    ctx.physical_root_locals
        .extend(physical_root_locals_by_home.values().copied());

    let mut sticky_slots = inherited_sticky_slots.clone();
    for (decl_index, stmt) in block.stmts[..linear_prefix_end].iter().enumerate() {
        let is_reserved = |temp| inherited.contains_key(&temp) || reserved_temps.contains(&temp);
        let mut merge_temps = branch_merge::candidate_temps(
            &block.stmts,
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
            if home_slot.is_none()
                && identity_sensitive_group_requires_home(
                    &BTreeSet::from([temp]),
                    ctx.identity_sensitive_temps,
                    ctx.cell_sensitive_temps,
                )
            {
                // 候选拒绝[SemanticBarrier:Capture]：引用捕获持续观察原 cell，缺 trusted home 时不能把 branch result 改成新 local。
                // 候选拒绝[SemanticBarrier:Resource]：TBC 需要精确 close owner；按值 capture 只在 closure 点保存单次快照，已由单节点分支放行。
                continue;
            }
            let preceding_lookup_root = home_slot
                .and_then(|home| lookup_gc_root_lifetimes.overwrite_pair_for_home(decl_index, home))
                .map(|pair| (pair.root_index(), pair.home()));
            let preceding_call_root = home_slot
                .and_then(|home| call_root_lifetimes.overwrite_pair_for_home(decl_index, home))
                .or_else(|| call_root_lifetimes.unambiguous_overwrite_pair(decl_index))
                .map(|pair| (pair.root_index(), pair.home()));
            let preceding_physical_root_local = preceding_call_root
                .or(preceding_lookup_root)
                .and_then(|(root, root_home)| {
                    physical_root_locals_by_home
                        .get(&(root, root_home))
                        .copied()
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
                new_local_debug_scopes: ctx.new_local_debug_scopes,
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
            // 已认领或已在组内的 alias 不再形成新候选。
            // 候选拒绝[SemanticBarrier:ValueFlow]：`next=f(carried); carried=next` 中 alias 在 root 定义前已被读取；删除写回会让下一轮继续读取入口 seed。
            !is_reserved(*alias_temp)
                && !temps.contains(alias_temp)
                && match move_home_relation(root_temp, *alias_temp, facts) {
                    MoveHomeRelation::SameExact => true,
                    MoveHomeRelation::ProvenDistinct => {
                        // 候选拒绝[SemanticBarrier:Lifetime]：完整 possible-home 集合已证明
                        // MOVE 两端异槽；它是值快照与两个独立 GC root，不能合并 cell。
                        false
                    }
                    MoveHomeRelation::MayDiffer => {
                        // 候选拒绝[SemanticBarrier:ValueFlow]：root/alias 的多槽集合即使相交，
                        // 仍可在两条路径上分别取 `(slot0,slot1)` 与 `(slot1,slot0)`；合并会把
                        // 原本独立快照改成同一 local。缺集合时也包含该异槽反例。
                        false
                    }
                }
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

fn move_home_relation(
    root: TempId,
    alias: TempId,
    facts: &ProtoPromotionFacts,
) -> MoveHomeRelation {
    if let (Some(root), Some(alias)) = (
        facts.trusted_temp_home_slot(root),
        facts.trusted_temp_home_slot(alias),
    ) {
        return if root == alias {
            MoveHomeRelation::SameExact
        } else {
            MoveHomeRelation::ProvenDistinct
        };
    }
    match (
        facts.possible_temp_home_slots(root),
        facts.possible_temp_home_slots(alias),
    ) {
        (Some(root), Some(alias)) if root.len() == 1 && root == alias => {
            MoveHomeRelation::SameExact
        }
        (Some(root), Some(alias))
            if !root.is_empty() && !alias.is_empty() && root.is_disjoint(&alias) =>
        {
            MoveHomeRelation::ProvenDistinct
        }
        _ => MoveHomeRelation::MayDiffer,
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum LabelFlowGroupFailure {
    ControlFlow,
    Lifetime,
}

struct LabelFlowGroupProof<'a> {
    block: &'a HirBlock,
    linear_prefix_end: usize,
    cfg: Option<&'a LexicalCfg>,
    facts: &'a ProtoPromotionFacts,
    call_roots: &'a CallRootLifetimeIndices,
    lookup_roots: &'a LookupGcRootLifetimeIndices,
    safety: HirExprSafety,
}

impl LabelFlowGroupProof<'_> {
    fn group_safety(
        &self,
        decl_index: usize,
        root_temp: TempId,
        group: &PromotionGroup,
    ) -> Result<(), LabelFlowGroupFailure> {
        let Some(cfg) = self.cfg else {
            return Err(LabelFlowGroupFailure::ControlFlow);
        };
        if !cfg.statement_dominates_suffix(decl_index) {
            return Err(LabelFlowGroupFailure::ControlFlow);
        }
        let Some(value) = single_temp_assign_value(&self.block.stmts[decl_index], root_temp) else {
            return Err(LabelFlowGroupFailure::ControlFlow);
        };
        let exact_home = trusted_home_slot_for_group(&group.temps, self.facts);
        if !self.safety.result_is_gc_inert(value) {
            let Some(home) = exact_home else {
                return Err(LabelFlowGroupFailure::Lifetime);
            };
            if !root_lifetime_closes_in_prefix(
                decl_index,
                home,
                self.linear_prefix_end,
                self.call_roots,
                self.lookup_roots,
            ) {
                return Err(LabelFlowGroupFailure::Lifetime);
            }
        }
        for &index in &group.touching_stmt_indices {
            let stmt = &self.block.stmts[index];
            if group
                .temps
                .iter()
                .all(|temp| !stmt_writes_temp(stmt, *temp))
                || group_writes_are_gc_inert(stmt, &group.temps, self.safety)
            {
                continue;
            }
            let Some(home) = exact_home else {
                return Err(LabelFlowGroupFailure::Lifetime);
            };
            if index >= self.linear_prefix_end
                || !root_lifetime_closes_in_prefix(
                    index,
                    home,
                    self.linear_prefix_end,
                    self.call_roots,
                    self.lookup_roots,
                )
            {
                return Err(LabelFlowGroupFailure::Lifetime);
            }
        }
        Ok(())
    }
}

fn group_writes_are_gc_inert(
    stmt: &HirStmt,
    group: &BTreeSet<TempId>,
    safety: HirExprSafety,
) -> bool {
    match stmt {
        HirStmt::Assign(assign) => {
            let writes_group = assign
                .targets
                .iter()
                .any(|target| matches!(target, HirLValue::Temp(temp) if group.contains(temp)));
            !writes_group
                || matches!(
                    (assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
                    ([HirLValue::Temp(target)], [value], None)
                        if group.contains(target) && safety.result_is_gc_inert(value)
                )
        }
        HirStmt::If(if_stmt) => {
            if_stmt
                .then_block
                .stmts
                .iter()
                .all(|stmt| group_writes_are_gc_inert(stmt, group, safety))
                && if_stmt.else_block.as_ref().is_none_or(|block| {
                    block
                        .stmts
                        .iter()
                        .all(|stmt| group_writes_are_gc_inert(stmt, group, safety))
                })
        }
        HirStmt::While(while_stmt) => while_stmt
            .body
            .stmts
            .iter()
            .all(|stmt| group_writes_are_gc_inert(stmt, group, safety)),
        HirStmt::Repeat(repeat_stmt) => repeat_stmt
            .body
            .stmts
            .iter()
            .all(|stmt| group_writes_are_gc_inert(stmt, group, safety)),
        HirStmt::NumericFor(numeric_for) => numeric_for
            .body
            .stmts
            .iter()
            .all(|stmt| group_writes_are_gc_inert(stmt, group, safety)),
        HirStmt::GenericFor(generic_for) => generic_for
            .body
            .stmts
            .iter()
            .all(|stmt| group_writes_are_gc_inert(stmt, group, safety)),
        HirStmt::Block(block) => block
            .stmts
            .iter()
            .all(|stmt| group_writes_are_gc_inert(stmt, group, safety)),
        HirStmt::LocalDecl(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => true,
    }
}

fn root_lifetime_closes_in_prefix(
    root_index: usize,
    home: HomeSlotKey,
    linear_prefix_end: usize,
    call_roots: &CallRootLifetimeIndices,
    lookup_roots: &LookupGcRootLifetimeIndices,
) -> bool {
    (root_index + 1..linear_prefix_end).any(|overwrite_index| {
        call_roots
            .overwrite_pairs(overwrite_index)
            .any(|pair| pair.root_index() == root_index && pair.home() == home)
            || lookup_roots
                .overwrite_pairs(overwrite_index)
                .any(|pair| pair.root_index() == root_index && pair.home() == home)
    })
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
            let mut temps = scalar_temp_assign_targets_for_home(&if_stmt.then_block, facts, home);
            temps.extend(scalar_temp_assign_targets_for_home(else_block, facts, home));
            temps
        }
        HirStmt::Block(block) => scalar_temp_assign_targets_for_home(block, facts, home),
        _ => return None,
    };
    (!temps.is_empty()).then_some(temps)
}

fn multi_home_call_root_handoffs(
    block: &HirBlock,
    root_index: usize,
    root_temp: TempId,
    facts: &ProtoPromotionFacts,
    call_roots: &CallRootLifetimeIndices,
    physical_root_locals_by_home: &BTreeMap<(usize, HomeSlotKey), LocalId>,
) -> Option<Vec<MultiHomeCallRootHandoff>> {
    let pairs = call_roots.overwrite_pairs(root_index).collect::<Vec<_>>();
    if pairs.len() <= 1 {
        return None;
    }

    let mut pending = BTreeMap::new();
    for pair in pairs {
        let local = physical_root_locals_by_home
            .get(&(pair.root_index(), pair.home()))
            .copied()?;
        if pending.insert(pair.home(), local).is_some() {
            return None;
        }
    }

    let immediate_move_homes = facts.trusted_immediate_move_write_homes(root_temp)?;
    let mut seen_homes = BTreeSet::new();
    let mut handoffs = Vec::with_capacity(pending.len());
    for alias_index in root_index + 1..=root_index.checked_add(immediate_move_homes.len())? {
        let HirStmt::Assign(assign) = block.stmts.get(alias_index)? else {
            return None;
        };
        let ([HirLValue::Temp(temp)], [HirExpr::TempRef(source)], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) else {
            return None;
        };
        if *source != root_temp {
            return None;
        }
        let home = facts.trusted_temp_home_slot(*temp)?;
        if !immediate_move_homes.contains(&home) || !seen_homes.insert(home) {
            return None;
        }
        if let Some(local) = pending.remove(&home) {
            handoffs.push(MultiHomeCallRootHandoff {
                alias_index,
                temp: *temp,
                home,
                local,
                values: assign.values.clone(),
            });
        }
    }

    pending.is_empty().then_some(handoffs)
}

fn scalar_temp_assign_targets_for_home(
    block: &HirBlock,
    facts: &ProtoPromotionFacts,
    home: HomeSlotKey,
) -> BTreeSet<TempId> {
    block
        .stmts
        .iter()
        .filter_map(|stmt| {
            let HirStmt::Assign(assign) = stmt else {
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
        })
        .collect()
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
            initializer_merge_transaction: None,
        }))),
        (PromotionAction::ReuseExistingLocal, PromotionInit::FromAssign(_)) => {
            Some(HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(plan.local)],
                values,
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
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
            if targets_changed {
                assign.generic_for_initializer_producer = None;
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
                BlockProtection {
                    current_plan_temps: &condition_temps,
                    descendant_temps: &condition_temps,
                    trailing_root_condition: None,
                },
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
                BlockProtection {
                    current_plan_temps: &BTreeSet::new(),
                    descendant_temps: &condition_temps,
                    trailing_root_condition: Some(&repeat_stmt.cond),
                },
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
            if iterator_changed {
                generic_for.initializer_transaction = None;
            }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::DecompileDialect;
    use crate::hir::common::{
        HirCallExpr, HirCallStmt, HirGlobalRef, HirGoto, HirIf, HirLabel, HirLabelId, HirPackTail,
    };

    fn assign(target: TempId, value: HirExpr) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(target)],
            values: HirValuePack::fixed(vec![value]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }))
    }

    fn goto(target: HirLabelId) -> HirStmt {
        HirStmt::Goto(Box::new(HirGoto { target }))
    }

    fn label(id: HirLabelId) -> HirStmt {
        HirStmt::Label(Box::new(HirLabel {
            id,
            tbc_barriers: Vec::new(),
        }))
    }

    fn call(name: &str) -> HirExpr {
        HirExpr::Call(Box::new(HirCallExpr {
            callee: HirExpr::GlobalRef(HirGlobalRef { key: name.into() }),
            args: HirValuePack::default(),
            method: false,
            fastcall: None,
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
        }))
    }

    #[test]
    fn only_single_value_capture_can_promote_without_a_home() {
        let first = TempId(0);
        let second = TempId(1);
        let value_captured = BTreeSet::from([first]);

        assert!(!identity_sensitive_group_requires_home(
            &BTreeSet::from([first]),
            &value_captured,
            &BTreeSet::new(),
        ));
        assert!(identity_sensitive_group_requires_home(
            &BTreeSet::from([first]),
            &value_captured,
            &BTreeSet::from([first]),
        ));
        assert!(identity_sensitive_group_requires_home(
            &BTreeSet::from([first, second]),
            &value_captured,
            &BTreeSet::new(),
        ));

        let mut dispositions = crate::hir::common::HirInlineDispositions::default();
        assert!(dispositions.preserve_temp(
            first,
            crate::hir::common::HirInlineRetentionReason::CapturedValueEpoch,
        ));
        assert!(!dispositions.preserve_temp(
            first,
            crate::hir::common::HirInlineRetentionReason::CapturedValueEpoch,
        ));
        dispositions.promote_temp_to_local(first, LocalId(0));
        dispositions.promote_temp_to_local(second, LocalId(0));
        assert_eq!(
            dispositions.local(LocalId(0)),
            crate::hir::common::HirInlineDisposition::Preserve(BTreeSet::from([
                crate::hir::common::HirInlineRetentionReason::CapturedValueEpoch,
            ]))
        );
    }

    #[test]
    fn call_root_owner_accepts_reference_capture_but_not_value_snapshot_or_tbc() {
        let reference = TempId(0);
        let value = TempId(1);
        let tbc = TempId(2);
        let identity_sensitive = BTreeSet::from([reference, value, tbc]);
        let cell_sensitive = BTreeSet::from([reference, tbc]);
        let to_be_closed = BTreeSet::from([tbc]);

        assert!(capture_kind_allows_call_root_owner(
            reference,
            &identity_sensitive,
            &cell_sensitive,
            &to_be_closed,
        ));
        assert!(!capture_kind_allows_call_root_owner(
            value,
            &identity_sensitive,
            &cell_sensitive,
            &to_be_closed,
        ));
        assert!(!capture_kind_allows_call_root_owner(
            tbc,
            &identity_sensitive,
            &cell_sensitive,
            &to_be_closed,
        ));
    }

    #[test]
    fn move_home_relation_accepts_only_one_shared_possible_home() {
        let exact_root = TempId(0);
        let exact_alias = TempId(1);
        let disjoint_alias = TempId(2);
        let overlapping_alias = TempId(3);
        let invalidated_single_alias = TempId(4);
        let root_home = HomeSlotKey::new(0, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(exact_root, root_home);
        facts.record_temp_home_slot_for_test(exact_alias, root_home);
        facts.record_temp_home_slot_for_test(disjoint_alias, HomeSlotKey::new(1, 0));
        facts.record_temp_home_merge(
            disjoint_alias,
            Some(BTreeSet::from([HomeSlotKey::new(2, 0)])),
        );
        facts.record_temp_home_slot_for_test(overlapping_alias, HomeSlotKey::new(3, 0));
        facts.record_temp_home_merge(overlapping_alias, Some(BTreeSet::from([root_home])));
        facts.record_temp_home_slot_for_test(invalidated_single_alias, root_home);
        facts.record_temp_home_merge(invalidated_single_alias, Some(BTreeSet::new()));

        assert_eq!(
            move_home_relation(exact_root, exact_alias, &facts),
            MoveHomeRelation::SameExact
        );
        assert_eq!(
            move_home_relation(exact_root, disjoint_alias, &facts),
            MoveHomeRelation::ProvenDistinct
        );
        assert_eq!(
            move_home_relation(exact_root, overlapping_alias, &facts),
            MoveHomeRelation::MayDiffer
        );
        assert_eq!(
            move_home_relation(exact_root, invalidated_single_alias, &facts),
            MoveHomeRelation::SameExact
        );
        assert_eq!(
            move_home_relation(exact_root, TempId(5), &facts),
            MoveHomeRelation::MayDiffer
        );
    }

    #[test]
    fn label_flow_accepts_dominated_structured_gc_inert_writes() {
        let temp = TempId(0);
        let sink = TempId(1);
        let target = HirLabelId(0);
        let group = PromotionGroup {
            temps: BTreeSet::from([temp]),
            removable_aliases: BTreeSet::new(),
            touching_stmt_indices: BTreeSet::from([1, 4]),
        };
        let safety = HirExprSafety::for_dialect(DecompileDialect::Lua54);
        let inert = HirBlock {
            stmts: vec![
                assign(temp, HirExpr::Integer(1)),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::ParamRef(crate::hir::common::ParamId(0)),
                    then_block: HirBlock {
                        stmts: vec![assign(temp, HirExpr::Integer(2))],
                    },
                    else_block: None,
                })),
                goto(target),
                assign(sink, HirExpr::Integer(0)),
                label(target),
                assign(sink, HirExpr::TempRef(temp)),
            ],
        };
        let owner_refs = count_label_references(&inert.stmts);
        let inert_cfg = LexicalCfg::analyze(&inert.stmts, &owner_refs, safety).unwrap();
        let call_roots = CallRootLifetimeIndices::default();
        let lookup_roots = LookupGcRootLifetimeIndices::default();
        let facts = ProtoPromotionFacts::default();
        let proof = LabelFlowGroupProof {
            block: &inert,
            linear_prefix_end: 2,
            cfg: Some(&inert_cfg),
            facts: &facts,
            call_roots: &call_roots,
            lookup_roots: &lookup_roots,
            safety,
        };

        assert_eq!(proof.group_safety(0, temp, &group), Ok(()));
    }

    #[test]
    fn label_flow_rejects_bypassed_declaration_and_unclosed_gc_value() {
        let temp = TempId(0);
        let resource = TempId(1);
        let sink = TempId(2);
        let target = HirLabelId(0);
        let safety = HirExprSafety::for_dialect(DecompileDialect::Lua54);
        let bypassed = HirBlock {
            stmts: vec![
                goto(target),
                assign(temp, HirExpr::Integer(1)),
                label(target),
                assign(sink, HirExpr::TempRef(temp)),
            ],
        };
        let bypassed_group = PromotionGroup {
            temps: BTreeSet::from([temp]),
            removable_aliases: BTreeSet::new(),
            touching_stmt_indices: BTreeSet::from([3]),
        };
        let bypassed_refs = count_label_references(&bypassed.stmts);
        let bypassed_cfg = LexicalCfg::analyze(&bypassed.stmts, &bypassed_refs, safety).unwrap();
        let call_roots = CallRootLifetimeIndices::default();
        let lookup_roots = LookupGcRootLifetimeIndices::default();
        let facts = ProtoPromotionFacts::default();
        let bypassed_proof = LabelFlowGroupProof {
            block: &bypassed,
            linear_prefix_end: 0,
            cfg: Some(&bypassed_cfg),
            facts: &facts,
            call_roots: &call_roots,
            lookup_roots: &lookup_roots,
            safety,
        };
        assert_eq!(
            bypassed_proof.group_safety(1, temp, &bypassed_group),
            Err(LabelFlowGroupFailure::ControlFlow)
        );

        let unclosed = HirBlock {
            stmts: vec![
                assign(temp, HirExpr::TempRef(resource)),
                goto(target),
                label(target),
                assign(sink, HirExpr::TempRef(temp)),
            ],
        };
        let unclosed_group = PromotionGroup {
            temps: BTreeSet::from([temp]),
            removable_aliases: BTreeSet::new(),
            touching_stmt_indices: BTreeSet::from([3]),
        };
        let unclosed_refs = count_label_references(&unclosed.stmts);
        let unclosed_cfg = LexicalCfg::analyze(&unclosed.stmts, &unclosed_refs, safety).unwrap();
        let unclosed_proof = LabelFlowGroupProof {
            block: &unclosed,
            linear_prefix_end: 1,
            cfg: Some(&unclosed_cfg),
            facts: &facts,
            call_roots: &call_roots,
            lookup_roots: &lookup_roots,
            safety,
        };
        assert_eq!(
            unclosed_proof.group_safety(0, temp, &unclosed_group),
            Err(LabelFlowGroupFailure::Lifetime)
        );
    }

    #[test]
    fn root_lifetime_pair_must_match_the_candidate_home() {
        let left = TempId(0);
        let right = TempId(1);
        let left_overwrite = TempId(2);
        let left_home = HomeSlotKey::new(0, 0);
        let right_home = HomeSlotKey::new(1, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(left, left_home);
        facts.record_temp_home_slot_for_test(right, right_home);
        facts.record_temp_home_slot_for_test(left_overwrite, left_home);
        let stmts = vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(left), HirLValue::Temp(right)],
                values: HirValuePack::expanding(
                    Vec::new(),
                    HirPackTail::exact(call("producer"), 2),
                ),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
            HirStmt::CallStmt(Box::new(HirCallStmt {
                call: match call("collectgarbage") {
                    HirExpr::Call(call) => *call,
                    _ => unreachable!(),
                },
            })),
            assign(left_overwrite, HirExpr::Integer(0)),
        ];
        let safety = HirExprSafety::for_dialect(DecompileDialect::Lua54);
        let call_roots =
            collect_call_root_lifetimes(&stmts, &facts, safety, true, |_| true, |_| true);
        let lookup_roots = LookupGcRootLifetimeIndices::default();

        assert!(root_lifetime_closes_in_prefix(
            0,
            left_home,
            stmts.len(),
            &call_roots,
            &lookup_roots,
        ));
        assert!(!root_lifetime_closes_in_prefix(
            0,
            right_home,
            stmts.len(),
            &call_roots,
            &lookup_roots,
        ));
    }

    #[test]
    fn batched_initializer_certificate_requires_the_complete_exact_multicall_pair() {
        let bindings = vec![LocalId(0), LocalId(1)];
        let mut declaration = HirLocalDecl {
            bindings: bindings.clone(),
            values: HirValuePack::fixed(Vec::new()),
            initializer_merge_transaction: None,
        };
        let mut assignment = HirStmt::Assign(Box::new(HirAssign {
            targets: bindings.iter().copied().map(HirLValue::Local).collect(),
            values: HirValuePack::expanding(
                Vec::new(),
                HirPackTail::exact(call("producer"), bindings.len()),
            ),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }));
        certify_batched_initializer_merge_transaction(
            HirProtoRef(0),
            &mut declaration,
            &mut assignment,
        );

        let HirStmt::Assign(assignment) = assignment else {
            unreachable!();
        };
        assert_eq!(
            declaration.initializer_merge_transaction,
            assignment.initializer_merge_transaction
        );
        assert!(declaration.initializer_merge_transaction.is_some());

        let mut partial_declaration = HirLocalDecl {
            bindings: vec![bindings[0]],
            values: HirValuePack::fixed(Vec::new()),
            initializer_merge_transaction: None,
        };
        let mut non_multicall_assignment = HirStmt::Assign(Box::new(HirAssign {
            targets: bindings.iter().copied().map(HirLValue::Local).collect(),
            values: HirValuePack::fixed(vec![HirExpr::Integer(1), HirExpr::Integer(2)]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }));

        certify_batched_initializer_merge_transaction(
            HirProtoRef(0),
            &mut partial_declaration,
            &mut non_multicall_assignment,
        );

        let HirStmt::Assign(non_multicall_assignment) = non_multicall_assignment else {
            unreachable!();
        };
        assert_eq!(partial_declaration.initializer_merge_transaction, None);
        assert_eq!(non_multicall_assignment.initializer_merge_transaction, None);
    }
}
