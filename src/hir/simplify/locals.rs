//! 把跨语句存活的 temp 链提升为源码 local，并收敛函数入口的参数别名。
//!
//! 消费 promotion 的 home、close epoch、capture/debug 身份及物理根事实，
//! 为同一存活链建立稳定绑定；只在后续单个站点消费的中转值仍留给内联或构造器 owner。
//! 例如同一槽和 close epoch 的多个 SSA 版本可写回同一 local；close 后复用该槽
//! 属于新的词法身份，不能继续写入旧闭包 cell。

mod branch_merge;
mod entry_nil;
mod param_alias;
mod rewrite;

use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use super::label_refs::{count_label_references, stmt_has_label_or_goto};
use super::lexical_cfg::LexicalCfg;
use super::mention::{CaptureCollector, ToBeClosedTempCollector, stmt_writes_temp};
use super::root_lifetimes::{
    CallRootLifetimeIndices, RootEventBlock, RootEventIndex, RootEventStmt, RootLifetimeFacts,
    RootOverwritePolicy, collect_call_result_local_roots, collect_call_root_lifetimes,
    collect_scalar_gc_root_lifetimes, exact_multi_call_home_targets,
    stmt_has_argument_root_handoff,
};
use super::temp_touch::{collect_temp_refs_in_expr, expr_touches_any_temp};
use crate::hir::common::{
    HirAssign, HirBinding, HirBlock, HirCaptureMode, HirExpr, HirInitializerMergeTransactionId,
    HirLValue, HirLocalDecl, HirProto, HirProtoRef, HirStmt, HirValuePack, LocalId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

/// 对单个 proto 执行带 promotion facts 的 temp -> local 提升。
pub(super) fn promote_temps_to_locals_in_proto_with_facts(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    safety: HirExprSafety,
    dialect: crate::decompile::DecompileDialect,
) -> bool {
    // 定义数和根块实际绑定压力须同时超限；单纯 SSA 版本多不证明源码局部槽不足。
    // 无 debug 身份时才允许同 home/epoch 复用，避免把源码声明压成同一绑定。
    let compact_home_slots = hir_block_local_pressure(&proto.body) > crate::SOURCE_LOCAL_LIMIT
        && facts.home_slot_definition_count() > crate::SOURCE_LOCAL_LIMIT
        && proto.temp_debug_locals.iter().all(Option::is_none);
    if compact_home_slots {
        facts.enable_home_slot_compaction();
    }
    let mut physical_root_locals = BTreeSet::new();
    let mut promoted_bindings = Vec::new();
    let mut direct_seed_promotions = Vec::new();
    let mut debug_scope_locals = BTreeMap::new();
    let mut identities = (
        CaptureCollector::new(HirCaptureMode::ByReference),
        (
            CaptureCollector::new(HirCaptureMode::ByValue),
            ToBeClosedTempCollector::default(),
        ),
    );
    crate::hir::visit::visit_stmts(&proto.body.stmts, &mut identities);
    let (reference, (value, closed)) = identities;
    let reference_captured_temps = reference.bindings.temps;
    let mut identity_sensitive_temps = reference_captured_temps.clone();
    identity_sensitive_temps.extend(value.bindings.temps);
    let to_be_closed_temps = closed.temps;
    let label_refs = count_label_references(&proto.body.stmts);
    identity_sensitive_temps.extend(to_be_closed_temps.iter().copied());
    let mut cell_sensitive_temps = reference_captured_temps;
    cell_sensitive_temps.extend(to_be_closed_temps.iter().copied());
    let event_index = RootEventIndex::new(&proto.body.stmts, facts, safety);
    let constants_fit_rk = super::call_frames::constants_fit_rk(proto);
    let result = {
        let mut ctx = PromotionCtx {
            dialect,
            constants_fit_rk,
            proto_id: proto.id,
            facts,
            safety,
            temp_debug_locals: &proto.temp_debug_locals,
            temp_debug_scopes: &proto.temp_debug_scopes,
            next_local_index: &mut proto.local_count,
            local_debug_hints: &mut proto.local_debug_hints,
            local_debug_scopes: &mut proto.local_debug_scopes,
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
            event_index.root(),
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
    // 候选形成时冻结初始化值，apply 不重新匹配可能已被其它 plan 改写的 anchor。
    init: PromotionInit,
    action: PromotionAction,
    batch_declaration: Option<BatchDeclaration>,
    /// 在已证明的声明交接后或调用 dispatch 前结束旧源码根，保持原求值边界。
    root_release: Option<(usize, RootRelease)>,
}

#[derive(Debug, Clone)]
enum PromotionInit {
    FromAssign(HirValuePack),
    Empty,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum BatchDeclaration {
    /// 原 CALL/nil 批次的准备写继续留给原协议 owner 消费。
    Empty,
    /// 新绑定直接接收已验证的原常量组，不引入 nil 预写。
    Primitive,
}

#[derive(Debug, Clone, Copy)]
enum RootRelease {
    Before(LocalId),
    After(LocalId),
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

struct CallMoveRootHandoff {
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
    dialect: crate::decompile::DecompileDialect,
    constants_fit_rk: bool,
    proto_id: HirProtoRef,
    facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
    temp_debug_locals: &'a [Option<String>],
    temp_debug_scopes: &'a [Option<usize>],
    next_local_index: &'a mut usize,
    local_debug_hints: &'a mut Vec<Option<String>>,
    local_debug_scopes: &'a mut Vec<Option<usize>>,
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
    local_debug_hints: &'a mut Vec<Option<String>>,
    local_debug_scopes: &'a mut Vec<Option<usize>>,
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
        self.local_debug_hints
            .push(debug_hint_for_temp_group(self.temp_debug_locals, &temps));
        self.local_debug_scopes
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
            batch_declaration: None,
            root_release: None,
        });
    }

    fn allocate_batched_local(
        &mut self,
        decl_index: usize,
        home_slot: HomeSlotKey,
        temp: TempId,
        declaration: BatchDeclaration,
    ) -> LocalId {
        self.allocate_local(
            decl_index,
            Some(home_slot),
            BTreeSet::from([temp]),
            BTreeSet::new(),
            PromotionInit::Empty,
        );
        let plan = self.plans.last_mut().unwrap();
        plan.batch_declaration = Some(declaration);
        plan.local
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
            batch_declaration: None,
            root_release: None,
        });
    }
}

fn promote_block(
    ctx: &mut PromotionCtx<'_>,
    block: &mut HirBlock,
    event_block: RootEventBlock<'_>,
    inherited: &LocalMapping,
    inherited_sticky_slots: &BTreeMap<HomeSlotKey, LocalId>,
    outer_uses_temp: &dyn Fn(TempId) -> bool,
) -> PromotionResult {
    let empty = BTreeSet::new();
    promote_block_with_protection(
        ctx,
        block,
        event_block,
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
    event_block: RootEventBlock<'_>,
    inherited: &LocalMapping,
    inherited_sticky_slots: &BTreeMap<HomeSlotKey, LocalId>,
    outer_uses_temp: &dyn Fn(TempId) -> bool,
    protection: BlockProtection<'_>,
) -> PromotionResult {
    ctx.physical_root_locals
        .extend(collect_call_result_local_roots(
            &block.stmts,
            event_block,
            protection.trailing_root_condition,
            ctx.safety,
        ));

    let block_uses_outer_temp =
        |temp| outer_uses_temp(temp) || protection.current_plan_temps.contains(&temp);
    let plans = collect_plans(
        ctx,
        block,
        event_block,
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
    let mut root_releases = BTreeMap::<usize, Vec<RootRelease>>::new();
    for (index, local) in plans.iter().filter_map(|plan| plan.root_release) {
        root_releases.entry(index).or_default().push(local);
    }
    let append_root_releases = |index, before: bool, stmts: &mut Vec<HirStmt>| {
        if let Some(releases) = root_releases.get(&index) {
            stmts.extend(releases.iter().filter_map(|release| match *release {
                RootRelease::Before(local) if before => Some(HirStmt::LocalRootRelease(local)),
                RootRelease::After(local) if !before => Some(HirStmt::LocalRootRelease(local)),
                _ => None,
            }));
        }
    };
    let removable = plans
        .iter()
        .flat_map(|plan| plan.removable_aliases.iter().copied())
        .collect::<BTreeSet<_>>();

    let mut changed = !plans.is_empty();
    let mut mapping = Rc::clone(inherited);
    let mut current_slot_locals = inherited_sticky_slots.clone();
    let mut active_sticky_slots = inherited_sticky_slots.clone();
    let original_stmts = std::mem::take(&mut block.stmts);
    let mut rewritten = Vec::with_capacity(original_stmts.len());

    for (index, mut stmt) in original_stmts.into_iter().enumerate() {
        append_root_releases(index, true, &mut rewritten);
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
            if let Some(declaration) = plans.iter().find_map(|plan| plan.batch_declaration) {
                assert!(
                    plans.iter().all(|plan| {
                        matches!(plan.init, PromotionInit::Empty)
                            && plan
                                .batch_declaration
                                .is_none_or(|kind| kind == declaration)
                            && (plan.batch_declaration.is_some()
                                == matches!(plan.action, PromotionAction::AllocateLocal))
                    }),
                    "batched declarations must use one mode and share only empty handoff plans"
                );
                batched_decl_output_index = Some((rewritten.len(), declaration));
                rewritten.push(HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: plans
                        .iter()
                        .filter(|plan| plan.batch_declaration.is_some())
                        .map(|plan| plan.local)
                        .collect(),
                    values: HirValuePack::fixed(Vec::new()),
                    initializer_merge_transaction: None,
                })));
            } else {
                for plan in plans {
                    if let Some(anchor_stmt) =
                        rewrite_plan_anchor_stmt(plan, mapping.as_ref(), &stmt)
                    {
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
                    current_slot_locals.insert(slot, plan.local);
                }
                replaced_stmt |= plan_replaces_original_stmt(plan);
            }
        }
        activate_captured_slots_in_stmt(
            &stmt,
            ctx.facts,
            &current_slot_locals,
            &mut active_sticky_slots,
        );
        if replaced_stmt {
            append_root_releases(index, false, &mut rewritten);
            continue;
        }

        if removable.contains(&index) {
            continue;
        }

        // 候选拒绝[SemanticBarrier:Scope]：前缀读取可经 goto 回边重访；regress_485 中
        // 子块若把 `next=1; state=next` 合并成新 local，会让外层始终读取入口 state。
        // 查询原快照：前缀中已删除或替换的语句仍属于本轮外层保护，不按 rewritten 缩域。
        let child_uses_outer_temp = |temp| {
            block_uses_outer_temp(temp)
                || protection.descendant_temps.contains(&temp)
                || event_block.has_touch_before(temp, index)
                || event_block.has_touch_from(temp, index + 1)
        };
        let stmt_changed = rewrite_stmt(
            ctx,
            &mut stmt,
            &mapping,
            &active_sticky_slots,
            &child_uses_outer_temp,
            event_block.stmt(index),
        );
        changed |= stmt_changed;
        if let Some((decl_index, declaration)) = batched_decl_output_index {
            let HirStmt::LocalDecl(local_decl) = &mut rewritten[decl_index] else {
                unreachable!("batched declaration output must remain a local declaration");
            };
            if declaration == BatchDeclaration::Primitive {
                let HirStmt::Assign(assign) = &mut stmt else {
                    unreachable!("primitive declaration retains its original assignment");
                };
                assert!(
                    primitive_fixed_initializer(assign)
                        && local_decl.bindings.len() == assign.targets.len()
                        && local_decl
                            .bindings
                            .iter()
                            .zip(&assign.targets)
                            .all(|(local, target)| *target == HirLValue::Local(*local)),
                    "primitive declaration must own the complete original initializer"
                );
                // 整组新绑定直接接收原常量写；不先发空声明，避免增加原来没有的 nil 覆写。
                local_decl.values = std::mem::take(&mut assign.values);
                append_root_releases(index, false, &mut rewritten);
                continue;
            }
            certify_batched_initializer_merge_transaction(ctx.proto_id, local_decl, &mut stmt);
        }
        changed |= prune_binding_self_assigns(&mut stmt);
        if matches!(&stmt, HirStmt::Assign(assign) if assign.targets.is_empty()) {
            continue;
        }
        rewritten.push(stmt);
        append_root_releases(index, false, &mut rewritten);
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

/// 新资源的声明与 TBC activation 是同一入口事务；释放旧根必须在完整入口之后。
fn root_handoff_end(block: &HirBlock, declaration: usize) -> usize {
    if let Some(HirStmt::ToBeClosed(tbc)) = block.stmts.get(declaration + 1)
        && tbc.declaration(&block.stmts[declaration]).is_some()
    {
        declaration + 1
    } else {
        declaration
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

fn primitive_fixed_initializer(assign: &HirAssign) -> bool {
    assign.initializer_merge_transaction.is_none()
        && assign.generic_for_initializer_producer.is_none()
        && assign.method_rewrite_transaction.is_none()
        && assign.values.tail.is_none()
        && assign.values.fixed.len() == assign.targets.len()
        && assign.values.fixed.iter().all(|value| {
            matches!(
                value,
                HirExpr::Nil | HirExpr::Boolean(_) | HirExpr::Integer(_) | HirExpr::Number(_)
            )
        })
}

fn collect_plans(
    ctx: &mut PromotionCtx<'_>,
    block: &HirBlock,
    event_block: RootEventBlock<'_>,
    inherited: &BTreeMap<TempId, LocalId>,
    inherited_sticky_slots: &BTreeMap<HomeSlotKey, LocalId>,
    outer_uses_temp: &dyn Fn(TempId) -> bool,
) -> Vec<PromotionPlan> {
    let label_flow_boundary = block.stmts.iter().position(stmt_has_label_or_goto);
    let linear_prefix_end = label_flow_boundary.unwrap_or(block.stmts.len());
    let lifetime_stmts = &block.stmts[..linear_prefix_end];
    let has_label_flow = label_flow_boundary.is_some();
    let suffix_dominance = if has_label_flow {
        LexicalCfg::analyze(&block.stmts, ctx.label_refs, ctx.safety)
            .ok()
            .map(|cfg| cfg.suffix_dominance())
    } else {
        None
    };

    let facts = ctx.facts;
    let temp_debug_locals = ctx.temp_debug_locals;
    let temp_debug_scopes = ctx.temp_debug_scopes;
    let mut plans = Vec::<PromotionPlan>::new();
    let lifetime_snapshot =
        RootLifetimeFacts::with_events(lifetime_stmts, facts, ctx.safety, Some(event_block));
    let call_root_lifetimes = collect_call_root_lifetimes(
        &lifetime_snapshot,
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
            if ctx.to_be_closed_temps.contains(&temp) {
                RootOverwritePolicy::Reject
            } else if temp_debug_locals
                .get(temp.index())
                .is_some_and(Option::is_some)
            {
                // debug 新身份不复用匿名 root；确切覆盖仍须结束已物化的旧 owner。
                RootOverwritePolicy::ReleaseExisting
            } else {
                RootOverwritePolicy::Reuse
            }
        },
    );
    let scalar_gc_root_lifetimes =
        collect_scalar_gc_root_lifetimes(&lifetime_snapshot, facts, ctx.safety, |temp| {
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
        suffix_dominance: suffix_dominance.as_deref(),
        facts,
        closed_root_homes: suffix_dominance.as_ref().map_or_else(BTreeSet::new, |_| {
            call_root_lifetimes
                .closed_roots_before(linear_prefix_end)
                .chain(scalar_gc_root_lifetimes.closed_roots_before(linear_prefix_end))
                .map(|owner| (owner.root_index(), owner.home()))
                .collect()
        }),
        safety: ctx.safety,
    };
    let mut reserved_temps = BTreeSet::new();
    let mut reserved_alias_indices = BTreeSet::new();
    // 当前词法身份独立于 compaction 资格：受保护的 debug local 仍须接收后续同 scope 清零。
    let mut current_slot_locals = inherited_sticky_slots.clone();
    let mut sticky_slots = inherited_sticky_slots.clone();
    let mut unavailable_for_compaction = BTreeSet::new();
    let mut materialized_owner_locals = BTreeMap::<(usize, HomeSlotKey), LocalId>::new();
    let mut copy_reuse_last_touch = BTreeMap::<LocalId, usize>::new();
    let mut planned_temp_locals = BTreeMap::<TempId, LocalId>::new();
    let mut accounted_plans = 0;
    for (decl_index, stmt) in block.stmts.iter().enumerate() {
        // 每份 plan 只登记一次。一个 local 的所有已映射 SSA 版本共用最后需求位置；
        // 后续新增 capture/debug 身份会撤销资格，不能因最后一个 temp 已死就复用旧 cell。
        for plan in &plans[accounted_plans..] {
            planned_temp_locals.extend(plan.temps.iter().map(|&temp| (temp, plan.local)));
            let anonymous = ctx
                .local_debug_hints
                .get(plan.local.index())
                .is_none_or(Option::is_none)
                && ctx
                    .local_debug_scopes
                    .get(plan.local.index())
                    .is_none_or(Option::is_none)
                && debug_hint_for_temp_group(temp_debug_locals, &plan.temps).is_none()
                && plan
                    .temps
                    .iter()
                    .all(|temp| !ctx.identity_sensitive_temps.contains(temp));
            if !anonymous {
                copy_reuse_last_touch.remove(&plan.local);
                continue;
            }
            if matches!(plan.action, PromotionAction::AllocateLocal) {
                copy_reuse_last_touch.insert(plan.local, plan.decl_index);
            }
            if let Some(last) = copy_reuse_last_touch.get_mut(&plan.local) {
                for &temp in &plan.temps {
                    *last = (*last).max(event_block.last_touch(temp).unwrap_or(plan.decl_index));
                }
            }
        }
        accounted_plans = plans.len();
        if reserved_alias_indices.contains(&decl_index) {
            activate_captured_slots_in_stmt(stmt, facts, &current_slot_locals, &mut sticky_slots);
            continue;
        }

        activate_captured_slots_in_stmt(stmt, facts, &current_slot_locals, &mut sticky_slots);

        for owner in call_root_lifetimes
            .call_dispatch_releases(decl_index)
            .chain(scalar_gc_root_lifetimes.call_dispatch_releases(decl_index))
        {
            let Some(local) = materialized_owner_locals
                .get(&(owner.root_index(), owner.home()))
                .copied()
            else {
                continue;
            };
            plans.push(PromotionPlan {
                decl_index,
                local,
                home_slot: None,
                temps: BTreeSet::new(),
                removable_aliases: BTreeSet::new(),
                init: PromotionInit::Empty,
                action: PromotionAction::ReuseExistingLocal,
                batch_declaration: None,
                root_release: Some((decl_index, RootRelease::Before(local))),
            });
            ctx.physical_root_locals.insert(local);
            current_slot_locals.remove(&owner.home());
        }

        if let HirStmt::LocalDecl(decl) = stmt
            && let [local] = decl.bindings.as_slice()
            && let Some(owner) = call_root_lifetimes.continuation_owner(decl_index)
            && let Some(old_local) = materialized_owner_locals
                .get(&(owner.root_index(), owner.home()))
                .copied()
            && old_local != *local
        {
            // 捕获 owner 已在前层建立声明；消费其同值交接事实，保留原 declaration 与 capture cell。
            plans.push(PromotionPlan {
                decl_index,
                local: *local,
                home_slot: Some(owner.home()),
                temps: BTreeSet::new(),
                removable_aliases: BTreeSet::new(),
                init: PromotionInit::Empty,
                action: PromotionAction::ReuseExistingLocal,
                batch_declaration: None,
                root_release: Some((
                    root_handoff_end(block, decl_index),
                    RootRelease::After(old_local),
                )),
            });
            ctx.physical_root_locals.extend([old_local, *local]);
            materialized_owner_locals.insert((owner.root_index(), owner.home()), *local);
            current_slot_locals.insert(owner.home(), *local);
            unavailable_for_compaction.insert(*local);
            continue;
        }

        let mut separate_call_move_homes = false;
        if let Some((root_temp, _)) = stmt.scalar_temp_assignment()
            && let Some(handoffs) = call_move_root_handoffs(
                block,
                decl_index,
                root_temp,
                facts,
                &call_root_lifetimes,
                &materialized_owner_locals,
            )
        {
            separate_call_move_homes = true;
            // call 自己的结果槽与后续 MOVE 的目标槽各有生命周期；即使只覆盖一个
            // 旧 home，结果槽仍有独立 root 时也必须保留两个 owner。先完整匹配所有 pair、
            // old owner 与 HIR copy，再一次登记 plans；不能只复用任意一个 home，或在
            // 半数匹配后提交，否则会把同一个 VM overwrite transaction 拆开。
            for handoff in handoffs {
                // 该 COPY 已实际写入源码 owner，后续精确覆盖必须能找到它。
                // GC 观察只选择同值的一个代表；没有选中本 home 不代表它未被物化。
                materialized_owner_locals
                    .insert((handoff.alias_index, handoff.home), handoff.local);
                if call_root_lifetimes.is_root(handoff.alias_index) {
                    ctx.physical_root_locals.insert(handoff.local);
                }
                let mut allocator = PlanAllocator {
                    temp_debug_locals,
                    temp_debug_scopes,
                    plans: &mut plans,
                    reserved_temps: &mut reserved_temps,
                    reserved_alias_indices: &mut reserved_alias_indices,
                    next_local_index: ctx.next_local_index,
                    local_debug_hints: ctx.local_debug_hints,
                    local_debug_scopes: ctx.local_debug_scopes,
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
            .owner_overwrites(decl_index)
            .filter(|pair| {
                has_grouped_targets
                    && (call_root_lifetimes.owner_is_preserved(*pair)
                        || materialized_owner_locals
                            .contains_key(&(pair.root_index(), pair.home())))
            })
            .map(|pair| (pair.root_index(), pair.home()))
            .chain(
                scalar_gc_root_lifetimes
                    .owner_overwrites(decl_index)
                    .filter(|pair| {
                        scalar_gc_root_lifetimes.is_root(pair.root_index())
                            || materialized_owner_locals
                                .contains_key(&(pair.root_index(), pair.home()))
                    })
                    .map(|pair| (pair.root_index(), pair.home())),
            )
            .collect::<Vec<_>>();
        let physical_root_handoffs = physical_root_pairs
            .iter()
            .map(|(root_index, home)| {
                let local = materialized_owner_locals
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
        let mut allocator = PlanAllocator {
            temp_debug_locals,
            temp_debug_scopes,
            plans: &mut plans,
            reserved_temps: &mut reserved_temps,
            reserved_alias_indices: &mut reserved_alias_indices,
            next_local_index: ctx.next_local_index,
            local_debug_hints: ctx.local_debug_hints,
            local_debug_scopes: ctx.local_debug_scopes,
            promoted_bindings: ctx.promoted_bindings,
            direct_seed_promotions: ctx.direct_seed_promotions,
            debug_scope_locals: ctx.debug_scope_locals,
        };
        let has_physical_root_handoff = !physical_root_handoffs.is_empty();
        for (temps, home, local) in physical_root_handoffs {
            ctx.physical_root_locals.insert(local);
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
            materialized_owner_locals.insert((decl_index, home), local);
            if call_root_lifetimes.is_root(decl_index)
                || scalar_gc_root_lifetimes.is_root(decl_index)
            {
                // A scalar overwrite can terminate one physical-root transaction and produce
                // the next one in the same local. Preserve that chained owner for its later pair.
                ctx.physical_root_locals.insert(local);
                unavailable_for_compaction.insert(local);
            }
        }

        let nil_members = (|| {
            if has_label_flow {
                return None;
            }
            let HirStmt::Assign(assign) = stmt else {
                return None;
            };
            let HirLValue::Temp(first) = assign.targets.first()? else {
                return None;
            };
            let temps = facts.nil_write_temps(*first)?;
            if assign.targets.len() != temps.len()
                || assign.values.fixed.len() != temps.len()
                || assign.values.tail.is_some()
                || !assign
                    .values
                    .fixed
                    .iter()
                    .all(|value| matches!(value, HirExpr::Nil))
            {
                return None;
            }
            let base = facts.trusted_temp_home_slot(*first)?;
            // 捕获的连续初始 nil 组需要各自的源码 cell，不能因多目标而永远留给 AST。
            // 只为尚无 owner 的整组建立新 local；已有 captured cell 的复用仍走原限制。
            let fresh_captured_group = temps.len() > 1
                && temps
                    .iter()
                    .any(|temp| ctx.cell_sensitive_temps.contains(temp))
                && temps.iter().all(|temp| {
                    !allocator.reserved_temps.contains(temp)
                        && facts
                            .trusted_temp_home_slot(*temp)
                            .is_some_and(|home| !current_slot_locals.contains_key(&home))
                });
            let mut members = Vec::new();
            for (offset, (&temp, target)) in temps.iter().zip(&assign.targets).enumerate() {
                let home = facts.trusted_temp_home_slot(temp)?;
                if *target != HirLValue::Temp(temp)
                    || home.slot() != base.slot() + offset
                    || !facts
                        .complete_temp_definition_write_homes(temp)
                        .iter()
                        .copied()
                        .eq([home])
                {
                    return None;
                }
                if allocator.reserved_temps.contains(&temp) {
                    // 只承接本次原 root handoff，不能借别处已保留的身份补组。
                    materialized_owner_locals.get(&(decl_index, home))?;
                    continue;
                }
                if inherited.contains_key(&temp)
                    || (ctx.identity_sensitive_temps.contains(&temp) && !fresh_captured_group)
                    || ctx.to_be_closed_temps.contains(&temp)
                    || outer_uses_temp(temp)
                    || event_block.has_touch_before(temp, decl_index)
                    || temp_debug_locals
                        .get(temp.index())
                        .is_some_and(Option::is_some)
                    || temp_debug_scopes
                        .get(temp.index())
                        .is_some_and(Option::is_some)
                {
                    return None;
                }
                let local = if let Some(&local) = current_slot_locals.get(&home) {
                    // 与后续 COPY 使用同一退休证明：该 Local 的所有匿名 SSA 版本
                    // 都已结束需求。原 nil 在当前指令覆盖，不提前清根或扩展旧 cell。
                    if !copy_reuse_last_touch
                        .get(&local)
                        .is_some_and(|last| *last < decl_index)
                    {
                        return None;
                    }
                    Some(local)
                } else if has_physical_root_handoff || fresh_captured_group {
                    None
                } else {
                    // 无 root handoff 不建立新 holder；每个原槽都须已有可复用声明。
                    return None;
                };
                members.push((temp, home, local));
            }
            Some(members)
        })();
        if let Some(members) = nil_members {
            // 先验证整组再登记；既有 Local 的原 nil Assign 不改写。新成员仅补
            // 相邻 empty 声明，完整 source-frame 事务再合并该声明与原 LOADNIL 批次。
            for (temp, home, local) in members {
                let local = if let Some(local) = local {
                    allocator.reuse_existing_local(
                        decl_index,
                        local,
                        Some(home),
                        BTreeSet::from([temp]),
                        BTreeSet::new(),
                        PromotionInit::Empty,
                    );
                    local
                } else {
                    allocator.allocate_batched_local(
                        decl_index,
                        home,
                        temp,
                        BatchDeclaration::Empty,
                    )
                };
                materialized_owner_locals.insert((decl_index, home), local);
                current_slot_locals.insert(home, local);
            }
        }
        if let HirStmt::Assign(assign) = stmt
            && assign.targets.len() > 1
        {
            let fresh_group = (|| {
                if has_label_flow || ctx.compact_home_slots || !primitive_fixed_initializer(assign)
                {
                    return None;
                }
                let mut members = Vec::with_capacity(assign.targets.len());
                let mut first_slot = None;
                for (offset, target) in assign.targets.iter().enumerate() {
                    let HirLValue::Temp(temp) = target else {
                        return None;
                    };
                    let home = facts.trusted_temp_home_slot(*temp)?;
                    let base = *first_slot.get_or_insert(home.slot());
                    if home.slot() != base + offset
                        || inherited.contains_key(temp)
                        || allocator.reserved_temps.contains(temp)
                        || current_slot_locals.contains_key(&home)
                        || outer_uses_temp(*temp)
                        || event_block.has_touch_before(*temp, decl_index)
                        || !event_block.has_read_from(*temp, decl_index + 1)
                        || event_block
                            .touch_positions_from(*temp, decl_index + 1)
                            .take(2)
                            .count()
                            < 2
                        || ctx.identity_sensitive_temps.contains(temp)
                        || ctx.to_be_closed_temps.contains(temp)
                        || temp_debug_locals
                            .get(temp.index())
                            .is_some_and(Option::is_some)
                        || temp_debug_scopes
                            .get(temp.index())
                            .is_some_and(Option::is_some)
                        || !facts
                            .complete_temp_definition_write_homes(*temp)
                            .iter()
                            .copied()
                            .eq([home])
                    {
                        return None;
                    }
                    members.push((*temp, home));
                }
                Some(members)
            })();
            if let Some(members) = fresh_group {
                // 先验证全部成员，再按原次序分配；部分既有 owner 的批次仍走下面的复用协议。
                for (temp, home) in members {
                    let local = allocator.allocate_batched_local(
                        decl_index,
                        home,
                        temp,
                        BatchDeclaration::Primitive,
                    );
                    materialized_owner_locals.insert((decl_index, home), local);
                    current_slot_locals.insert(home, local);
                }
                continue;
            }
            let pure_fixed_pack = assign.values.tail.is_none()
                && assign.values.fixed.len() == assign.targets.len()
                && assign.values.fixed.iter().all(|value| {
                    matches!(
                        value,
                        HirExpr::TempRef(_)
                            | HirExpr::ParamRef(_)
                            | HirExpr::LocalRef(_)
                            | HirExpr::Nil
                            | HirExpr::Boolean(_)
                            | HirExpr::Integer(_)
                            | HirExpr::Number(_)
                    )
                });
            for (target_index, target) in assign.targets.iter().enumerate() {
                let HirLValue::Temp(temp) = target else {
                    continue;
                };
                if inherited.contains_key(temp) || allocator.reserved_temps.contains(temp) {
                    continue;
                }
                let Some(home) = facts.trusted_temp_home_slot(*temp) else {
                    continue;
                };
                // 并行 carried seed 也可能只是把刚产生的 CALL 结果交给同 home。
                // 匿名旧 owner 继续承接后续循环写，不能另建一个永久保活旧值的 local。
                let same_home_source =
                    assign
                        .values
                        .fixed
                        .get(target_index)
                        .and_then(|value| match value {
                            HirExpr::TempRef(source) => planned_temp_locals
                                .get(source)
                                .copied()
                                .filter(|_| facts.trusted_temp_home_slot(*source) == Some(home)),
                            _ => None,
                        });
                if let Some(local) = same_home_source
                    && current_slot_locals.get(&home) == Some(&local)
                    && ctx.physical_root_locals.contains(&local)
                    && !has_label_flow
                    && !outer_uses_temp(*temp)
                    && !event_block.has_touch_before(*temp, decl_index)
                    && !ctx.identity_sensitive_temps.contains(temp)
                    && !ctx.to_be_closed_temps.contains(temp)
                    && temp_debug_scopes
                        .get(temp.index())
                        .is_none_or(Option::is_none)
                    && temp_debug_locals
                        .get(temp.index())
                        .is_none_or(Option::is_none)
                    && copy_reuse_last_touch
                        .get(&local)
                        .is_some_and(|last| *last <= decl_index)
                    && pure_fixed_pack
                {
                    allocator.reuse_existing_local(
                        decl_index,
                        local,
                        Some(home),
                        BTreeSet::from([*temp]),
                        BTreeSet::new(),
                        PromotionInit::Empty,
                    );
                    materialized_owner_locals.insert((decl_index, home), local);
                    continue;
                }
                let Some(scope) = temp_debug_scopes.get(temp.index()).copied().flatten() else {
                    continue;
                };
                let Some(local) = allocator.debug_scope_locals.get(&(home, scope)).copied() else {
                    continue;
                };
                let group = BTreeSet::from([*temp]);
                if current_slot_locals.get(&home) != Some(&local)
                    || outer_uses_temp(*temp)
                    || event_block.has_touch_before(*temp, decl_index)
                    || has_label_flow
                {
                    // debug scope 身份不代表当前 HIR 声明可见；也不能只改子块的写入，
                    // 留下外部/回边读取旧 temp。多目标尚无 label-flow promotion 证明。
                    continue;
                }
                // 并行 carried seed 与单目标写入消费同一 debug scope 身份；保留 RHS
                // 求值和赋值位置，不因机械批次制造另一个强根。
                allocator.reuse_existing_local(
                    decl_index,
                    local,
                    Some(home),
                    group,
                    BTreeSet::new(),
                    PromotionInit::Empty,
                );
                materialized_owner_locals.insert((decl_index, home), local);
            }
        }

        let call_root_homes = call_root_lifetimes
            .root_homes(decl_index)
            .collect::<BTreeSet<_>>();
        if let Some(targets) = exact_multi_call_home_targets(stmt, facts)
            && (!call_root_homes.is_empty()
                || !matches!(stmt, HirStmt::Assign(assign) if assign.generic_for_initializer_producer.is_some()))
            && (!has_label_flow || !call_root_homes.is_empty())
            && targets.iter().all(|(temp, _)| {
                !ctx.to_be_closed_temps.contains(temp)
                    && !outer_uses_temp(*temp)
                    && !event_block.has_touch_before(*temp, decl_index)
                    && !event_block.has_read_at(*temp, decl_index)
            })
        {
            // 完整返回组共用一次求值；只物化其中一个目标会丢失其余目标的后续 home 端点。
            // TBC 仍由资源声明 owner 消费整组协议；普通分组不越过尚未证明的 label/backedge。

            let mut allocator = PlanAllocator {
                temp_debug_locals,
                temp_debug_scopes,
                plans: &mut plans,
                reserved_temps: &mut reserved_temps,
                reserved_alias_indices: &mut reserved_alias_indices,
                next_local_index: ctx.next_local_index,
                local_debug_hints: ctx.local_debug_hints,
                local_debug_scopes: ctx.local_debug_scopes,
                promoted_bindings: ctx.promoted_bindings,
                direct_seed_promotions: ctx.direct_seed_promotions,
                debug_scope_locals: ctx.debug_scope_locals,
            };
            for (temp, home) in targets {
                let existing_local = inherited
                    .get(&temp)
                    .copied()
                    .or_else(|| materialized_owner_locals.get(&(decl_index, home)).copied());
                let local = if let Some(local) = existing_local {
                    local
                } else {
                    assert!(
                        !allocator.reserved_temps.contains(&temp),
                        "reserved multi-call target must retain its promotion owner"
                    );
                    allocator.allocate_batched_local(
                        decl_index,
                        home,
                        temp,
                        BatchDeclaration::Empty,
                    )
                };
                materialized_owner_locals.insert((decl_index, home), local);
                current_slot_locals.insert(home, local);
                if call_root_homes.contains(&home) {
                    ctx.physical_root_locals.insert(local);
                    unavailable_for_compaction.insert(local);
                }
            }
            continue;
        }

        let Some((root_temp, _)) = stmt.scalar_temp_assignment() else {
            continue;
        };
        if inherited.contains_key(&root_temp) || reserved_temps.contains(&root_temp) {
            // 已被祖先映射或当前 plan 认领的 temp 不再形成新候选。
            continue;
        }
        if event_block.has_touch_before(root_temp, decl_index) {
            // 候选拒绝[SemanticBarrier:ValueFlow]：backedge/goto 可让文本前方读取同一
            // TempId 的入口或上一轮值；在此定义点新建 local 会把该读取切到未初始化 binding。
            continue;
        }
        // 目标 temp 自己又出现在 RHS 里时，这条赋值表达的是“沿用同一状态槽位继续更新”，
        // 不能在 locals pass 里把它误提升成新的 block-local。否则像 loop carried state
        // 或分支内的状态写回，会被拆成 `local next = step(state)`，原状态槽位反而失去写回。
        if stmt_self_updates_temp(stmt, root_temp)
            && !is_recursive_closure_initializer(stmt, root_temp, facts)
        {
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
            event_block,
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
            .and_then(|home| scalar_gc_root_lifetimes.overwrite_pair_for_home(decl_index, home))
            .map(|pair| (pair.root_index(), pair.home()));
        let preceding_call_root = home_slot
            .and_then(|home| {
                call_root_lifetimes
                    .owner_overwrites(decl_index)
                    .find(|owner| {
                        owner.home() == home
                            && (call_root_lifetimes.owner_is_preserved(*owner)
                                || materialized_owner_locals
                                    .contains_key(&(owner.root_index(), home)))
                    })
            })
            .or_else(|| {
                (!separate_call_move_homes)
                    .then(|| call_root_lifetimes.unambiguous_overwrite_pair(decl_index))
                    .flatten()
            })
            .map(|pair| (pair.root_index(), pair.home()));
        let continuation_owner = call_root_lifetimes.continuation_owner(decl_index);
        let continuation_local = continuation_owner.and_then(|owner| {
            materialized_owner_locals
                .get(&(owner.root_index(), owner.home()))
                .copied()
        });
        // 新 debug scope 与 TBC owner 保留独立声明入口；同值交接不从匿名 root 的保活资格反推身份。
        let release_local = continuation_local.filter(|_| {
            sticky_local.is_none()
                && debug_local.is_none()
                && (debug_scope_for_temp_group(temp_debug_scopes, &group).is_some()
                    || group
                        .iter()
                        .any(|temp| ctx.to_be_closed_temps.contains(temp)))
        });
        let preceding_physical_root = preceding_call_root.or(preceding_lookup_root).or_else(|| {
            continuation_owner
                .filter(|owner| call_root_lifetimes.owner_is_preserved(*owner))
                .map(|owner| (owner.root_index(), owner.home()))
        });
        let preceding_physical_root_local = preceding_physical_root
            .and_then(|owner| materialized_owner_locals.get(&owner).copied());
        let force_physical_root_local = group_has_physical_root
            || call_root_lifetimes.is_root(decl_index)
            || scalar_gc_root_lifetimes.is_root(decl_index)
            || preceding_physical_root_local.is_some()
            || release_local.is_some();
        if sticky_local.is_none()
            && debug_local.is_none()
            && !force_physical_root_local
            && group.len() == 1
            && debug_hint_for_temp_group(temp_debug_locals, &group).is_none()
            && facts.is_direct_table_seed_temp(root_temp)
            && facts.overwrites_entry_nil(root_temp)
            && (matches!(block.stmts.get(decl_index + 1), Some(HirStmt::TableSetList(batch))
                if batch.base == HirExpr::TempRef(root_temp) && batch.values.tail.is_none())
                || touching_stmt_indices.len() == 1
                    && matches!(stmt, HirStmt::Assign(assign)
                        if assign.values.tail.is_none()
                            && matches!(assign.values.fixed.as_slice(), [HirExpr::TableConstructor(_)])))
            && facts.temp_is_transferred_call_argument(root_temp)
            && touching_stmt_indices
                .iter()
                .filter(|index| stmt_has_argument_root_handoff(&block.stmts[**index], root_temp))
                .count()
                == 1
        {
            // 候选拒绝[LayerBoundary]：入口 seed 与当前参数交接端点已配对；相邻
            // fixed batch 由 constructor owner 消费，完整且单次使用的 constructor 则
            // 交给 temp-inline。raw SETLIST 被消费后许可仍有效，不能新增跨调用的 local
            // 根（regress_342）；这里不重建字段、原始参数协议或内联求值顺序。
            continue;
        }
        let reusable_local = if release_local.is_some() {
            None
        } else {
            sticky_local
                .or(debug_local)
                .or(preceding_physical_root_local)
                .or_else(|| {
                    if ctx.dialect != crate::decompile::DecompileDialect::Luau
                        || !facts.is_direct_comparison_result(
                            root_temp,
                            stmt.scalar_temp_assignment()?.1,
                            |temp| {
                                facts.trusted_temp_home_slot(temp).is_some_and(|home| {
                                    planned_temp_locals.get(&temp).is_some_and(|local| {
                                        current_slot_locals.get(&home) == Some(local)
                                    })
                                })
                            },
                        )
                    {
                        return None;
                    }
                    let local = *current_slot_locals.get(&home_slot?)?;
                    // Luau 比较直接在目标写 LOADBOOL；原决策保证写发生在比较后。
                    // 复用匿名原槽，避免新增声明把后续 CALL 的 callee/参数区整体抬高。
                    (debug_hint_for_temp_group(temp_debug_locals, &group).is_none()
                        && group
                            .iter()
                            .all(|temp| !ctx.identity_sensitive_temps.contains(temp))
                        && copy_reuse_last_touch
                            .get(&local)
                            .is_some_and(|last| *last < decl_index))
                    .then_some(local)
                })
                .or_else(|| {
                    let home = home_slot?;
                    let HirExpr::Call(call) = stmt.scalar_temp_assignment()?.1 else {
                        return None;
                    };
                    let predecessor = facts.same_slot_call_predecessor(call, root_temp)?;
                    let local = *planned_temp_locals.get(&predecessor)?;
                    // 已知词法 closure 的 COPY 不需要额外 GC root，仍有真实的原 CALL 覆盖。
                    // 只连接已物化的匿名 callee 与原结果，所有旧版本需求在此结束；完整调用
                    // 的 freereg/准备事件仍交给 native frame owner，不能由这里授权折叠 RHS。
                    (current_slot_locals.get(&home) == Some(&local)
                        && debug_hint_for_temp_group(temp_debug_locals, &group).is_none()
                        && group
                            .iter()
                            .all(|temp| !ctx.identity_sensitive_temps.contains(temp))
                        && copy_reuse_last_touch
                            .get(&local)
                            .is_some_and(|last| *last <= decl_index))
                    .then_some(local)
                })
                .or_else(|| {
                    let home = home_slot?;
                    let source_home = match stmt.scalar_temp_assignment()?.1 {
                        HirExpr::TempRef(source) => facts.trusted_temp_home_slot(*source),
                        HirExpr::LocalRef(source) => facts.trusted_local_home_slot(*source),
                        HirExpr::ParamRef(source) => facts.trusted_param_home_slot(*source),
                        _ => None,
                    }?;
                    let local = *current_slot_locals.get(&home)?;
                    // 原不同 home 的 COPY 仍在原位求值并写回；不把 CALL/分配的
                    // 覆盖时点改成整个 RHS 结束。旧身份的全部逻辑需求必须已结束，
                    // 新版本也必须匿名，不能把新的 source scope 接到旧匿名 cell，
                    // 否则其后同 scope 写会另建身份而留下旧根。
                    (source_home != home
                        && debug_hint_for_temp_group(temp_debug_locals, &group).is_none()
                        && group
                            .iter()
                            .all(|temp| !ctx.identity_sensitive_temps.contains(temp))
                        && copy_reuse_last_touch
                            .get(&local)
                            .is_some_and(|last| *last < decl_index))
                    .then_some(local)
                })
                .or_else(|| {
                    if has_label_flow
                        || !ctx.constants_fit_rk
                        || !matches!(
                            ctx.dialect,
                            crate::decompile::DecompileDialect::Lua51
                                | crate::decompile::DecompileDialect::Lua52
                                | crate::decompile::DecompileDialect::Lua53
                                | crate::decompile::DecompileDialect::Lua54
                                | crate::decompile::DecompileDialect::Lua55
                        )
                    {
                        return None;
                    }
                    let home = home_slot?;
                    let HirExpr::TableAccess(access) = stmt.scalar_temp_assignment()?.1 else {
                        return None;
                    };
                    let crate::hir::common::HirOperationSources::Single(source) = access.sources
                    else {
                        return None;
                    };
                    let layout = facts.native_table_read_layout(access)?;
                    let base = match &access.base {
                        HirExpr::TempRef(temp) => facts.trusted_temp_home_slot(*temp),
                        HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
                        HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
                        _ => None,
                    }?;
                    let local = *current_slot_locals.get(&home)?;
                    // 原 GETTABLE 已在此写目标槽，低槽 base 与内嵌 key 不额外准备
                    // scratch；只复用已退休匿名身份，不能从查表外形推断 RHS 写回布局。
                    (facts.operation_result_temp(source) == Some(root_temp)
                        && facts.trusted_temp_home_slot(root_temp) == Some(home)
                        && layout.base == base
                        && base.slot() < home.slot()
                        && layout.key.is_none()
                        && matches!(
                            access.key,
                            HirExpr::String(_) | HirExpr::Integer(_) | HirExpr::Number(_)
                        )
                        && debug_hint_for_temp_group(temp_debug_locals, &group).is_none()
                        && debug_scope_for_temp_group(temp_debug_scopes, &group).is_none()
                        && group
                            .iter()
                            .all(|temp| !ctx.identity_sensitive_temps.contains(temp))
                        && copy_reuse_last_touch
                            .get(&local)
                            .is_some_and(|last| *last < decl_index))
                    .then_some(local)
                })
                .or_else(|| {
                    ctx.compact_home_slots
                        .then(|| home_slot.and_then(|slot| current_slot_locals.get(&slot).copied()))
                        .flatten()
                        .filter(|local| !unavailable_for_compaction.contains(local))
                })
        };

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
                .all(|index| !event_block.reads_any(index, &group))
        {
            // 只有写 touch、没有表达式读取的链不承载可恢复的
            // 跨语句 binding。dead-temps 仍按自己的 discard-safe/raw-home 合同清理可删写入；
            // locals 不把未被读取的 SSA 版本固化成源码 local。
            continue;
        }
        if sticky_local.is_none()
            && !force_physical_root_local
            && debug_hint_for_temp_group(temp_debug_locals, &group).is_none()
        {
            let first_touch_index = touching_stmt_indices.first().copied();
            // 只在控制头里单次消费的 temp，更像机械性的结构参数而不是源码级 local。
            // 只有一次后续消费的全局别名或字符串常量，必须结合消费站点判定：
            // 全局别名只有作为表字段安装的 base，字符串常量只有作为调用实参，
            // 才更像寄存器级脚手架而不是源码 local。数字/布尔/nil 等也可能是
            // 捕获 local 的重绑定值，仍按原规则保守提升。
            if touching_stmt_indices.len() == 1 {
                let use_stmt = &block.stmts[first_touch_index.expect("single touch must exist")];
                // 未被 temp-inline 消费的闭包仍需在原创建点拥有 binding。仅在循环条件
                // 出现一次不是一次执行；交给 AST 才物化会使后续 HIR 源码帧缺少这个前缀身份。
                if event_block
                    .stmt(first_touch_index.unwrap())
                    .consumes_only_control_head(use_stmt, &group)
                    && !matches!(
                        single_temp_assign_value(stmt, root_temp),
                        Some(HirExpr::Closure(_))
                    )
                {
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
            local_debug_hints: ctx.local_debug_hints,
            local_debug_scopes: ctx.local_debug_scopes,
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
                current_slot_locals.insert(slot, local);
            }
            if ctx.facts.is_direct_table_seed_temp(root_temp) {
                allocator.direct_seed_promotions.push((root_temp, local));
            }
            local
        };
        if let Some(old_local) = release_local {
            allocator.plans.last_mut().unwrap().root_release = Some((
                root_handoff_end(block, decl_index),
                RootRelease::After(old_local),
            ));
            let owner = continuation_owner.unwrap();
            // 替换当前 owner 后，旧 local 仍须保留其精确 nil 端点，不能从保护集合中消失。
            ctx.physical_root_locals.insert(old_local);
            ctx.physical_root_locals.insert(selected_local);
            materialized_owner_locals.insert((owner.root_index(), owner.home()), selected_local);
        }
        if let Some((home, old_local)) = call_root_lifetimes
            .overwrite_releases(decl_index)
            .find(|owner| Some(owner.home()) == home_slot)
            .and_then(|owner| {
                materialized_owner_locals
                    .get(&(owner.root_index(), owner.home()))
                    .map(|&local| (owner.home(), local))
            })
            .filter(|(_, old_local)| *old_local != selected_local)
        {
            // 先确定实际身份：同 debug scope 若复用旧 local，原赋值已退休旧值；
            // 只有独立声明才在 RHS 完成后释放旧 local，不能把新值一起清空。
            allocator.plans.last_mut().unwrap().root_release =
                Some((decl_index, RootRelease::After(old_local)));
            ctx.physical_root_locals.insert(old_local);
            current_slot_locals.insert(home, selected_local);
        }
        let collected_root =
            call_root_lifetimes.is_root(decl_index) || scalar_gc_root_lifetimes.is_root(decl_index);
        if let Some(home) = home_slot
            && !(preceding_physical_root_local == Some(selected_local)
                && preceding_physical_root.is_some_and(|(_, root_home)| root_home != home))
        {
            // CALL/MOVE 可整体复用 MOVE 目标 home 的 local，却没有独立物化 CALL 结果
            // home。不能再按 root_temp 的 home 登记该 local：regress_500 中 r5 接收
            // r6 的结果后，assert 覆盖 r6，而后续 object.total 仍读取 r5。
            materialized_owner_locals.insert((decl_index, home), selected_local);
        }
        if collected_root
            || (group_has_physical_root && home_slot.is_some())
            || preceding_physical_root_local.is_some()
        {
            ctx.physical_root_locals.insert(selected_local);
        }
        if collected_root
            || (group_has_physical_root && home_slot.is_some())
            || (continuation_owner.is_some() && preceding_physical_root_local.is_some())
            || release_local.is_some()
        {
            // This local must stay dedicated to the root result until its proven physical
            // overwrite partner reuses it. Home-slot compaction may otherwise lend the same
            // source local to a simultaneously-live value before that overwrite occurs.
            unavailable_for_compaction.insert(selected_local);
        } else if let Some(home) = home_slot
            && let Some((_, root_home)) = preceding_call_root.or(preceding_lookup_root)
            && root_home == home
        {
            // 精确覆盖已经结束旧 root，当前 owner 可以重新参与同槽复用。
            // 跨 home 的 call/MOVE 交接只证明旧目标槽被覆盖，不能把它登记成
            // call 自己的结果槽，否则下一次结果槽写会破坏仍活跃的 MOVE 目标。
            unavailable_for_compaction.remove(&selected_local);
            current_slot_locals.insert(home, selected_local);
        }
    }

    let mut sticky_slots = inherited_sticky_slots.clone();
    for (decl_index, stmt) in block.stmts[..linear_prefix_end].iter().enumerate() {
        let is_reserved = |temp| inherited.contains_key(&temp) || reserved_temps.contains(&temp);
        let mut merge_temps = branch_merge::candidate_temps(
            &block.stmts,
            stmt,
            event_block,
            decl_index,
            &is_reserved,
            ctx.safety,
        );
        if (call_root_lifetimes
            .overwrite_pairs(decl_index)
            .next()
            .is_some()
            || scalar_gc_root_lifetimes
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
                .and_then(|home| scalar_gc_root_lifetimes.overwrite_pair_for_home(decl_index, home))
                .map(|pair| (pair.root_index(), pair.home()));
            let preceding_call_root = home_slot
                .and_then(|home| call_root_lifetimes.overwrite_pair_for_home(decl_index, home))
                .or_else(|| call_root_lifetimes.unambiguous_overwrite_pair(decl_index))
                .map(|pair| (pair.root_index(), pair.home()));
            let preceding_physical_root_local = preceding_call_root
                .or(preceding_lookup_root)
                .and_then(|(root, root_home)| {
                    materialized_owner_locals.get(&(root, root_home)).copied()
                });
            let mut allocator = PlanAllocator {
                temp_debug_locals,
                temp_debug_scopes,
                plans: &mut plans,
                reserved_temps: &mut reserved_temps,
                reserved_alias_indices: &mut reserved_alias_indices,
                next_local_index: ctx.next_local_index,
                local_debug_hints: ctx.local_debug_hints,
                local_debug_scopes: ctx.local_debug_scopes,
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
                                .then(|| current_slot_locals.get(&slot).copied())
                                .flatten()
                                .filter(|local| !unavailable_for_compaction.contains(local))
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
                    current_slot_locals.insert(slot, local);
                }
            }
        }
        activate_captured_slots_in_stmt(stmt, facts, &current_slot_locals, &mut sticky_slots);
    }

    plans
}

fn collect_promotion_group(
    block: &HirBlock,
    decl_index: usize,
    root_temp: TempId,
    facts: &ProtoPromotionFacts,
    is_reserved: &dyn Fn(TempId) -> bool,
    event_block: RootEventBlock<'_>,
) -> PromotionGroup {
    let mut temps = BTreeSet::from([root_temp]);
    let mut removable_aliases = BTreeSet::new();
    let mut touching_stmt_indices = BTreeSet::new();
    let mut pending_indices = BTreeSet::new();
    pending_indices.extend(event_block.touch_positions_from(root_temp, decl_index + 1));

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
                && !event_block.has_touch_in(*alias_temp, decl_index..future_index)
        });
        if let Some(alias_temp) = alias {
            temps.insert(alias_temp);
            removable_aliases.insert(future_index);
            pending_indices.extend(event_block.touch_positions_from(alias_temp, future_index + 1));
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
    suffix_dominance: Option<&'a [bool]>,
    facts: &'a ProtoPromotionFacts,
    closed_root_homes: BTreeSet<(usize, HomeSlotKey)>,
    safety: HirExprSafety,
}

impl LabelFlowGroupProof<'_> {
    fn group_safety(
        &self,
        decl_index: usize,
        root_temp: TempId,
        group: &PromotionGroup,
    ) -> Result<(), LabelFlowGroupFailure> {
        let Some(suffix_dominance) = self.suffix_dominance else {
            return Err(LabelFlowGroupFailure::ControlFlow);
        };
        if !suffix_dominance[decl_index] {
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
            if !self.closed_root_homes.contains(&(decl_index, home))
                && !self.facts.has_retargeted_scalar_root(root_temp)
            {
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
            if index >= self.linear_prefix_end || !self.closed_root_homes.contains(&(index, home)) {
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
        HirStmt::LocalRootRelease(_) => true,
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

fn activate_captured_slots_in_stmt(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
    current_slot_locals: &BTreeMap<HomeSlotKey, LocalId>,
    sticky_slots: &mut BTreeMap<HomeSlotKey, LocalId>,
) {
    let mut captured_slots = BTreeSet::new();
    facts.collect_captured_home_slots_in_stmt(stmt, &mut captured_slots);
    for slot in captured_slots {
        if let Some(local) = current_slot_locals.get(&slot).copied() {
            sticky_slots.insert(slot, local);
        }
    }
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

fn call_move_root_handoffs(
    block: &HirBlock,
    root_index: usize,
    root_temp: TempId,
    facts: &ProtoPromotionFacts,
    call_roots: &CallRootLifetimeIndices,
    materialized_owner_locals: &BTreeMap<(usize, HomeSlotKey), LocalId>,
) -> Option<Vec<CallMoveRootHandoff>> {
    // 是否由 call 域强制保活与是否已经物化是两份事实；scratch/debug 等 owner
    // 已建立的根也必须在同一个原 CALL/MOVE 事务中退休。
    let pairs = call_roots
        .owner_overwrites(root_index)
        .filter(|owner| {
            call_roots.owner_is_preserved(*owner)
                || materialized_owner_locals.contains_key(&(owner.root_index(), owner.home()))
        })
        .collect::<Vec<_>>();
    let own_home = facts.trusted_temp_home_slot(root_temp)?;
    let keeps_distinct_result_home = pairs.iter().all(|pair| pair.home() != own_home)
        && call_roots
            .root_homes(root_index)
            .any(|home| home == own_home);
    if pairs.is_empty() || (pairs.len() == 1 && !keeps_distinct_result_home) {
        return None;
    }

    let mut pending = BTreeMap::new();
    for pair in pairs {
        let local = materialized_owner_locals
            .get(&(pair.root_index(), pair.home()))
            .copied()?;
        if pending.insert(pair.home(), local).is_some() {
            return None;
        }
    }

    let immediate_move_homes = facts.trusted_immediate_move_write_homes(root_temp)?;
    let mut seen_homes = BTreeSet::new();
    let mut aliases = BTreeSet::from([root_temp]);
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
        // Promotion 按 canonical SSA 签发连续原 MOVE 链；当前 HIR 可能仍保留中间
        // scratch，例如 result -> copy -> first/second。沿顺序验证值身份，不要求
        // 中间 COPY 已被别的 pass 删除，也不把任意同 home 的 temp 当作同值。
        if !aliases.contains(source) {
            return None;
        }
        let home = facts.trusted_temp_home_slot(*temp)?;
        if !immediate_move_homes.contains(&home) || !seen_homes.insert(home) {
            return None;
        }
        aliases.insert(*temp);
        if let Some(local) = pending.remove(&home) {
            handoffs.push(CallMoveRootHandoff {
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

fn prune_binding_self_assigns(stmt: &mut HirStmt) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    if assign.values.tail.is_some()
        || assign.targets.len() != assign.values.fixed.len()
        || assign.initializer_merge_transaction.is_some()
        || assign.generic_for_initializer_producer.is_some()
        || assign.method_rewrite_transaction.is_some()
    {
        return false;
    }
    let mut temps = BTreeSet::new();
    let mut locals = BTreeSet::new();
    if !assign.targets.iter().all(|target| match target {
        HirLValue::Temp(temp) => temps.insert(*temp),
        HirLValue::Local(local) => locals.insert(*local),
        _ => false,
    }) || !assign.values.fixed.iter().all(|value| {
        matches!(
            value,
            HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::TempRef(_)
                | HirExpr::LocalRef(_)
                | HirExpr::ParamRef(_)
        )
    }) {
        return false;
    }
    // RHS 无调用/分配且目标不重复，去掉 x=x 不会恢复其它分量更新前的快照，
    // 也不改变观察期间的根。只删除配对分量，余下赋值保持并行。
    let keep = assign
        .targets
        .iter()
        .zip(&assign.values.fixed)
        .map(|(target, value)| {
            !matches!((target, value), (HirLValue::Temp(a), HirExpr::TempRef(b)) if a == b)
                && !matches!((target, value), (HirLValue::Local(a), HirExpr::LocalRef(b)) if a == b)
        })
        .collect::<Vec<_>>();
    if keep.iter().all(|keep| *keep) {
        return false;
    }
    let mut indices = keep.iter();
    assign.targets.retain(|_| *indices.next().unwrap());
    let mut indices = keep.iter();
    assign.values.fixed.retain(|_| *indices.next().unwrap());
    true
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

/// 原 CLOSURE 的引用自捕获读取新建 cell，而不是赋值前的值。已由前面的 touch-before
/// 检查排除外层状态写回，且原结果 Def/home 必须保持不变；ByValue 自读取仍是旧值观察。
// 引用自捕获建立初始化 cell，不是读取旧值的自更新；只有原 CLOSURE Def/home
// 与 touch-before 证明齐备才可提升，ByValue 仍须按创建点快照处理。
fn is_recursive_closure_initializer(
    stmt: &HirStmt,
    temp: TempId,
    facts: &ProtoPromotionFacts,
) -> bool {
    let Some(HirExpr::Closure(closure)) = single_temp_assign_value(stmt, temp) else {
        return false;
    };
    facts.trusted_temp_home_slot(temp).is_some()
        && closure
            .source_site
            .and_then(|site| facts.operation_result_temp(site))
            == Some(temp)
        && closure.captures.iter().any(|capture| {
            capture.binding == HirBinding::Temp(temp) && capture.mode == HirCaptureMode::ByReference
        })
        && closure.captures.iter().all(|capture| {
            capture.binding != HirBinding::Temp(temp) || capture.mode == HirCaptureMode::ByReference
        })
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
    original: &HirStmt,
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
            let generic_for_dispatch_release = match original {
                HirStmt::Assign(assign)
                    if assign.values == values
                        && assign.targets.len() == 1
                        && match assign.targets[0] {
                            HirLValue::Temp(temp) => plan.temps.contains(&temp),
                            HirLValue::Local(local) => local == plan.local,
                            _ => false,
                        } =>
                {
                    // 同一 nil 写只应用已经证明的 Temp→Local 映射，保留其原 dispatch 身份。
                    assign.generic_for_dispatch_release
                }
                _ => None,
            };
            Some(HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(plan.local)],
                values,
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                generic_for_dispatch_release,
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
    event_stmt: RootEventStmt<'_>,
) -> bool {
    match stmt {
        HirStmt::LocalRootRelease(_) => false,
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
            // 提升只替换 Temp 的绑定身份，producer occurrence 与 iterator span 不变。
            // 后续消费仍核对两端的实际 binding、home 和完整帧，不能按槽重新猜回 token。
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
                event_stmt.child(0),
                mapping,
                sticky_slots,
                outer_uses_temp,
            )
            .changed;
            let else_changed = if_stmt.else_block.as_mut().is_some_and(|else_block| {
                promote_block(
                    ctx,
                    else_block,
                    event_stmt.child(1),
                    mapping,
                    sticky_slots,
                    outer_uses_temp,
                )
                .changed
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
                event_stmt.child(0),
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
                event_stmt.child(0),
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
                event_stmt.child(0),
                mapping,
                sticky_slots,
                outer_uses_temp,
            )
            .changed;
            start_changed || limit_changed || step_changed || body_changed
        }
        HirStmt::GenericFor(generic_for) => {
            // 同一已证明的 Temp -> Local 映射同步作用于 producer 与 iterator；
            // 纯身份提升不撤销 occurrence。普通表达式改写仍走 rewrite_iterator。
            let iterator_changed = rewrite::value_pack(&mut generic_for.iterator, mapping.as_ref());
            let body_changed = promote_block(
                ctx,
                &mut generic_for.body,
                event_stmt.child(0),
                mapping,
                sticky_slots,
                outer_uses_temp,
            )
            .changed;
            iterator_changed || body_changed
        }
        HirStmt::Block(block) => {
            promote_block(
                ctx,
                block,
                event_stmt.child(0),
                mapping,
                sticky_slots,
                outer_uses_temp,
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
