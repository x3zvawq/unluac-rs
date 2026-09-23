//! 编排 carried-local 交接收敛，将机械 seed/update 身份认回原状态绑定。
//!
//! 消费 promotion、binding mention 与资源身份事实，负责后序遍历、外层活跃性保护
//! 和各 handoff owner 的调度；具体证明与提交分别位于 adjacent、handoffs、
//! loop_updates、region_results 和 prune，不在入口重建它们的规则。
//! 例如 local s=1; local c; c=s; use(c) 在身份及路径证明成立时可收成
//! local s=1; use(s)，仍被外层或闭包观察的状态不得合并。

mod adjacent;
mod binding;
mod boundary;
mod coalesce;
mod handoffs;
mod loop_updates;
mod prune;
mod reads;
mod region_results;
mod repeat_snapshots;
mod seeds;

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirBlock, HirLabelId, HirProto, HirStmt, LocalId, TempId};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::ProtoPromotionFacts;

use super::label_refs::count_label_references;
use super::temp_touch::collect_temp_touch_positions;
use super::walk::for_each_nested_block_mut;

pub(super) use self::adjacent::adjacent_nil_initializer_bindings;
use self::adjacent::{try_collapse_adjacent_local_seed_handoff, try_collapse_guarded_local_update};
use self::binding::{
    BindingProtection, binding_home_slot, bindings_may_share_raw_home_slot,
    carry_binding_from_capture, carry_binding_from_expr,
};
pub(super) use self::binding::{CarryBinding, single_binding_copy};
use self::boundary::LabelJumpIndex;
use self::handoffs::{HandoffAction, try_collapse_handoff_at};
use self::loop_updates::collapse_dead_loop_update_handoffs;
use self::prune::{
    prune_dead_for_binding_temp_mirrors, prune_redundant_branch_state_copies,
    prune_redundant_copy_stmts, restore_phi_copy_writes,
};
use self::reads::{BindingMentionIndex, BlockMentions, collect_binding_mentions_in_expr};
use self::region_results::{
    RegionResultIndex, collapse_inferred_if_result_chains, collapse_result_writeback_transactions,
    collapse_written_back_if_results, try_collapse_region_result_handoff,
};
use super::mention::{stmts_captured_locals, stmts_reference_captured_bindings};
use crate::hir::visit::{HirVisitor, visit_stmts};

struct HandoffSafety<'a> {
    promotion_facts: &'a mut ProtoPromotionFacts,
    identity_facts: &'a HandoffIdentityFacts,
}

pub(super) fn collapse_carried_local_handoffs_in_proto(
    proto: &mut HirProto,
    promotion_facts: &mut ProtoPromotionFacts,
    expr_safety: HirExprSafety,
) -> bool {
    let restored_copies = restore_phi_copy_writes(proto, promotion_facts);
    let preserved_bindings = collect_preserved_bindings(proto);
    let branch_copies_changed =
        prune_redundant_branch_state_copies(proto, expr_safety, &preserved_bindings);
    let snapshots_changed = repeat_snapshots::coalesce_repeat_terminal_snapshots(
        proto,
        promotion_facts,
        &preserved_bindings,
    );
    let dead_for_binding_mirrors_changed =
        prune_dead_for_binding_temp_mirrors(proto, promotion_facts, &preserved_bindings);
    // Both structural rewrites above can remove a materialization that would otherwise be
    // recorded as an active identity.  Freeze protection facts only after those rewrites so the
    // handoff owner never reasons over a stale binding set.
    let control_facts = RegionControlFacts {
        label_refs: count_label_references(&proto.body.stmts),
        expr_safety,
    };
    let identity_facts = HandoffIdentityFacts::new(proto, promotion_facts, preserved_bindings);
    let coalesced =
        coalesce::coalesce_disjoint_temps(proto, promotion_facts, &identity_facts, expr_safety);
    let mentions = BindingMentionIndex::new(&proto.body.stmts);
    branch_copies_changed
        | restored_copies
        | coalesced
        | snapshots_changed
        | dead_for_binding_mirrors_changed
        | collapse_handoffs_recursive(
            &mut proto.body,
            &BTreeSet::new(),
            promotion_facts,
            &identity_facts,
            &control_facts,
            &mut BTreeSet::new(),
            &mut mentions.blocks(),
        )
}

/// 自定义后序遍历：先递归处理子块（同时把外层 binding 引用集传下去），再在当前块做
/// handoff 折叠。外层仍提及的 source 或 target 不能在当前块内被当成私有快照消除。
fn collapse_handoffs_recursive<'a>(
    block: &mut HirBlock,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
    control_facts: &RegionControlFacts,
    inherited_locals: &mut BTreeSet<LocalId>,
    snapshots: &mut impl Iterator<Item = BlockMentions<'a>>,
) -> bool {
    let mentions = snapshots
        .next()
        .expect("each original block has a mention snapshot");
    let mut changed = false;
    let mut introduced_locals = Vec::new();

    // 跟踪每个嵌套语句“进入该子块时需要保护的 binding 集”。
    // 对于 index 处的语句，保护集 = 继承的 outer_bindings ∪ 本块中其他语句的 mentions。
    // 注意不能用 `all - self` 来近似：如果某个 binding 同时出现在当前语句和其他语句中，
    // 差集会把它减掉，导致跨作用域的引用失去保护。这里用前缀+后缀并集来精确计算。
    for index in 0..block.stmts.len() {
        let repeat_cond_refs = match &block.stmts[index] {
            HirStmt::Repeat(repeat_stmt) => {
                Some(collect_binding_mentions_in_expr(&repeat_stmt.cond))
            }
            _ => None,
        };
        let child_outer = ScopedBindingProtection {
            inherited: outer_bindings,
            refs: mentions,
            stmt_index: index,
            extra: repeat_cond_refs.as_ref(),
        };
        let local_checkpoint = introduced_locals.len();
        let for_bindings = match &block.stmts[index] {
            HirStmt::NumericFor(numeric_for) => std::slice::from_ref(&numeric_for.binding),
            HirStmt::GenericFor(generic_for) => generic_for.bindings.as_slice(),
            _ => &[],
        };
        extend_visible_locals(inherited_locals, &mut introduced_locals, for_bindings);

        for_each_nested_block_mut(&mut block.stmts[index], &mut |nested_block| {
            changed |= collapse_handoffs_recursive(
                nested_block,
                &child_outer,
                promotion_facts,
                identity_facts,
                control_facts,
                inherited_locals,
                snapshots,
            );
        });

        for local in introduced_locals.drain(local_checkpoint..) {
            inherited_locals.remove(&local);
        }
        if let HirStmt::LocalDecl(local_decl) = &block.stmts[index] {
            extend_visible_locals(
                inherited_locals,
                &mut introduced_locals,
                &local_decl.bindings,
            );
        }
    }

    // 后序 owner 判断的是进入本块之前的可用性，不能把本块后置声明当成入口 local。
    for local in introduced_locals {
        inherited_locals.remove(&local);
    }
    // 初始快照保留给祖先和未处理的兄弟；子块改变后由实际消费者按需重建。
    changed |= collapse_dead_loop_update_handoffs(
        block,
        (!changed).then_some(mentions),
        outer_bindings,
        promotion_facts,
        identity_facts,
        inherited_locals,
        control_facts.expr_safety,
    );
    changed |= collapse_block_handoffs(
        block,
        outer_bindings,
        promotion_facts,
        identity_facts,
        control_facts,
        inherited_locals,
        control_facts.expr_safety,
    );
    changed |= prune_redundant_copy_stmts(
        block,
        &identity_facts.preserved,
        &identity_facts.call_preparations,
        &identity_facts.reference_captured,
    );
    changed
}

fn extend_visible_locals(
    visible: &mut BTreeSet<LocalId>,
    introduced: &mut Vec<LocalId>,
    bindings: &[LocalId],
) {
    for &local in bindings {
        // 同一身份可能已经由祖先声明；退出子块时只能撤销本层首次引入的身份。
        if visible.insert(local) {
            introduced.push(local);
        }
    }
}

fn collapse_block_handoffs(
    block: &mut HirBlock,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
    control_facts: &RegionControlFacts,
    inherited_locals: &BTreeSet<LocalId>,
    expr_safety: HirExprSafety,
) -> bool {
    let mut changed = collapse_result_writeback_transactions(
        block,
        outer_bindings,
        promotion_facts,
        identity_facts,
        control_facts,
        inherited_locals,
    );
    changed |= collapse_written_back_if_results(
        block,
        outer_bindings,
        promotion_facts,
        identity_facts,
        control_facts,
    );
    changed |= collapse_inferred_if_result_chains(
        block,
        outer_bindings,
        promotion_facts,
        identity_facts,
        control_facts,
    );
    let mut index = 0;
    let mut captured_bindings;

    loop {
        let action = {
            let temp_touches = collect_temp_touch_positions(&block.stmts);
            let label_jumps = LabelJumpIndex::new(&block.stmts);
            captured_bindings = collect_captured_bindings(&block.stmts);
            let region_results = RegionResultIndex::new(&block.stmts);
            let mut action = None;
            while index < block.stmts.len() {
                if try_collapse_region_result_handoff(
                    block,
                    index,
                    outer_bindings,
                    promotion_facts,
                    &region_results,
                    identity_facts,
                    control_facts,
                ) {
                    action = Some(HandoffAction::RetrySameIndex);
                    break;
                }
                if try_collapse_guarded_local_update(
                    block,
                    index,
                    outer_bindings,
                    &captured_bindings,
                    promotion_facts,
                    identity_facts,
                ) {
                    action = Some(HandoffAction::RetrySameIndex);
                    break;
                }
                if try_collapse_adjacent_local_seed_handoff(
                    block,
                    index,
                    promotion_facts,
                    identity_facts,
                    expr_safety,
                ) {
                    action = Some(HandoffAction::RetrySameIndex);
                    break;
                }
                let mut safety = HandoffSafety {
                    promotion_facts,
                    identity_facts,
                };
                if let Some(handoff_action) = try_collapse_handoff_at(
                    block,
                    index,
                    outer_bindings,
                    &temp_touches,
                    &label_jumps,
                    &captured_bindings,
                    &mut safety,
                ) {
                    action = Some(handoff_action);
                    break;
                }

                index += 1;
            }
            action
        };

        let Some(action) = action else {
            break;
        };
        changed = true;
        if matches!(action, HandoffAction::AdvanceIndex) {
            index += 1;
        }
    }

    changed
}

struct RegionControlFacts {
    // Region-result candidates are slices of nested owners.  Proto-wide reference counts let
    // LexicalCfg distinguish an internal label cycle from an entry originating outside the slice.
    label_refs: BTreeMap<HirLabelId, usize>,
    expr_safety: HirExprSafety,
}

struct HandoffIdentityFacts {
    debug: BTreeSet<LocalId>,
    for_bindings: BTreeSet<LocalId>,
    physical_roots: BTreeSet<CarryBinding>,
    reference_captured: BTreeSet<CarryBinding>,
    to_be_closed: BTreeSet<CarryBinding>,
    preserved: BTreeSet<CarryBinding>,
    call_preparations: BTreeSet<(CarryBinding, CarryBinding)>,
}

impl HandoffIdentityFacts {
    fn new(
        proto: &HirProto,
        promotion_facts: &ProtoPromotionFacts,
        preserved: BTreeSet<CarryBinding>,
    ) -> Self {
        let debug = (0..proto.local_count)
            .map(LocalId)
            .zip(&proto.local_debug_hints)
            .filter_map(|(local, hint)| hint.is_some().then_some(local))
            .collect();
        let mut collector = HandoffIdentityCollector::default();
        visit_stmts(&proto.body.stmts, &mut collector);
        Self {
            debug,
            for_bindings: collector.for_bindings,
            physical_roots: proto
                .physical_root_locals
                .iter()
                .copied()
                .map(CarryBinding::Local)
                .chain(
                    proto
                        .physical_root_temps
                        .iter()
                        .copied()
                        .map(CarryBinding::Temp),
                )
                .collect(),
            reference_captured: collector.reference_captured,
            to_be_closed: collector.to_be_closed,
            preserved,
            call_preparations: promotion_facts
                .call_preparation_local_copies()
                .map(|(target, source)| (CarryBinding::Local(target), CarryBinding::Local(source)))
                .collect(),
        }
    }

    fn contains(&self, local: LocalId) -> bool {
        self.debug.contains(&local)
            || self.for_bindings.contains(&local)
            || self.physical_roots.contains(&CarryBinding::Local(local))
            || self.preserved.contains(&CarryBinding::Local(local))
    }

    fn binding_merge_preserves_identity(
        &self,
        source: CarryBinding,
        target: CarryBinding,
        promotion_facts: &ProtoPromotionFacts,
    ) -> bool {
        self.binding_merge_preserves_identity_with_nil_target(
            source,
            target,
            promotion_facts,
            false,
        )
    }

    /// 相邻 nil initializer 原位保留；只退休后面的空 carrier 声明，不退休目标根。
    fn binding_merge_preserves_identity_with_nil_target(
        &self,
        source: CarryBinding,
        target: CarryBinding,
        promotion_facts: &ProtoPromotionFacts,
        retains_nil_target: bool,
    ) -> bool {
        self.binding_merge_preserves_retained_target(
            source,
            target,
            promotion_facts,
            retains_nil_target,
            false,
        )
    }

    // 原同槽结果写入继续使用已有 target；只有 synthetic phi 写回可以退休。
    // 调用方还须证明完整路径上的写回关系，不能凭同槽提前覆盖旧 target。
    fn binding_merge_preserves_retained_target(
        &self,
        source: CarryBinding,
        target: CarryBinding,
        promotion_facts: &ProtoPromotionFacts,
        retains_nil_target: bool,
        retains_phi_target: bool,
    ) -> bool {
        let shares_exact_home = binding_home_slot(source, promotion_facts)
            .zip(binding_home_slot(target, promotion_facts))
            .is_some_and(|(source, target)| source == target);
        let retains_target = (retains_nil_target || retains_phi_target) && shares_exact_home;
        let endpoint_is_reference_captured =
            self.reference_captured.contains(&source) || self.reference_captured.contains(&target);
        // 候选拒绝[PolicyBoundary]：debug binding 是项目选择保留的源码身份。
        // 候选拒绝[SemanticBarrier:Scope]：for binding 每轮重建且只在 loop body 可见；
        // 与外层/跨轮 binding 合并会改变迭代 refresh 和词法作用域。
        // 候选拒绝[SemanticBarrier:Lifetime]：把 physical-root result 合并到 state 会删除其 VM root declaration；lua54_01_close#17 用 __gc + collectgarbage 观察同槽清空前的对象若失去该 root 会提前析构。
        // 候选拒绝[SemanticBarrier:Capture]：reference-captured endpoint 只有在两端缺少
        // 同一 `(slot, close epoch)` 证明时才是不同 cell；同一 exact home 指向同一 VM
        // upvalue cell。其它 may-alias reference capture 仍需保守保护，因为它不在本次
        // rewrite map 内。By-value capture 只是创建点快照，其值等价性由 transaction 的
        // reaching relation 验证。
        // 候选拒绝[SemanticBarrier:Lifetime]：TBC 任一端或 raw-home may-alias resource binding 时，合并会改变 close/root epoch。
        // 候选拒绝[LayerBoundary]：HIR 已证明必须保留的 binding definition 不得被
        // carried-local 的跨身份 merge 删除；不相关 Preserve 不影响当前事务。
        !self.preserved.contains(&source)
            && (retains_target || !self.preserved.contains(&target))
            && !self.physical_roots.contains(&source)
            && (retains_target || !self.physical_roots.contains(&target))
            && !source.local().is_some_and(|local| self.contains(local))
            && !target.local().is_some_and(|local| {
                if retains_target {
                    (!retains_phi_target && self.debug.contains(&local))
                        || self.for_bindings.contains(&local)
                } else {
                    self.contains(local)
                }
            })
            && (!endpoint_is_reference_captured || shares_exact_home)
            && !self.to_be_closed.contains(&source)
            && !self.to_be_closed.contains(&target)
            && self
                .reference_captured
                .iter()
                .filter(|binding| **binding != source && **binding != target)
                .chain(&self.to_be_closed)
                .all(|binding| {
                    !bindings_may_share_raw_home_slot(source, *binding, promotion_facts)
                        && !bindings_may_share_raw_home_slot(target, *binding, promotion_facts)
                })
    }
}

fn collect_preserved_bindings(proto: &HirProto) -> BTreeSet<CarryBinding> {
    (0..proto.temp_count)
        .map(TempId)
        .filter(|temp| proto.inline_dispositions.temp(*temp).must_preserve())
        .map(CarryBinding::Temp)
        .chain(
            (0..proto.local_count)
                .map(LocalId)
                .filter(|local| proto.inline_dispositions.local(*local).must_preserve())
                .map(CarryBinding::Local),
        )
        .collect()
}

#[derive(Default)]
struct HandoffIdentityCollector {
    for_bindings: BTreeSet<LocalId>,
    reference_captured: BTreeSet<CarryBinding>,
    to_be_closed: BTreeSet<CarryBinding>,
}

impl HirVisitor<'_> for HandoffIdentityCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::NumericFor(numeric_for) => {
                self.for_bindings.insert(numeric_for.binding);
            }
            HirStmt::GenericFor(generic_for) => {
                self.for_bindings
                    .extend(generic_for.bindings.iter().copied());
            }
            HirStmt::ToBeClosed(to_be_closed) => {
                if let Some(binding) = carry_binding_from_expr(&to_be_closed.value) {
                    self.to_be_closed.insert(binding);
                }
            }
            _ => {}
        }
    }

    fn visit_capture(&mut self, capture: &crate::hir::HirCapture) {
        if capture.mode == crate::hir::HirCaptureMode::ByReference
            && let Some(binding) = carry_binding_from_capture(capture.binding)
        {
            self.reference_captured.insert(binding);
        }
    }
}

struct ScopedBindingProtection<'scope> {
    inherited: &'scope dyn BindingProtection,
    refs: BlockMentions<'scope>,
    stmt_index: usize,
    extra: Option<&'scope BTreeSet<CarryBinding>>,
}

impl BindingProtection for ScopedBindingProtection<'_> {
    fn contains(&self, binding: &CarryBinding) -> bool {
        self.inherited.contains(binding)
            || self.refs.outside_stmt(self.stmt_index, *binding)
            || self.extra.is_some_and(|extra| extra.contains(binding))
    }
}

fn collect_captured_bindings(stmts: &[HirStmt]) -> BTreeSet<CarryBinding> {
    let captured = stmts_reference_captured_bindings(stmts);
    let mut bindings = stmts_captured_locals(stmts)
        .into_iter()
        .map(CarryBinding::Local)
        .collect::<BTreeSet<_>>();
    bindings.extend(captured.params.into_iter().map(CarryBinding::Param));
    bindings.extend(captured.temps.into_iter().map(CarryBinding::Temp));
    bindings
}
