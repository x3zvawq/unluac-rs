//! carried-local handoff 折叠 pass 的编排入口。
//!
//! 这个 pass 把 fallback label/goto 区域里“交棒出去的 carried 状态”认回原绑定，
//! 也会收敛结构化分支/循环里相邻的 `seed local + empty carried local`。它只负责
//! 后序遍历、外层 binding 活跃性保护，以及在当前 block 内按既定顺序调用各类 owner：
//! `adjacent.rs` 处理相邻 local seed，`boundary.rs` 索引 label/goto 边界，
//! `handoffs.rs` 处理具体 seed/update handoff，`binding.rs` 和 `prune.rs` 提供共享工具。
//!
//! 它不会发明新 local，也不会在原 local 仍然活跃时强行合并两段状态；所有折叠都必须
//! 先证明 seed 在后续不再可观察、temp 不被外层作用域消费，并且写回形状可证明。
//! captured local 也不能作为纯 alias handoff 的来源：闭包调用可能在后缀没有显式提及
//! 该 local 时写回它，跨过这类调用消除快照会改变后续读值。
//! 所有 owner 还共享 proto 级 capture/TBC 身份门：direct 资源 binding 与其 raw home
//! may-alias 都不得成为改写两端，避免先改坏 closure cell/close 身份再靠 provenance 兜底。
//!
//! 例子：
//! - 输入：`local l0 = 1; do t4 = l0; ::L1:: if t4 < 3 then t4 = t4 + 1; goto L1 end end`
//! - 输出：`local l0 = 1; do ::L1:: if l0 < 3 then l0 = l0 + 1; goto L1 end end`
//! - 输入：`assign t8, t9, t10 = t1, t2, 0; ... assign t1, t2 = t8, t9`
//! - 输出：`assign t10 = 0; ...`

mod adjacent;
mod binding;
mod boundary;
mod handoffs;
mod loop_updates;
mod prune;
mod reads;
mod region_results;
mod seeds;

use std::collections::BTreeSet;

use crate::hir::common::{HirBlock, HirProto, HirStmt, LocalId};
use crate::hir::promotion::ProtoPromotionFacts;

use super::temp_touch::{RefScopeTracker, TempTouchIndex, collect_temp_refs_by_stmt};
use super::walk::for_each_nested_block_mut;

use self::adjacent::{try_collapse_adjacent_local_seed_handoff, try_collapse_guarded_local_update};
use self::binding::{BindingProtection, bindings_may_share_raw_home_slot, carry_binding_from_expr};
pub(super) use self::binding::{CarryBinding, single_binding_copy};
use self::boundary::LabelJumpIndex;
use self::handoffs::{HandoffAction, try_collapse_handoff_at};
use self::loop_updates::collapse_dead_loop_update_handoffs;
use self::prune::prune_redundant_copy_stmts;
use self::reads::{collect_binding_mentions_by_stmt, collect_binding_mentions_in_expr};
use self::region_results::{
    RegionResultIndex, collapse_inferred_if_result_chains, collapse_result_writeback_transactions,
    collapse_written_back_if_results, try_collapse_region_result_handoff,
};
use super::mention::{stmts_captured_locals, stmts_reference_captured_bindings};
use super::visit::{HirVisitor, visit_expr, visit_stmts};

struct HandoffSafety<'a> {
    promotion_facts: &'a mut ProtoPromotionFacts,
    identity_facts: &'a HandoffIdentityFacts,
}

pub(super) fn collapse_carried_local_handoffs_in_proto(
    proto: &mut HirProto,
    promotion_facts: &mut ProtoPromotionFacts,
) -> bool {
    let identity_facts = HandoffIdentityFacts::new(proto);
    collapse_handoffs_recursive(
        &mut proto.body,
        &BTreeSet::new(),
        promotion_facts,
        &identity_facts,
        &BTreeSet::new(),
    )
}

/// 自定义后序遍历：先递归处理子块（同时把外层 binding 引用集传下去），再在当前块做
/// handoff 折叠。外层仍提及的 source 或 target 不能在当前块内被当成私有快照消除。
fn collapse_handoffs_recursive(
    block: &mut HirBlock,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
    inherited_locals: &BTreeSet<LocalId>,
) -> bool {
    let mut changed = false;
    let mut visible_locals = inherited_locals.clone();

    // 跟踪每个嵌套语句“进入该子块时需要保护的 binding 集”。
    // 对于 index 处的语句，保护集 = 继承的 outer_bindings ∪ 本块中其他语句的 mentions。
    // 注意不能用 `all - self` 来近似：如果某个 binding 同时出现在当前语句和其他语句中，
    // 差集会把它减掉，导致跨作用域的引用失去保护。这里用前缀+后缀并集来精确计算。
    let stmt_binding_refs = collect_binding_mentions_by_stmt(&block.stmts);
    let mut binding_refs = RefScopeTracker::new(&stmt_binding_refs);
    for index in 0..binding_refs.len() {
        binding_refs.enter_stmt(index);
        let repeat_cond_refs = match &block.stmts[index] {
            HirStmt::Repeat(repeat_stmt) => {
                Some(collect_binding_mentions_in_expr(&repeat_stmt.cond))
            }
            _ => None,
        };
        let child_outer = ScopedBindingProtection {
            inherited: outer_bindings,
            refs: &binding_refs,
            extra: repeat_cond_refs.as_ref(),
        };
        let mut child_locals = visible_locals.clone();
        match &block.stmts[index] {
            HirStmt::NumericFor(numeric_for) => {
                child_locals.insert(numeric_for.binding);
            }
            HirStmt::GenericFor(generic_for) => {
                child_locals.extend(generic_for.bindings.iter().copied());
            }
            _ => {}
        }

        for_each_nested_block_mut(&mut block.stmts[index], &mut |nested_block| {
            changed |= collapse_handoffs_recursive(
                nested_block,
                &child_outer,
                promotion_facts,
                identity_facts,
                &child_locals,
            );
        });

        if let HirStmt::LocalDecl(local_decl) = &block.stmts[index] {
            visible_locals.extend(local_decl.bindings.iter().copied());
        }

        binding_refs.leave_stmt(index);
    }

    // 后序：子块可能把 binding 引用改写到当前层，因此 owner 不能继续使用递归前的索引。
    let refreshed_stmt_binding_refs = collect_binding_mentions_by_stmt(&block.stmts);
    changed |= collapse_dead_loop_update_handoffs(
        block,
        &refreshed_stmt_binding_refs,
        outer_bindings,
        promotion_facts,
        identity_facts,
        inherited_locals,
    );
    changed |= collapse_block_handoffs(
        block,
        outer_bindings,
        promotion_facts,
        identity_facts,
        inherited_locals,
    );
    changed |= prune_redundant_copy_stmts(block);
    changed
}

fn collapse_block_handoffs(
    block: &mut HirBlock,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
    inherited_locals: &BTreeSet<LocalId>,
) -> bool {
    let mut changed = collapse_result_writeback_transactions(
        block,
        outer_bindings,
        promotion_facts,
        identity_facts,
        inherited_locals,
    );
    let mut captured_bindings = collect_captured_bindings(&block.stmts);
    changed |= collapse_written_back_if_results(
        block,
        outer_bindings,
        &captured_bindings,
        promotion_facts,
        identity_facts,
    );
    captured_bindings = collect_captured_bindings(&block.stmts);
    changed |= collapse_inferred_if_result_chains(
        block,
        outer_bindings,
        promotion_facts,
        &captured_bindings,
        identity_facts,
    );
    let mut index = 0;
    let mut stmt_temp_refs = collect_temp_refs_by_stmt(&block.stmts);

    loop {
        let action = {
            let temp_touches = TempTouchIndex::new(&stmt_temp_refs);
            let label_jumps = LabelJumpIndex::new(&block.stmts);
            captured_bindings = collect_captured_bindings(&block.stmts);
            let region_results = RegionResultIndex::new(&block.stmts, &captured_bindings);
            let mut action = None;
            while index < block.stmts.len() {
                if try_collapse_region_result_handoff(
                    block,
                    index,
                    outer_bindings,
                    promotion_facts,
                    &region_results,
                    identity_facts,
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
        stmt_temp_refs = collect_temp_refs_by_stmt(&block.stmts);
    }

    changed
}

struct HandoffIdentityFacts {
    debug: BTreeSet<LocalId>,
    for_bindings: BTreeSet<LocalId>,
    captured: BTreeSet<CarryBinding>,
    reference_captured: BTreeSet<CarryBinding>,
    to_be_closed: BTreeSet<CarryBinding>,
}

impl HandoffIdentityFacts {
    fn new(proto: &HirProto) -> Self {
        let debug = proto
            .locals
            .iter()
            .copied()
            .zip(&proto.local_debug_hints)
            .filter_map(|(local, hint)| hint.is_some().then_some(local))
            .collect();
        let mut collector = HandoffIdentityCollector::default();
        visit_stmts(&proto.body.stmts, &mut collector);
        Self {
            debug,
            for_bindings: collector.for_bindings,
            captured: collector.captured,
            reference_captured: collector.reference_captured,
            to_be_closed: collector.to_be_closed,
        }
    }

    fn contains(&self, local: LocalId) -> bool {
        self.debug.contains(&local) || self.for_bindings.contains(&local)
    }

    fn binding_merge_preserves_identity(
        &self,
        source: CarryBinding,
        target: CarryBinding,
        promotion_facts: &ProtoPromotionFacts,
    ) -> bool {
        !self.captured.contains(&source)
            && !self.captured.contains(&target)
            && !self.to_be_closed.contains(&source)
            && !self.to_be_closed.contains(&target)
            && self
                .reference_captured
                .iter()
                .chain(&self.to_be_closed)
                .all(|binding| {
                    !bindings_may_share_raw_home_slot(source, *binding, promotion_facts)
                        && !bindings_may_share_raw_home_slot(target, *binding, promotion_facts)
                })
    }
}

#[derive(Default)]
struct HandoffIdentityCollector {
    for_bindings: BTreeSet<LocalId>,
    captured: BTreeSet<CarryBinding>,
    reference_captured: BTreeSet<CarryBinding>,
    to_be_closed: BTreeSet<CarryBinding>,
}

impl HirVisitor for HandoffIdentityCollector {
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

    fn visit_expr(&mut self, expr: &crate::hir::common::HirExpr) {
        let crate::hir::common::HirExpr::Closure(closure) = expr else {
            return;
        };
        for capture in &closure.captures {
            visit_expr(
                &capture.value,
                &mut CapturedValueBindingCollector {
                    bindings: &mut self.captured,
                },
            );
            if capture.mode == crate::hir::common::HirCaptureMode::ByReference {
                visit_expr(
                    &capture.value,
                    &mut CapturedValueBindingCollector {
                        bindings: &mut self.reference_captured,
                    },
                );
            }
        }
    }
}

struct CapturedValueBindingCollector<'a> {
    bindings: &'a mut BTreeSet<CarryBinding>,
}

impl HirVisitor for CapturedValueBindingCollector<'_> {
    fn visit_expr(&mut self, expr: &crate::hir::common::HirExpr) {
        if let Some(binding) = carry_binding_from_expr(expr) {
            self.bindings.insert(binding);
        }
    }
}

struct ScopedBindingProtection<'scope, 'refs> {
    inherited: &'scope dyn BindingProtection,
    refs: &'scope RefScopeTracker<'refs, CarryBinding>,
    extra: Option<&'scope BTreeSet<CarryBinding>>,
}

impl BindingProtection for ScopedBindingProtection<'_, '_> {
    fn contains(&self, binding: &CarryBinding) -> bool {
        self.inherited.contains(binding)
            || self.refs.prefix_contains(*binding)
            || self.refs.suffix_contains(*binding)
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
