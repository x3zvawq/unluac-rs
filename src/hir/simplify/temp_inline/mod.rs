//! 这个文件实现 HIR 的第一批 temp inlining。
//!
//! 我们故意把规则收得很保守：常规路径只折叠“单目标 temp 赋值，并且被紧邻下一条
//! 简单语句使用一次”的情况。调用表达式另有一条更窄的连续融合规则，用来处理
//! `callee_temp = f; arg_temp = expr; callee_temp(arg_temp)` 这种 bytecode 为保持 Lua
//! “先求 callee、再求参数”而拆出的形状；融合时必须把 callee 和参数一起放回同一条
//! call，不能只把 callee 延后到参数求值之后。run 中无读取且可安全丢弃的匿名 temp
//! 不构成求值事件，但带 debug/capture 身份的赋值仍会阻断整包融合。
//! 同一 block 的独立 run 沿进入本函数时的语句索引批量判定：sink 原位改写，删除区间
//! 延迟到扫描结束后一次压缩，使 capture 与求值顺序快照始终处在同一坐标系。
//! order-sensitive def 索引由 proto 级 scratch 复用，每个 block 只清理上次实际写过的槽，
//! 避免结构块数量与全局 temp 数相乘的稠密初始化成本。
//! 相邻内联以可观察事件前缀而非语法子节点顺序判定：纯 local/param 读取本身不是
//! 屏障，但读取结果形成的 temp 快照不能越过可能改写 binding 的事件；lookup、调用、
//! 运算和 method sugar 的隐式 lookup 是屏障。while/repeat 条件还属于每轮重新求值的
//! 独立区域，不能接收循环外快照。跨边界折叠只有三个窄合同：repeat body 尾写入与
//! until 属于同一轮；open return 的 fixed alias 必须先于完整保留的 tail setup；PUC
//! Lua 5.2–5.5 的单 upvalue table 左值可把相邻 producer 收回 key。三项仍要求唯一消费
//! 且不绕过原求值点；前两项不允许相关 home 被跨越区间写入或 capture，table key 则
//! 继续服从内部前缀顺序证明。
//! numeric-for 前的连续 materialization run 还允许越过保留下来的状态赋值收回稳定字面量
//! header temp；例如 `t0 = 1; t1 = 3; state = seed; for i = t0, t1` 会恢复成
//! `state = seed; for i = 1, 3`。非字面量仍走相邻求值顺序证明，不跨状态赋值猜快照。
//! closure 的复杂度无法代表 child proto 函数体，因此不把 closure producer 内联进 loop head；
//! 普通 `local function iter()` 应保留为独立声明，避免生成多行匿名 iterator。
//! method 协议的 callee base 与隐式首参虽是两个语法 use，却只求值一次 receiver；相邻
//! 裸 binding 或命名字段链快照可在严格匹配这对 use 后原子收回，例如
//! `t = subject.worker; t:touch()` 会恢复成 `subject.worker:touch()`；普通点调用仍按两次读取处理。
//! branch-values 的定向入口只重用同一证明去处理本轮新暴露的根级 global-call run 或
//! 单值 terminal return，不递归，也不开放其它普通内联 site。

mod rewrite;
mod site;
mod usage;

use std::collections::BTreeSet;

use crate::ast::{DecompileDialect, ReadabilityOptions};
use crate::hir::common::{
    HirBlock, HirCallExpr, HirExpr, HirLValue, HirProto, HirStmt, HirTableField, HirTableKey,
    TempId,
};
use crate::hir::expr_safety::{
    expr_is_discard_safe, expr_observes_eval_order, expr_requires_ordered_snapshot,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use self::rewrite::replace_temp_in_stmt;
use self::site::{
    InlineSite, expr_touches_temp, fastcall_callee_materialization_precedes_temp,
    inline_site_in_repeat_condition, inline_site_in_stmt, is_method_receiver_snapshot,
    is_stable_inline_value, puc_upvalue_table_key_with_deferred_base_read,
    temp_precedes_observable_eval_in_expr, temp_precedes_observable_eval_in_stmt,
};
use self::usage::{
    TempUseScratch, collect_expr_temp_uses_summary, collect_stmt_temp_uses, inline_candidate,
    max_temp_index_in_block,
};
use super::mention::{ReferenceCapturedBindings, stmt_writes_temp};
use super::temp_touch::stmt_contains_nested_nonlocal_control;

const NESTED_INLINE_MAX_COMPLEXITY: usize = 5;
const CONTROL_HEAD_INLINE_MAX_COMPLEXITY: usize = 5;
// 限制人工 chunk 的超长单 run 反复扫描 growing sink；这不是 VM 参数上限。
// 超限只放弃可读性融合，原 temp 与求值语义保持不变。
const CALL_MATERIALIZATION_SINK_REWRITE_BUDGET: usize = 1024;

struct TempInlineWorkspace {
    uses: TempUseScratch,
    order_sensitive_defs: OrderSensitiveDefWorkspace,
    scope: TempInlineScope,
    dialect: DecompileDialect,
}

enum TempInlineScope {
    All,
    BranchValueSinks(Vec<bool>),
}

impl TempInlineScope {
    fn allows_open_return(&self) -> bool {
        matches!(self, Self::All)
    }

    fn allows_adjacent(
        &self,
        temp: TempId,
        site: InlineSite,
        next_stmt: &HirStmt,
        is_block_terminal: bool,
    ) -> bool {
        let Self::BranchValueSinks(exposed) = self else {
            return true;
        };
        exposed.get(temp.index()).copied().unwrap_or(false)
            && site == InlineSite::ReturnValue
            && is_block_terminal
            && matches!(
                next_stmt,
                HirStmt::Return(ret)
                    if ret.values.tail.is_none()
                        && matches!(ret.values.fixed.as_slice(),
                            [HirExpr::TempRef(result)] if *result == temp)
            )
    }

    fn allows_call(
        &self,
        call_stmt: &crate::hir::common::HirCallStmt,
        callee_value: &HirExpr,
        terminal_candidate: Option<TempId>,
        sink: &HirStmt,
    ) -> bool {
        let Self::BranchValueSinks(exposed) = self else {
            return true;
        };
        !call_stmt.call.method
            && call_stmt.call.method_name.is_none()
            && matches!(callee_value, HirExpr::GlobalRef(_))
            && terminal_candidate.is_some_and(|temp| {
                exposed.get(temp.index()).copied().unwrap_or(false)
                    && inline_site_in_stmt(sink, temp).is_some()
            })
    }
}

impl TempInlineWorkspace {
    fn new(
        proto: &HirProto,
        temp_count: usize,
        scope: TempInlineScope,
        dialect: DecompileDialect,
    ) -> Self {
        Self {
            uses: TempUseScratch::new(proto, temp_count),
            order_sensitive_defs: OrderSensitiveDefWorkspace::new(temp_count),
            scope,
            dialect,
        }
    }
}

pub(super) fn inline_temps_in_proto_with_facts(
    proto: &mut HirProto,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> bool {
    inline_temps_in_proto_with_scope(proto, readability, facts, TempInlineScope::All, dialect)
}

pub(super) fn inline_exposed_branch_value_sinks_in_proto_with_facts(
    proto: &mut HirProto,
    exposed_temps: &[TempId],
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) {
    if exposed_temps.is_empty() {
        return;
    }
    let exposed_len = exposed_temps
        .iter()
        .map(|temp| temp.index())
        .max()
        .expect("non-empty exposed temp set must have a maximum")
        + 1;
    let mut exposed = vec![false; exposed_len];
    for temp in exposed_temps {
        exposed[temp.index()] = true;
    }
    inline_temps_in_proto_with_scope(
        proto,
        readability,
        facts,
        TempInlineScope::BranchValueSinks(exposed),
        dialect,
    );
}

fn inline_temps_in_proto_with_scope(
    proto: &mut HirProto,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    scope: TempInlineScope,
    dialect: DecompileDialect,
) -> bool {
    let temp_count = temp_count_for_proto(proto);
    let mut workspace = TempInlineWorkspace::new(proto, temp_count, scope, dialect);
    let mut live_use_counts = collect_block_temp_use_totals(&proto.body.stmts, &mut workspace.uses);
    let reference_captured = super::mention::stmts_reference_captured_bindings(&proto.body.stmts);
    inline_temps_in_block(
        &mut proto.body,
        &mut workspace,
        &mut live_use_counts,
        &reference_captured,
        readability,
        facts,
        &BTreeSet::new(),
    )
}

fn temp_count_for_proto(proto: &HirProto) -> usize {
    let proto_temp_count = proto
        .temps
        .iter()
        .map(|temp| temp.index())
        .max()
        .map_or(0, |max_index| max_index + 1);
    let body_temp_count = max_temp_index_in_block(&proto.body).map_or(0, |max_index| max_index + 1);
    proto_temp_count.max(body_temp_count)
}

fn inline_temps_in_block(
    block: &mut HirBlock,
    workspace: &mut TempInlineWorkspace,
    live_use_counts: &mut [usize],
    reference_captured: &ReferenceCapturedBindings,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    inherited_captured_slots: &BTreeSet<HomeSlotKey>,
) -> bool {
    let mut changed = false;
    let mut captured_slots_before_stmt =
        CapturedSlotSnapshots::new(block.stmts.len(), inherited_captured_slots);
    let mut active_captured_slots = inherited_captured_slots.clone();

    for index in 0..block.stmts.len() {
        captured_slots_before_stmt.push(&active_captured_slots);
        if matches!(workspace.scope, TempInlineScope::All) {
            let mut nested_captured_slots = active_captured_slots.clone();
            facts.collect_prefix_captured_home_slots_in_stmt(
                &block.stmts[index],
                &mut nested_captured_slots,
            );
            changed |= inline_temps_in_nested_blocks(
                &mut block.stmts[index],
                workspace,
                live_use_counts,
                reference_captured,
                readability,
                facts,
                &nested_captured_slots,
            );
        }
        let stmt = &block.stmts[index];
        facts.collect_captured_home_slots_in_stmt(stmt, &mut active_captured_slots);
    }

    if inline_materialization_runs(
        block,
        workspace,
        live_use_counts,
        facts,
        &captured_slots_before_stmt,
        reference_captured,
    ) {
        changed = true;
        captured_slots_before_stmt =
            captured_slots_before_stmts(block, facts, inherited_captured_slots);
    }

    // proto 级 live use count 会随成功内联同步减少；当前 block 只需保留下一条
    // 语句和 callee 物化位置。这既保留相邻内联边界，也避免每个 nested block
    // 重新遍历整棵子树。fallback 回边上任何额外读取都会使 live count 大于 1，
    // 因此不会被当成可删的 forwarding temp。
    let mut kept_rev = Vec::with_capacity(block.stmts.len());
    let mut callee_materialized_at = None;

    for (index, stmt) in std::mem::take(&mut block.stmts)
        .into_iter()
        .enumerate()
        .rev()
    {
        if let Some((temp, value)) = inline_candidate(&stmt)
            && !workspace.uses.has_debug_local_hint(temp)
            && !temp_rebinds_captured_slot(
                temp,
                facts,
                captured_slots_before_stmt
                    .get(index)
                    .expect("forward scan should record every statement"),
            )
            // `t = t + step` 这类自更新赋值表面上只在后缀里被用了一次，
            // 但它本质上承载的是跨语句/跨迭代的状态推进。
            // 一旦把它内联进下一条 `yield/return/call`，当前赋值本身就会消失，
            // 后续再也没有地方记录“状态已经更新过”。
            // 因此这里只允许折叠真正的 forwarding temp，不折叠自引用状态槽位。
            && !expr_touches_temp(value, temp)
            && let Some(next_stmt) = kept_rev.last()
            && let use_count = total_use_count(temp, live_use_counts)
            && (use_count == 1
                || (use_count == 2
                    && is_method_receiver_snapshot(next_stmt, temp, value)))
            && let Some(site) = inline_site_in_stmt(next_stmt, temp)
            && workspace
                .scope
                .allows_adjacent(temp, site, next_stmt, kept_rev.len() == 1)
            && !call_arg_inline_crosses_materialized_callee(
                site,
                value,
                index,
                callee_materialized_at,
            )
            && !inline_crosses_evaluation_boundary(
                site,
                value,
                next_stmt,
                temp,
                reference_captured,
                workspace.dialect,
            )
            && site.allows(value, readability)
        {
            let next_stmt = kept_rev
                .last_mut()
                .expect("next stmt metadata must track the last kept stmt");
            replace_temp_in_stmt(next_stmt, temp, value);
            if site.is_call_callee() {
                callee_materialized_at = Some(index);
            }
            remove_live_use(live_use_counts, temp);
            if use_count == 2 {
                // method receiver 会把 replacement 同时写入 callee base 与隐式首参；
                // 删除原赋值只抵消其中一份，因此需把新增的语法 use 记回本轮计数。
                collect_expr_temp_uses_summary(value, &mut workspace.uses)
                    .add_to_totals(live_use_counts);
                remove_live_use(live_use_counts, temp);
            }
            changed = true;
            continue;
        }

        // FASTCALL fallback callee 在参数后物化，收回 callee 后仍可按协议折叠相邻末参数；普通调用保留原顺序屏障。
        callee_materialized_at =
            kept_rev
                .last()
                .and_then(inline_candidate)
                .and_then(|(next_temp, _)| {
                    fastcall_callee_materialization_precedes_temp(&stmt, next_temp).then_some(index)
                });
        kept_rev.push(stmt);
    }

    kept_rev.reverse();
    block.stmts = kept_rev;

    changed
}

fn inline_crosses_evaluation_boundary(
    site: InlineSite,
    value: &HirExpr,
    next_stmt: &HirStmt,
    temp: TempId,
    reference_captured: &ReferenceCapturedBindings,
    dialect: DecompileDialect,
) -> bool {
    fixed_return_tail_call_prefers_materialization(site, value, next_stmt, temp)
        || (site == InlineSite::LoopCondition && !is_stable_inline_value(value))
        || (expr_requires_ordered_snapshot(value)
            && !puc_upvalue_table_key_with_deferred_base_read(site, next_stmt, dialect)
                .is_some_and(|key| {
                    temp_precedes_observable_eval_in_expr(
                        key,
                        temp,
                        expr_observes_eval_order(value),
                        reference_captured,
                    )
                })
            && !temp_precedes_observable_eval_in_stmt(
                next_stmt,
                temp,
                expr_observes_eval_order(value),
                reference_captured,
            ))
}

fn fixed_return_tail_call_prefers_materialization(
    site: InlineSite,
    value: &HirExpr,
    next_stmt: &HirStmt,
    temp: TempId,
) -> bool {
    let HirStmt::Return(ret) = next_stmt else {
        return false;
    };
    site == InlineSite::ReturnValue
        && ret.values.tail.is_none()
        && ret.values.expr_len() > 1
        && matches!(value, HirExpr::Call(_))
        && matches!(ret.values.last(), Some(HirExpr::TempRef(tail)) if *tail == temp)
}

fn captured_slots_before_stmts(
    block: &HirBlock,
    facts: &ProtoPromotionFacts,
    inherited_captured_slots: &BTreeSet<HomeSlotKey>,
) -> CapturedSlotSnapshots {
    let mut snapshots = CapturedSlotSnapshots::new(block.stmts.len(), inherited_captured_slots);
    let mut active_captured_slots = inherited_captured_slots.clone();
    for stmt in &block.stmts {
        snapshots.push(&active_captured_slots);
        facts.collect_captured_home_slots_in_stmt(stmt, &mut active_captured_slots);
    }
    snapshots
}

struct CapturedSlotSnapshots {
    snapshots: Vec<BTreeSet<HomeSlotKey>>,
    before_stmt: Vec<usize>,
}

impl CapturedSlotSnapshots {
    fn new(stmt_count: usize, inherited: &BTreeSet<HomeSlotKey>) -> Self {
        Self {
            snapshots: vec![inherited.clone()],
            before_stmt: Vec::with_capacity(stmt_count),
        }
    }

    fn push(&mut self, active: &BTreeSet<HomeSlotKey>) {
        if self.snapshots.last().is_none_or(|last| last != active) {
            self.snapshots.push(active.clone());
        }
        self.before_stmt.push(self.snapshots.len() - 1);
    }

    fn get(&self, stmt_index: usize) -> Option<&BTreeSet<HomeSlotKey>> {
        self.before_stmt
            .get(stmt_index)
            .and_then(|snapshot_index| self.snapshots.get(*snapshot_index))
    }
}

fn inline_materialization_runs(
    block: &mut HirBlock,
    workspace: &mut TempInlineWorkspace,
    live_use_counts: &mut [usize],
    facts: &ProtoPromotionFacts,
    captured_slots_before_stmt: &CapturedSlotSnapshots,
    reference_captured: &ReferenceCapturedBindings,
) -> bool {
    // child block 已全部处理完才会到这里，因此同一个 proto 级 workspace 不会覆盖
    // 仍在活跃递归 frame 中的 parent 索引。
    let TempInlineWorkspace {
        uses,
        order_sensitive_defs,
        scope,
        dialect,
    } = workspace;
    order_sensitive_defs.rebuild(&block.stmts);
    let mut removed_stmts = vec![false; block.stmts.len()];
    let mut changed = false;
    let mut index = 0;

    while index < block.stmts.len() {
        if inline_candidate(&block.stmts[index]).is_none() {
            index += 1;
            continue;
        }
        let run_start = index;
        let mut run_end = run_start + 1;
        while run_end < block.stmts.len() && inline_candidate(&block.stmts[run_end]).is_some() {
            run_end += 1;
        }
        if scope.allows_open_return()
            && inline_open_return_fixed_alias_run(
                block,
                run_start..run_end,
                uses,
                live_use_counts,
                facts,
                captured_slots_before_stmt,
                &mut removed_stmts,
            )
        {
            changed = true;
            index = run_end + 1;
            continue;
        }
        if inline_numeric_for_stable_header_aliases(
            block,
            run_start..run_end,
            uses,
            live_use_counts,
            facts,
            captured_slots_before_stmt,
            &mut removed_stmts,
        ) {
            changed = true;
            index = run_end + 1;
            continue;
        }
        let Some(HirStmt::CallStmt(call_stmt)) = block.stmts.get(run_end) else {
            index = run_end;
            continue;
        };
        let HirExpr::TempRef(callee_temp) = call_stmt.call.callee else {
            index = run_end + 1;
            continue;
        };
        let Some(callee_index) = (run_start..run_end).find(|candidate_index| {
            inline_candidate(&block.stmts[*candidate_index])
                .is_some_and(|(candidate, _)| candidate == callee_temp)
        }) else {
            index = run_end + 1;
            continue;
        };
        let Some((_, callee_value)) = inline_candidate(&block.stmts[callee_index]) else {
            index = run_end + 1;
            continue;
        };
        let terminal_candidate = block.stmts[..run_end]
            .last()
            .and_then(inline_candidate)
            .map(|(temp, _)| temp);
        if !scope.allows_call(
            call_stmt,
            callee_value,
            terminal_candidate,
            &block.stmts[run_end],
        ) {
            index = run_end + 1;
            continue;
        }
        if !materialization_run_candidate_is_safe(
            callee_temp,
            callee_value,
            callee_index,
            uses,
            facts,
            captured_slots_before_stmt,
        ) || total_use_count(callee_temp, live_use_counts) != 1
        {
            index = run_end + 1;
            continue;
        }

        let mut rewritten_sink = block.stmts[run_end].clone();
        let mut removed_temps = Vec::with_capacity(run_end - callee_index);
        let mut discarded_uses = Vec::new();
        let mut complete_run = true;
        let mut sink_rewrite_count = 0;
        for candidate_index in ((callee_index + 1)..run_end).rev() {
            let Some((temp, value)) = inline_candidate(&block.stmts[candidate_index]) else {
                complete_run = false;
                break;
            };
            let use_count = total_use_count(temp, live_use_counts);
            if use_count > 1 {
                complete_run = false;
                break;
            }
            let candidate_is_safe = materialization_run_candidate_is_safe(
                temp,
                value,
                candidate_index,
                uses,
                facts,
                captured_slots_before_stmt,
            );
            if use_count == 0 {
                if candidate_is_safe && expr_is_discard_safe(value) {
                    discarded_uses.push(collect_expr_temp_uses_summary(value, uses));
                    continue;
                }
                complete_run = false;
                break;
            }
            if sink_rewrite_count >= CALL_MATERIALIZATION_SINK_REWRITE_BUDGET {
                complete_run = false;
                break;
            }
            sink_rewrite_count += 1;
            let Some(site) = inline_site_in_stmt(&rewritten_sink, temp) else {
                complete_run = false;
                break;
            };
            if !candidate_is_safe
                || arg_value_forwards_prior_order_sensitive_expr(
                    value,
                    callee_index,
                    order_sensitive_defs,
                )
                || inline_crosses_evaluation_boundary(
                    site,
                    value,
                    &rewritten_sink,
                    temp,
                    reference_captured,
                    *dialect,
                )
            {
                complete_run = false;
                break;
            }
            replace_temp_in_stmt(&mut rewritten_sink, temp, value);
            removed_temps.push(temp);
        }
        if !complete_run {
            index = run_end + 1;
            continue;
        }
        let Some(callee_site) = inline_site_in_stmt(&rewritten_sink, callee_temp) else {
            index = run_end + 1;
            continue;
        };
        if !callee_site.is_call_callee()
            || inline_crosses_evaluation_boundary(
                callee_site,
                callee_value,
                &rewritten_sink,
                callee_temp,
                reference_captured,
                *dialect,
            )
        {
            index = run_end + 1;
            continue;
        }
        replace_temp_in_stmt(&mut rewritten_sink, callee_temp, callee_value);
        removed_temps.push(callee_temp);

        block.stmts[run_end] = rewritten_sink;
        removed_stmts[callee_index..run_end].fill(true);
        remove_live_use(live_use_counts, callee_temp);
        for temp in removed_temps
            .into_iter()
            .filter(|temp| *temp != callee_temp)
        {
            remove_live_use(live_use_counts, temp);
        }
        for uses in discarded_uses {
            uses.subtract_from_totals(live_use_counts);
        }
        changed = true;
        // 语句仍保留原索引，后续 run 可以继续复用进入本函数前冻结的 capture 与
        // order-sensitive def 快照；压缩只能在整次扫描结束后统一发生。
        index = run_end + 1;
    }

    if changed {
        let mut index = 0;
        block.stmts.retain(|_| {
            let keep = !removed_stmts[index];
            index += 1;
            keep
        });
    }
    changed
}

fn inline_numeric_for_stable_header_aliases(
    block: &mut HirBlock,
    run: std::ops::Range<usize>,
    scratch: &TempUseScratch,
    live_use_counts: &mut [usize],
    facts: &ProtoPromotionFacts,
    captured_slots_before_stmt: &CapturedSlotSnapshots,
    removed_stmts: &mut [bool],
) -> bool {
    let (run_start, run_end) = (run.start, run.end);
    if !matches!(block.stmts.get(run_end), Some(HirStmt::NumericFor(_))) {
        return false;
    }

    let mut rewritten_sink = block.stmts[run_end].clone();
    let mut changed = false;
    for (candidate_index, removed) in removed_stmts
        .iter_mut()
        .enumerate()
        .take(run_end)
        .skip(run_start)
    {
        let Some((temp, value)) = inline_candidate(&block.stmts[candidate_index]) else {
            continue;
        };
        if !is_stable_inline_value(value)
            || total_use_count(temp, live_use_counts) != 1
            || !materialization_run_candidate_is_safe(
                temp,
                value,
                candidate_index,
                scratch,
                facts,
                captured_slots_before_stmt,
            )
            || inline_site_in_stmt(&rewritten_sink, temp) != Some(InlineSite::LoopHead)
        {
            continue;
        }
        replace_temp_in_stmt(&mut rewritten_sink, temp, value);
        *removed = true;
        remove_live_use(live_use_counts, temp);
        changed = true;
    }
    if changed {
        block.stmts[run_end] = rewritten_sink;
    }
    changed
}

fn inline_open_return_fixed_alias_run(
    block: &mut HirBlock,
    run: std::ops::Range<usize>,
    scratch: &TempUseScratch,
    live_use_counts: &mut [usize],
    facts: &ProtoPromotionFacts,
    captured_slots_before_stmt: &CapturedSlotSnapshots,
    removed_stmts: &mut [bool],
) -> bool {
    let (run_start, run_end) = (run.start, run.end);
    let Some(HirStmt::Return(ret)) = block.stmts.get(run_end) else {
        return false;
    };
    let Some(tail) = ret.values.tail.as_ref() else {
        return false;
    };
    if tail.exact_width().is_some() || !matches!(tail.as_expr(), HirExpr::Call(_)) {
        return false;
    }
    let alias_count = ret.values.fixed.len();
    if alias_count == 0 || alias_count >= run_end - run_start {
        return false;
    }

    let Some(captured_slots) = captured_slots_before_stmt.get(run_end) else {
        return false;
    };
    let mut target_slots = BTreeSet::new();
    let mut source_slots = BTreeSet::new();
    for (stmt, fixed) in block.stmts[run_start..(run_start + alias_count)]
        .iter()
        .zip(&ret.values.fixed)
    {
        let Some((target, HirExpr::TempRef(source))) = inline_candidate(stmt) else {
            return false;
        };
        if !matches!(fixed, HirExpr::TempRef(temp) if *temp == target)
            || total_use_count(target, live_use_counts) != 1
            || scratch.has_debug_local_hint(target)
        {
            return false;
        }
        let (Some(target_slot), Some(source_slot)) =
            (facts.home_slot(target), facts.home_slot(*source))
        else {
            return false;
        };
        if captured_slots.contains(&target_slot)
            || captured_slots.contains(&source_slot)
            || !target_slots.insert(target_slot)
        {
            return false;
        }
        source_slots.insert(source_slot);
    }
    if !target_slots.is_disjoint(&source_slots) {
        return false;
    }

    for stmt in &block.stmts[(run_start + alias_count)..run_end] {
        let Some((target, _)) = inline_candidate(stmt) else {
            return false;
        };
        let Some(slot) = facts.home_slot(target) else {
            return false;
        };
        if target_slots.contains(&slot) || source_slots.contains(&slot) {
            return false;
        }
    }

    let (run, sink) = block.stmts.split_at_mut(run_end);
    let HirStmt::Return(ret) = &mut sink[0] else {
        unreachable!("validated open-return sink must remain a return")
    };
    for (offset, (stmt, fixed)) in run[run_start..(run_start + alias_count)]
        .iter()
        .zip(&mut ret.values.fixed)
        .enumerate()
    {
        let Some((target, HirExpr::TempRef(source))) = inline_candidate(stmt) else {
            unreachable!("validated fixed-prefix alias must remain scalar")
        };
        *fixed = HirExpr::TempRef(*source);
        removed_stmts[run_start + offset] = true;
        remove_live_use(live_use_counts, target);
    }
    true
}

fn call_arg_inline_crosses_materialized_callee(
    site: InlineSite,
    value: &HirExpr,
    stmt_index: usize,
    callee_materialized_at: Option<usize>,
) -> bool {
    site == InlineSite::CallArg
        && expr_observes_eval_order(value)
        && callee_materialized_at.is_some_and(|callee_index| stmt_index < callee_index)
}

struct OrderSensitiveDefWorkspace {
    defs: Vec<Option<usize>>,
    touched: Vec<TempId>,
}

impl OrderSensitiveDefWorkspace {
    fn new(temp_count: usize) -> Self {
        Self {
            defs: vec![None; temp_count],
            touched: Vec::new(),
        }
    }

    fn rebuild(&mut self, stmts: &[HirStmt]) {
        for temp in self.touched.drain(..) {
            self.defs[temp.index()] = None;
        }
        for (index, stmt) in stmts.iter().enumerate() {
            let Some((temp, value)) = inline_candidate(stmt) else {
                continue;
            };
            if !expr_observes_eval_order(value) {
                continue;
            }
            let slot = &mut self.defs[temp.index()];
            if slot.is_none() {
                self.touched.push(temp);
            }
            *slot = Some(index);
        }
    }

    fn get(&self, temp: TempId) -> Option<usize> {
        self.defs[temp.index()]
    }
}

fn arg_value_forwards_prior_order_sensitive_expr(
    arg_value: &HirExpr,
    callee_def_index: usize,
    prior_order_sensitive_defs: &OrderSensitiveDefWorkspace,
) -> bool {
    let HirExpr::TempRef(temp) = arg_value else {
        return false;
    };
    prior_order_sensitive_defs
        .get(*temp)
        .is_some_and(|arg_def_index| arg_def_index < callee_def_index)
}

fn materialization_run_candidate_is_safe(
    temp: TempId,
    value: &HirExpr,
    stmt_index: usize,
    scratch: &TempUseScratch,
    facts: &ProtoPromotionFacts,
    captured_slots_before_stmt: &CapturedSlotSnapshots,
) -> bool {
    !scratch.has_debug_local_hint(temp)
        && !temp_rebinds_captured_slot(
            temp,
            facts,
            captured_slots_before_stmt
                .get(stmt_index)
                .expect("captured slot scan should cover every statement"),
        )
        && !expr_touches_temp(value, temp)
}

fn total_use_count(temp: TempId, total_use_totals: &[usize]) -> usize {
    total_use_totals
        .get(temp.index())
        .copied()
        .unwrap_or_default()
}

fn remove_live_use(live_use_counts: &mut [usize], temp: TempId) {
    let count = live_use_counts
        .get_mut(temp.index())
        .expect("live use counts should cover every referenced temp");
    *count = count
        .checked_sub(1)
        .expect("successful inline should remove one live use");
}

fn collect_block_temp_use_totals(stmts: &[HirStmt], scratch: &mut TempUseScratch) -> Vec<usize> {
    let mut totals = vec![0; scratch.temp_count()];
    for stmt in stmts {
        collect_stmt_temp_uses(stmt, scratch).add_to_totals(&mut totals);
    }
    totals
}

fn inline_temps_in_nested_blocks(
    stmt: &mut HirStmt,
    workspace: &mut TempInlineWorkspace,
    live_use_counts: &mut [usize],
    reference_captured: &ReferenceCapturedBindings,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    inherited_captured_slots: &BTreeSet<HomeSlotKey>,
) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            let mut changed = inline_temps_in_block(
                &mut if_stmt.then_block,
                workspace,
                live_use_counts,
                reference_captured,
                readability,
                facts,
                inherited_captured_slots,
            );
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= inline_temps_in_block(
                    else_block,
                    workspace,
                    live_use_counts,
                    reference_captured,
                    readability,
                    facts,
                    inherited_captured_slots,
                );
            }
            changed
        }
        HirStmt::While(while_stmt) => inline_temps_in_block(
            &mut while_stmt.body,
            workspace,
            live_use_counts,
            reference_captured,
            readability,
            facts,
            inherited_captured_slots,
        ),
        HirStmt::Repeat(repeat_stmt) => {
            let mut changed = inline_temps_in_block(
                &mut repeat_stmt.body,
                workspace,
                live_use_counts,
                reference_captured,
                readability,
                facts,
                inherited_captured_slots,
            );
            changed |= inline_repeat_tail_temp(
                repeat_stmt,
                &mut workspace.uses,
                live_use_counts,
                reference_captured,
                readability,
                facts,
                inherited_captured_slots,
            );
            changed
        }
        HirStmt::NumericFor(numeric_for) => inline_temps_in_block(
            &mut numeric_for.body,
            workspace,
            live_use_counts,
            reference_captured,
            readability,
            facts,
            inherited_captured_slots,
        ),
        HirStmt::GenericFor(generic_for) => inline_temps_in_block(
            &mut generic_for.body,
            workspace,
            live_use_counts,
            reference_captured,
            readability,
            facts,
            inherited_captured_slots,
        ),
        HirStmt::Block(block) => inline_temps_in_block(
            block,
            workspace,
            live_use_counts,
            reference_captured,
            readability,
            facts,
            inherited_captured_slots,
        ),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn inline_repeat_tail_temp(
    repeat_stmt: &mut crate::hir::common::HirRepeat,
    scratch: &mut TempUseScratch,
    live_use_counts: &mut [usize],
    reference_captured: &ReferenceCapturedBindings,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    inherited_captured_slots: &BTreeSet<HomeSlotKey>,
) -> bool {
    let Some(tail_index) = repeat_stmt.body.stmts.len().checked_sub(1) else {
        return false;
    };
    let Some((temp, value)) = inline_candidate(&repeat_stmt.body.stmts[tail_index]) else {
        return false;
    };
    if scratch.has_debug_local_hint(temp)
        || expr_touches_temp(value, temp)
        || total_use_count(temp, live_use_counts) != 1
        || collect_expr_temp_uses_summary(&repeat_stmt.cond, scratch).count(temp) != 1
    {
        return false;
    }
    let Some(site) = inline_site_in_repeat_condition(&repeat_stmt.cond, temp) else {
        return false;
    };
    if !site.allows(value, readability)
        || expr_requires_ordered_snapshot(value)
            && !temp_precedes_observable_eval_in_expr(
                &repeat_stmt.cond,
                temp,
                expr_observes_eval_order(value),
                reference_captured,
            )
    {
        return false;
    }

    let mut captured_slots = inherited_captured_slots.clone();
    for stmt in &repeat_stmt.body.stmts[..tail_index] {
        if collect_stmt_temp_uses(stmt, scratch).count(temp) != 0
            || stmt_writes_temp(stmt, temp)
            || stmt_contains_nested_nonlocal_control(stmt)
        {
            return false;
        }
        facts.collect_captured_home_slots_in_stmt(stmt, &mut captured_slots);
    }
    if temp_rebinds_captured_slot(temp, facts, &captured_slots) {
        return false;
    }

    let value = value.clone();
    rewrite::replace_temp_in_expr(&mut repeat_stmt.cond, temp, &value);
    repeat_stmt.body.stmts.pop();
    remove_live_use(live_use_counts, temp);
    true
}

fn temp_rebinds_captured_slot(
    temp: TempId,
    facts: &ProtoPromotionFacts,
    captured_slots: &BTreeSet<HomeSlotKey>,
) -> bool {
    facts
        .home_slot(temp)
        .is_some_and(|slot| captured_slots.contains(&slot))
}
