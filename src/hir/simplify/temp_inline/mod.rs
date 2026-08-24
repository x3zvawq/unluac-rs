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
//! 独立区域，不能接收循环外快照。跨边界折叠现在有四个窄合同：repeat body 尾写入与
//! until 属于同一轮；open return 的 fixed alias 必须先于完整保留的 tail setup；终态
//! fixed return 前的纯 nil 并行写可在无资源边界的 proto 内直接并入 return；PUC Lua
//! 5.2–5.5 的单 upvalue table 左值可把相邻 producer 收回 key。四项仍要求唯一消费
//! 且不绕过原求值点；前两项不允许相关 home 被跨越区间写入或 capture，nil pack 还
//! 拒绝任何 `<close>`/`Close` 资源事实与 home compaction，table key 则继续服从内部
//! 前缀顺序证明。
//! numeric-for 前的连续 materialization run 还允许越过保留下来的状态赋值收回稳定字面量
//! header temp；例如 `t0 = 1; t1 = 3; state = seed; for i = t0, t1` 会恢复成
//! `state = seed; for i = 1, 3`。非字面量仍走相邻求值顺序证明，不跨状态赋值猜快照。
//! repeat 的 frozen condition prefix 因直接 continue 被移到 body 首句时，若它是只由 latch
//! 读取一次的稳定标量，也可直接收回条件；continue 仍抵达同一 latch，break/return 则跳过。
//! closure 的复杂度无法代表 child proto 函数体，因此不把 closure producer 内联进 loop head；
//! 普通 `local function iter()` 应保留为独立声明，避免生成多行匿名 iterator。
//! 具有返回值的 call 同样按 child proto 当前 body 判断：复杂 callee 保留 producer binding，
//! 单条简单 body 才继续内联，避免把命名函数压回赋值或 return 中的多行 IIFE。
//! method 协议的 callee base 与隐式首参虽是两个语法 use，却只求值一次 receiver；相邻
//! 裸 binding 或命名字段链快照可在严格匹配这对 use 后原子收回，例如
//! `t = subject.worker; t:touch()` 会恢复成 `subject.worker:touch()`；终结调用的连续物化 run
//! 还可收回 owner 保持存活的裸 receiver，普通点调用仍按两次读取处理。
//! branch-values 的定向入口只重用同一证明去处理本轮新暴露的根级 global-call run 或
//! 单值 terminal return，不递归，也不开放其它普通内联 site。

mod rewrite;
mod site;
mod usage;

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::{DecompileDialect, ReadabilityOptions};
use crate::hir::common::{
    HirBlock, HirCallExpr, HirExpr, HirLValue, HirProto, HirStmt, HirTableField, HirTableKey,
    TempId,
};
use crate::hir::expr_safety::{
    expr_is_discard_safe, expr_is_repeatable, expr_observes_eval_order,
    expr_requires_ordered_snapshot,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use self::rewrite::{replace_temp_in_stmt, replace_temps_in_stmt};
use self::site::{
    InlineSite, expr_touches_temp, fastcall_callee_materialization_precedes_temp,
    inline_site_in_repeat_condition, inline_site_in_stmt, is_bare_method_receiver_snapshot_in_stmt,
    is_method_receiver_snapshot, is_stable_inline_value,
    puc_upvalue_table_key_with_deferred_base_read, temp_precedes_observable_eval_in_expr,
    temp_precedes_observable_eval_in_stmt,
};
use self::usage::{
    TempUseScratch, collect_expr_temp_uses_summary, collect_stmt_temp_uses, inline_candidate,
    max_temp_index_in_block,
};
use super::mention::{ReferenceCapturedBindings, stmt_writes_temp};
use super::root_lifetimes::{CallRootLifetimeIndices, collect_call_root_lifetimes};
use super::temp_touch::stmt_contains_nested_nonlocal_control;
use super::visit::{HirVisitor, visit_stmts};

const NESTED_INLINE_MAX_COMPLEXITY: usize = 5;
const CONTROL_HEAD_INLINE_MAX_COMPLEXITY: usize = 5;
struct TempInlineWorkspace<'a> {
    uses: TempUseScratch,
    order_sensitive_defs: OrderSensitiveDefWorkspace,
    block_depth: usize,
    scope: TempInlineScope,
    dialect: DecompileDialect,
    readability: ReadabilityOptions,
    substantial_closure_bodies: &'a [bool],
    has_resource_boundary: bool,
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

impl<'a> TempInlineWorkspace<'a> {
    fn new(
        proto: &HirProto,
        temp_count: usize,
        scope: TempInlineScope,
        dialect: DecompileDialect,
        readability: ReadabilityOptions,
        substantial_closure_bodies: &'a [bool],
        has_resource_boundary: bool,
    ) -> Self {
        Self {
            uses: TempUseScratch::new(proto, temp_count),
            order_sensitive_defs: OrderSensitiveDefWorkspace::new(temp_count),
            block_depth: 0,
            scope,
            dialect,
            readability,
            substantial_closure_bodies,
            has_resource_boundary,
        }
    }
}

pub(super) fn inline_temps_in_proto_with_facts(
    proto: &mut HirProto,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    substantial_closure_bodies: &[bool],
) -> bool {
    inline_temps_in_proto_with_scope(
        proto,
        readability,
        facts,
        TempInlineScope::All,
        dialect,
        substantial_closure_bodies,
    )
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
        &[],
    );
}

fn inline_temps_in_proto_with_scope(
    proto: &mut HirProto,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    scope: TempInlineScope,
    dialect: DecompileDialect,
    substantial_closure_bodies: &[bool],
) -> bool {
    let temp_count = temp_count_for_proto(proto);
    let has_resource_boundary = proto_contains_resource_boundary(proto);
    let mut workspace = TempInlineWorkspace::new(
        proto,
        temp_count,
        scope,
        dialect,
        readability,
        substantial_closure_bodies,
        has_resource_boundary,
    );
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

fn proto_contains_resource_boundary(proto: &HirProto) -> bool {
    #[derive(Default)]
    struct ResourceBoundaryProbe(bool);

    impl HirVisitor for ResourceBoundaryProbe {
        fn visit_stmt(&mut self, stmt: &HirStmt) {
            self.0 |= matches!(stmt, HirStmt::ToBeClosed(_) | HirStmt::Close(_));
        }
    }

    let mut probe = ResourceBoundaryProbe::default();
    visit_stmts(&proto.body.stmts, &mut probe);
    probe.0
}

fn inline_temps_in_block(
    block: &mut HirBlock,
    workspace: &mut TempInlineWorkspace<'_>,
    live_use_counts: &mut [usize],
    reference_captured: &ReferenceCapturedBindings,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    inherited_captured_slots: &BTreeSet<HomeSlotKey>,
) -> bool {
    let is_proto_root = workspace.block_depth == 0;
    workspace.block_depth += 1;
    let mut changed = false;
    let mut call_root_indices = collect_call_root_lifetimes(&block.stmts, facts, |_| true);
    let mut call_root_lifetimes = call_root_indices.marked_stmts(block.stmts.len());
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

    if is_proto_root
        && inline_root_open_return_nil_pack(
            block,
            &workspace.uses,
            live_use_counts,
            facts,
            &captured_slots_before_stmt,
        )
    {
        changed = true;
        captured_slots_before_stmt =
            captured_slots_before_stmts(block, facts, inherited_captured_slots);
        call_root_indices = collect_call_root_lifetimes(&block.stmts, facts, |_| true);
        call_root_lifetimes = call_root_indices.marked_stmts(block.stmts.len());
    }

    if inline_terminal_nil_return_pack(
        block,
        &workspace.uses,
        live_use_counts,
        facts,
        &captured_slots_before_stmt,
        workspace.has_resource_boundary,
        &call_root_lifetimes,
    ) {
        changed = true;
        captured_slots_before_stmt =
            captured_slots_before_stmts(block, facts, inherited_captured_slots);
        call_root_indices = collect_call_root_lifetimes(&block.stmts, facts, |_| true);
        call_root_lifetimes = call_root_indices.marked_stmts(block.stmts.len());
    }

    if inline_materialization_runs(
        block,
        workspace,
        live_use_counts,
        facts,
        &captured_slots_before_stmt,
        reference_captured,
        &call_root_lifetimes,
    ) {
        changed = true;
        captured_slots_before_stmt =
            captured_slots_before_stmts(block, facts, inherited_captured_slots);
        call_root_indices = collect_call_root_lifetimes(&block.stmts, facts, |_| true);
        call_root_lifetimes = call_root_indices.marked_stmts(block.stmts.len());
    }

    if matches!(workspace.scope, TempInlineScope::All)
        && inline_adjacent_call_root_expression_overwrites(
            block,
            &workspace.uses,
            live_use_counts,
            facts,
            &captured_slots_before_stmt,
            &call_root_indices,
        )
    {
        changed = true;
        captured_slots_before_stmt =
            captured_slots_before_stmts(block, facts, inherited_captured_slots);
        call_root_lifetimes = collect_call_root_lifetimes(&block.stmts, facts, |_| true)
            .marked_stmts(block.stmts.len());
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
            && !call_root_lifetimes[index]
            // A call result stored in a table can outlive the immediate write. Removing the
            // temp would remove the only lexical/VM root before a later rawset or table clear;
            // keep that producer unless a separate lifetime proof exists.
            && !(matches!(value, HirExpr::Call(_))
                && kept_rev
                    .last()
                    .is_some_and(|next_stmt| stmt_stores_temp_in_table(next_stmt, temp)))
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
            && !substantial_result_closure_prefers_binding(
                site,
                value,
                next_stmt,
                workspace.substantial_closure_bodies,
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

    workspace.block_depth -= 1;
    changed
}

fn substantial_result_closure_prefers_binding(
    site: InlineSite,
    value: &HirExpr,
    sink: &HirStmt,
    substantial_closure_bodies: &[bool],
) -> bool {
    let HirExpr::Closure(closure) = value else {
        return false;
    };
    site.is_call_callee()
        && matches!(
            sink,
            HirStmt::Assign(_) | HirStmt::LocalDecl(_) | HirStmt::Return(_)
        )
        && substantial_closure_bodies
            .get(closure.proto.index())
            .copied()
            .unwrap_or(true)
}

pub(super) fn proto_body_prefers_named_callee(body: &HirBlock) -> bool {
    let stmts = match body.stmts.last() {
        Some(HirStmt::Return(ret)) if ret.values.fixed.is_empty() && ret.values.tail.is_none() => {
            &body.stmts[..body.stmts.len() - 1]
        }
        _ => body.stmts.as_slice(),
    };
    stmts.len() > 1
        || matches!(
            stmts.first(),
            Some(
                HirStmt::If(_)
                    | HirStmt::While(_)
                    | HirStmt::Repeat(_)
                    | HirStmt::NumericFor(_)
                    | HirStmt::GenericFor(_)
                    | HirStmt::Block(_)
            )
        )
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

fn stmt_stores_temp_in_table(stmt: &HirStmt, temp: TempId) -> bool {
    match stmt {
        HirStmt::Assign(assign) => {
            let table_lvalue = assign.targets.iter().any(|target| {
                matches!(
                    target,
                    HirLValue::TableAccess(access)
                        if expr_touches_temp(&access.base, temp)
                            || expr_touches_temp(&access.key, temp)
                )
            });
            let table_constructor_value = assign.values.iter().any(|value| {
                matches!(value, HirExpr::TableConstructor(_)) && expr_touches_temp(value, temp)
            });
            table_lvalue
                || table_constructor_value
                || (assign
                    .targets
                    .iter()
                    .any(|target| matches!(target, HirLValue::TableAccess(_)))
                    && assign
                        .values
                        .iter()
                        .any(|value| expr_touches_temp(value, temp)))
        }
        HirStmt::TableSetList(set_list) => {
            expr_touches_temp(&set_list.base, temp)
                || set_list
                    .values
                    .iter()
                    .any(|value| expr_touches_temp(value, temp))
        }
        HirStmt::LocalDecl(local_decl) => local_decl.values.iter().any(|value| {
            matches!(value, HirExpr::TableConstructor(_)) && expr_touches_temp(value, temp)
        }),
        _ => false,
    }
}

fn inline_adjacent_call_root_expression_overwrites(
    block: &mut HirBlock,
    scratch: &TempUseScratch,
    live_use_counts: &mut [usize],
    facts: &ProtoPromotionFacts,
    captured_slots_before_stmt: &CapturedSlotSnapshots,
    call_roots: &CallRootLifetimeIndices,
) -> bool {
    let mut removed = vec![false; block.stmts.len()];
    for overwrite_index in 1..block.stmts.len() {
        let root_index = overwrite_index - 1;
        if call_roots.root_for_overwrite(overwrite_index) != Some(root_index) {
            continue;
        }
        let Some((root, HirExpr::Call(call))) = inline_candidate(&block.stmts[root_index]) else {
            continue;
        };
        let Some((target, overwrite)) = inline_candidate(&block.stmts[overwrite_index]) else {
            continue;
        };
        let (Some(root_slot), Some(target_slot)) = (
            facts.trusted_temp_home_slot(root),
            facts.trusted_temp_home_slot(target),
        ) else {
            continue;
        };
        if root == target
            || root_slot != target_slot
            || total_use_count(root, live_use_counts) != 1
            || scratch.has_debug_local_hint(root)
            || scratch.has_debug_local_hint(target)
            || !call_root_overwrite_is_inlineable(overwrite, root)
            || captured_slots_before_stmt
                .get(overwrite_index)
                .is_none_or(|captured| captured.contains(&root_slot))
        {
            continue;
        }

        let call = HirExpr::Call(call.clone());
        replace_temp_in_stmt(&mut block.stmts[overwrite_index], root, &call);
        removed[root_index] = true;
        remove_live_use(live_use_counts, root);
    }
    let changed = removed.contains(&true);
    if changed {
        block.stmts = std::mem::take(&mut block.stmts)
            .into_iter()
            .enumerate()
            .filter_map(|(index, stmt)| (!removed[index]).then_some(stmt))
            .collect();
    }
    changed
}

fn call_root_overwrite_is_inlineable(expr: &HirExpr, root: TempId) -> bool {
    match expr {
        HirExpr::Binary(binary) => {
            matches!(&binary.lhs, HirExpr::TempRef(source) if *source == root)
                && call_root_rhs_is_primitive_literal(&binary.rhs)
        }
        HirExpr::LogicalOr(logical) => {
            matches!(&logical.lhs, HirExpr::TempRef(source) if *source == root)
                && (call_root_rhs_is_primitive_literal(&logical.rhs)
                    || matches!(
                        logical.rhs,
                        HirExpr::ParamRef(_) | HirExpr::LocalRef(_) | HirExpr::UpvalueRef(_)
                    ))
        }
        _ => false,
    }
}

fn call_root_rhs_is_primitive_literal(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Number(value) => value.is_finite(),
        HirExpr::Nil | HirExpr::Boolean(_) | HirExpr::Integer(_) | HirExpr::String(_) => true,
        _ => false,
    }
}

/// Inline a contiguous pure alias chain through one substitution-DAG rewrite.
///
/// This path deliberately accepts only repeatable expressions.  Such a chain has no
/// lookup, call, allocation, or mutable snapshot whose evaluation point could move;
/// every candidate has one total use and the dependency edges point forward in the
/// statement run.  The stricter contract is useful here because it lets the rewrite
/// operate on the final sink directly instead of recreating every intermediate sink.
struct PureMaterializationContext<'a> {
    scratch: &'a mut TempUseScratch,
    live_use_counts: &'a mut [usize],
    facts: &'a ProtoPromotionFacts,
    captured_slots_before_stmt: &'a CapturedSlotSnapshots,
    order_sensitive_defs: &'a OrderSensitiveDefWorkspace,
    readability: ReadabilityOptions,
    removed_stmts: &'a mut [bool],
}

fn inline_pure_materialization_run(
    block: &mut HirBlock,
    run_start: usize,
    run_end: usize,
    callee_index: usize,
    callee_temp: TempId,
    context: &mut PureMaterializationContext<'_>,
) -> bool {
    if callee_index != run_start || run_end <= run_start {
        return false;
    }

    let mut replacements = BTreeMap::new();
    let mut positions = BTreeMap::new();
    for index in run_start..run_end {
        let Some((temp, value)) = inline_candidate(&block.stmts[index]) else {
            return false;
        };
        if total_use_count(temp, context.live_use_counts) != 1
            || !expr_is_repeatable(value)
            || !InlineSite::Nested.allows(value, context.readability)
            || !materialization_run_candidate_is_safe(
                temp,
                value,
                index,
                context.scratch,
                context.facts,
                context.captured_slots_before_stmt,
            )
            || arg_value_forwards_prior_order_sensitive_expr(
                value,
                run_start,
                context.order_sensitive_defs,
            )
        {
            return false;
        }
        positions.insert(temp, index);
        replacements.insert(temp, value.clone());
    }

    // Every candidate must be on the dependency path that reaches the sink.  This
    // avoids deleting a dead assignment merely because its value happens to be pure.
    let mut needed = BTreeSet::new();
    collect_stmt_temp_uses(&block.stmts[run_end], context.scratch).for_each(|temp, _| {
        needed.insert(temp);
    });
    let mut pending = needed.iter().copied().collect::<Vec<_>>();
    while let Some(temp) = pending.pop() {
        let Some(value) = replacements.get(&temp) else {
            continue;
        };
        collect_expr_temp_uses_summary(value, context.scratch).for_each(|dependency, _| {
            if needed.insert(dependency) {
                pending.push(dependency);
            }
        });
    }
    if positions.keys().any(|temp| !needed.contains(temp)) {
        return false;
    }

    // A candidate may only depend on an earlier assignment.  Reject forward edges
    // explicitly so the map cannot contain a cycle or change source evaluation order.
    for (&temp, value) in &replacements {
        let Some(&position) = positions.get(&temp) else {
            continue;
        };
        let mut valid = true;
        collect_expr_temp_uses_summary(value, context.scratch).for_each(|dependency, _| {
            if positions
                .get(&dependency)
                .is_some_and(|dependency_position| *dependency_position >= position)
            {
                valid = false;
            }
        });
        if !valid {
            return false;
        }
    }

    let mut rewritten_sink = block.stmts[run_end].clone();
    if replace_temps_in_stmt(&mut rewritten_sink, &replacements) == 0 {
        return false;
    }
    let mut remaining = false;
    collect_stmt_temp_uses(&rewritten_sink, context.scratch).for_each(|temp, _| {
        remaining |= positions.contains_key(&temp);
    });
    if remaining {
        return false;
    }

    // The source call already establishes that `callee_temp` is the direct call
    // target.  The map expansion above only substitutes forwarding refs, so this
    // check guards against an unexpected shape change in future HIR variants.
    if !replacements.contains_key(&callee_temp) {
        return false;
    }
    block.stmts[run_end] = rewritten_sink;
    context.removed_stmts[run_start..run_end].fill(true);
    for temp in positions.keys().copied() {
        remove_live_use(context.live_use_counts, temp);
    }
    true
}

fn inline_materialization_runs(
    block: &mut HirBlock,
    workspace: &mut TempInlineWorkspace<'_>,
    live_use_counts: &mut [usize],
    facts: &ProtoPromotionFacts,
    captured_slots_before_stmt: &CapturedSlotSnapshots,
    reference_captured: &ReferenceCapturedBindings,
    call_root_lifetimes: &[bool],
) -> bool {
    // child block 已全部处理完才会到这里，因此同一个 proto 级 workspace 不会覆盖
    // 仍在活跃递归 frame 中的 parent 索引。
    let TempInlineWorkspace {
        uses,
        order_sensitive_defs,
        scope,
        dialect,
        readability,
        ..
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
        if call_root_lifetimes[run_start..run_end]
            .iter()
            .any(|preserve| *preserve)
        {
            index = run_end;
            continue;
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
        let callee_value = callee_value.clone();
        let terminal_candidate = block.stmts[..run_end]
            .last()
            .and_then(inline_candidate)
            .map(|(temp, _)| temp);
        if !scope.allows_call(
            call_stmt,
            &callee_value,
            terminal_candidate,
            &block.stmts[run_end],
        ) {
            index = run_end + 1;
            continue;
        }
        if !materialization_run_candidate_is_safe(
            callee_temp,
            &callee_value,
            callee_index,
            uses,
            facts,
            captured_slots_before_stmt,
        ) || total_use_count(callee_temp, live_use_counts) != 1
        {
            index = run_end + 1;
            continue;
        }

        // A long forwarding run can be represented as a substitution DAG.  Validate
        // the complete pure alias chain once, then rewrite the sink in one traversal;
        // this keeps generated source readable without imposing an arbitrary run-size
        // cutoff.  Runs containing observable expressions continue through the precise
        // per-site proof below.
        let mut pure_context = PureMaterializationContext {
            scratch: uses,
            live_use_counts,
            facts,
            captured_slots_before_stmt,
            order_sensitive_defs,
            readability: *readability,
            removed_stmts: &mut removed_stmts,
        };
        if inline_pure_materialization_run(
            block,
            run_start,
            run_end,
            callee_index,
            callee_temp,
            &mut pure_context,
        ) {
            changed = true;
            index = run_end + 1;
            continue;
        }

        let mut rewritten_sink = block.stmts[run_end].clone();
        let mut removed_temps = Vec::with_capacity(run_end - callee_index);
        let mut discarded_uses = Vec::new();
        let mut duplicated_uses = Vec::new();
        let trailing = &block.stmts[run_end + 1..];
        let sink_is_terminal = trailing.is_empty()
            || matches!(trailing, [HirStmt::Return(ret)]
                if ret.values.fixed.is_empty() && ret.values.tail.is_none());
        let materialization_run = &block.stmts[callee_index..run_end];
        let mut method_receiver_pair_seen = false;
        let mut complete_run = true;
        for candidate_index in ((callee_index + 1)..run_end).rev() {
            let Some((temp, value)) = inline_candidate(&block.stmts[candidate_index]) else {
                complete_run = false;
                break;
            };
            let use_count = total_use_count(temp, live_use_counts);
            let forwarded_owner_survives = sink_is_terminal
                && materialization_run_preserves_forwarded_temp_owner(
                    materialization_run,
                    candidate_index - callee_index,
                    value,
                    facts,
                );
            let method_receiver_pair = use_count == 2
                && sink_is_terminal
                && (!matches!(value, HirExpr::TempRef(_)) || forwarded_owner_survives)
                && is_bare_method_receiver_snapshot_in_stmt(&rewritten_sink, temp, value);
            let stable_method_run_alias =
                forwarded_owner_survives && (method_receiver_pair || method_receiver_pair_seen);
            if use_count > 1 && !method_receiver_pair {
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
            if matches!(value, HirExpr::Call(_)) && stmt_stores_temp_in_table(&rewritten_sink, temp)
            {
                complete_run = false;
                break;
            }
            if use_count == 0 {
                if candidate_is_safe && expr_is_discard_safe(value) {
                    discarded_uses.push(collect_expr_temp_uses_summary(value, uses));
                    continue;
                }
                complete_run = false;
                break;
            }
            let Some(site) = inline_site_in_stmt(&rewritten_sink, temp) else {
                complete_run = false;
                break;
            };
            if !candidate_is_safe
                || (!stable_method_run_alias
                    && arg_value_forwards_prior_order_sensitive_expr(
                        value,
                        callee_index,
                        order_sensitive_defs,
                    ))
                || (!stable_method_run_alias
                    && inline_crosses_evaluation_boundary(
                        site,
                        value,
                        &rewritten_sink,
                        temp,
                        reference_captured,
                        *dialect,
                    ))
            {
                complete_run = false;
                break;
            }
            replace_temp_in_stmt(&mut rewritten_sink, temp, value);
            removed_temps.push(temp);
            if method_receiver_pair {
                // 原赋值已经持有 replacement 的一份 use；method lowering 把两处 HIR
                // 引用收成一次源码求值，因此替换后只新增一份活跃依赖。
                duplicated_uses.push(collect_expr_temp_uses_summary(value, uses));
                removed_temps.push(temp);
                method_receiver_pair_seen = true;
            }
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
                &callee_value,
                &rewritten_sink,
                callee_temp,
                reference_captured,
                *dialect,
            )
        {
            index = run_end + 1;
            continue;
        }
        replace_temp_in_stmt(&mut rewritten_sink, callee_temp, &callee_value);
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
        for uses in duplicated_uses {
            uses.add_to_totals(live_use_counts);
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

fn materialization_run_preserves_forwarded_temp_owner(
    run: &[HirStmt],
    candidate_offset: usize,
    value: &HirExpr,
    facts: &ProtoPromotionFacts,
) -> bool {
    let HirExpr::TempRef(owner) = value else {
        return false;
    };
    let Some(owner_home) = facts.trusted_temp_home_slot(*owner) else {
        return false;
    };

    run.iter().enumerate().all(|(offset, stmt)| {
        if offset == candidate_offset {
            return true;
        }
        let Some((target, _)) = inline_candidate(stmt) else {
            return false;
        };
        facts
            .trusted_temp_home_slot(target)
            .is_some_and(|home| home != owner_home)
            && facts
                .trusted_immediate_move_write_homes(target)
                .is_some_and(|homes| !homes.contains(&owner_home))
    })
}

struct RootOpenReturnNilPackPlan {
    assignment_index: usize,
    fixed_start: usize,
    targets: Vec<TempId>,
}

fn inline_root_open_return_nil_pack(
    block: &mut HirBlock,
    scratch: &TempUseScratch,
    live_use_counts: &mut [usize],
    facts: &ProtoPromotionFacts,
    captured_slots_before_stmt: &CapturedSlotSnapshots,
) -> bool {
    let Some(plan) = root_open_return_nil_pack_plan(
        block,
        scratch,
        live_use_counts,
        facts,
        captured_slots_before_stmt,
    ) else {
        return false;
    };

    let return_index = block.stmts.len() - 1;
    let HirStmt::Return(ret) = &mut block.stmts[return_index] else {
        unreachable!("validated terminal nil-pack sink must remain a return")
    };
    ret.values.fixed[plan.fixed_start..plan.fixed_start + plan.targets.len()].fill(HirExpr::Nil);
    for target in plan.targets {
        remove_live_use(live_use_counts, target);
    }
    block.stmts.remove(plan.assignment_index);
    true
}

fn root_open_return_nil_pack_plan(
    block: &HirBlock,
    scratch: &TempUseScratch,
    live_use_counts: &[usize],
    facts: &ProtoPromotionFacts,
    captured_slots_before_stmt: &CapturedSlotSnapshots,
) -> Option<RootOpenReturnNilPackPlan> {
    if facts.compacts_home_slots() {
        return None;
    }
    let return_index = block.stmts.len().checked_sub(1)?;
    let HirStmt::Return(ret) = &block.stmts[return_index] else {
        return None;
    };
    let tail = ret.values.tail.as_ref()?;
    if tail.exact_width().is_some() || !matches!(tail.as_expr(), HirExpr::Call(_)) {
        return None;
    }
    let captured_slots = captured_slots_before_stmt.get(return_index)?;

    for assignment_index in (0..return_index).rev() {
        let HirStmt::Assign(assign) = &block.stmts[assignment_index] else {
            continue;
        };
        if assign.targets.len() < 2
            || assign.values.tail.is_some()
            || assign.values.fixed.len() != assign.targets.len()
            || !assign
                .values
                .fixed
                .iter()
                .all(|value| matches!(value, HirExpr::Nil))
            || !block.stmts[..assignment_index]
                .iter()
                .all(root_nil_pack_prefix_stmt_is_single_pass)
        {
            continue;
        }
        let Some(targets) = assign
            .targets
            .iter()
            .map(|target| match target {
                HirLValue::Temp(temp) => Some(*temp),
                HirLValue::Param(_)
                | HirLValue::Local(_)
                | HirLValue::Upvalue(_)
                | HirLValue::Global(_)
                | HirLValue::TableAccess(_) => None,
            })
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        let fixed_start = ret.values.fixed.windows(targets.len()).position(|window| {
            window
                .iter()
                .zip(&targets)
                .all(|(value, target)| matches!(value, HirExpr::TempRef(temp) if temp == target))
        });
        let Some(fixed_start) = fixed_start else {
            continue;
        };

        let mut target_slots = BTreeSet::new();
        if targets.iter().any(|target| {
            !facts.overwrites_entry_nil(*target)
                || total_use_count(*target, live_use_counts) != 1
                || scratch.has_debug_local_hint(*target)
                || facts
                    .trusted_temp_home_slot(*target)
                    .is_none_or(|slot| captured_slots.contains(&slot) || !target_slots.insert(slot))
        }) || !block.stmts[assignment_index + 1..return_index]
            .iter()
            .all(|stmt| root_nil_pack_gap_preserves_slots(stmt, &target_slots, facts))
        {
            continue;
        }

        return Some(RootOpenReturnNilPackPlan {
            assignment_index,
            fixed_start,
            targets,
        });
    }
    None
}

/// 收回紧邻终态 fixed return 前的并行 nil 写入。
///
/// 这条路径与 open-tail 的 root handoff 分开：return 本身仍在原 statement 位置产生
/// 同样宽度的 nil pack，因而没有把 nil 跨过 call/lookup 或其它求值事件。只有临时槽、
/// 非压缩 home、无 debug/capture 且每个目标只有唯一 return 读取时才成立；带 tail 的
/// return、局部/参数目标和任何不可信 home 继续保留原始并行写。
fn inline_terminal_nil_return_pack(
    block: &mut HirBlock,
    scratch: &TempUseScratch,
    live_use_counts: &mut [usize],
    facts: &ProtoPromotionFacts,
    captured_slots_before_stmt: &CapturedSlotSnapshots,
    has_resource_boundary: bool,
    call_root_lifetimes: &[bool],
) -> bool {
    if facts.compacts_home_slots() || has_resource_boundary {
        return false;
    }
    let Some(return_index) = block.stmts.len().checked_sub(1) else {
        return false;
    };
    let Some(assign_index) = return_index.checked_sub(1) else {
        return false;
    };
    if call_root_lifetimes
        .get(assign_index)
        .copied()
        .unwrap_or(true)
    {
        return false;
    }
    let (HirStmt::Assign(assign), HirStmt::Return(ret)) =
        (&block.stmts[assign_index], &block.stmts[return_index])
    else {
        return false;
    };
    if assign.targets.len() < 2
        || assign.values.tail.is_some()
        || assign.values.fixed.len() != assign.targets.len()
        || !assign
            .values
            .fixed
            .iter()
            .all(|value| matches!(value, HirExpr::Nil))
        || ret.values.tail.is_some()
        || ret.values.fixed.len() != assign.targets.len()
    {
        return false;
    }

    let Some(targets) = assign
        .targets
        .iter()
        .map(|target| match target {
            HirLValue::Temp(temp) => Some(*temp),
            HirLValue::Param(_)
            | HirLValue::Local(_)
            | HirLValue::Upvalue(_)
            | HirLValue::Global(_)
            | HirLValue::TableAccess(_) => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    if !ret
        .values
        .fixed
        .iter()
        .zip(&targets)
        .all(|(value, target)| matches!(value, HirExpr::TempRef(temp) if temp == target))
    {
        return false;
    }

    let Some(captured_slots) = captured_slots_before_stmt.get(assign_index) else {
        return false;
    };
    let mut target_slots = BTreeSet::new();
    for target in &targets {
        let Some(slot) = facts.trusted_temp_home_slot(*target) else {
            return false;
        };
        if !target_slots.insert(slot)
            || captured_slots.contains(&slot)
            || scratch.has_debug_local_hint(*target)
            || total_use_count(*target, live_use_counts) != 1
        {
            return false;
        }
    }

    let HirStmt::Return(ret) = &mut block.stmts[return_index] else {
        unreachable!("validated terminal nil-pack sink must remain a return")
    };
    ret.values.fixed.fill(HirExpr::Nil);
    for target in targets {
        remove_live_use(live_use_counts, target);
    }
    block.stmts.remove(assign_index);
    true
}

fn root_nil_pack_prefix_stmt_is_single_pass(stmt: &HirStmt) -> bool {
    matches!(
        stmt,
        HirStmt::LocalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::CallStmt(_)
    )
}

fn root_nil_pack_gap_preserves_slots(
    stmt: &HirStmt,
    protected: &BTreeSet<HomeSlotKey>,
    facts: &ProtoPromotionFacts,
) -> bool {
    match stmt {
        HirStmt::Assign(assign) => assign.targets.iter().all(|target| {
            direct_lvalue_home_slot(target, facts)
                .is_some_and(|slot| slot.is_none_or(|slot| !protected.contains(&slot)))
        }),
        HirStmt::LocalDecl(local_decl) => local_decl.bindings.iter().all(|local| {
            facts
                .trusted_local_home_slot(*local)
                .is_some_and(|slot| !protected.contains(&slot))
        }),
        HirStmt::TableSetList(_) | HirStmt::CallStmt(_) => true,
        HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::Return(_)
        | HirStmt::If(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::Block(_) => false,
    }
}

fn direct_lvalue_home_slot(
    target: &HirLValue,
    facts: &ProtoPromotionFacts,
) -> Option<Option<HomeSlotKey>> {
    match target {
        HirLValue::Param(param) => facts.trusted_param_home_slot(*param).map(Some),
        HirLValue::Temp(temp) => facts.trusted_temp_home_slot(*temp).map(Some),
        HirLValue::Local(local) => facts.trusted_local_home_slot(*local).map(Some),
        HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => Some(None),
    }
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
        let (Some(target_slot), Some(source_slot)) = (
            facts.trusted_temp_home_slot(target),
            facts.trusted_temp_home_slot(*source),
        ) else {
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
        let Some(slot) = facts.trusted_temp_home_slot(target) else {
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
    workspace: &mut TempInlineWorkspace<'_>,
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
            changed |= inline_repeat_head_scalar_temp(
                repeat_stmt,
                &mut workspace.uses,
                live_use_counts,
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

fn inline_repeat_head_scalar_temp(
    repeat_stmt: &mut crate::hir::common::HirRepeat,
    scratch: &mut TempUseScratch,
    live_use_counts: &mut [usize],
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    inherited_captured_slots: &BTreeSet<HomeSlotKey>,
) -> bool {
    let Some((temp, value)) = repeat_stmt.body.stmts.first().and_then(inline_candidate) else {
        return false;
    };
    if facts.compacts_home_slots()
        || !facts.is_repeat_condition_prefix_temp(temp)
        || facts.trusted_temp_home_slot(temp).is_none()
        || !is_repeat_header_rootless_scalar(value)
        || scratch.has_debug_local_hint(temp)
        || total_use_count(temp, live_use_counts) != 1
        || collect_expr_temp_uses_summary(&repeat_stmt.cond, scratch).count(temp) != 1
    {
        return false;
    }
    let Some(site) = inline_site_in_repeat_condition(&repeat_stmt.cond, temp) else {
        return false;
    };
    if !site.allows(value, readability) {
        return false;
    }

    let mut captured_slots = inherited_captured_slots.clone();
    for stmt in &repeat_stmt.body.stmts[1..] {
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
    repeat_stmt.body.stmts.remove(0);
    remove_live_use(live_use_counts, temp);
    true
}

fn is_repeat_header_rootless_scalar(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
    )
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
