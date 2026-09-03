//! 这个文件实现 HIR 的第一批 temp inlining。
//!
//! 原始参数槽交接证明只在当前唯一 producer/参数 occurrence 配对后消费；capture、
//! 执行区域与求值顺序仍需正证，展示复杂度不能迫使该参数变成额外 caller root。
//! 常规路径以 use-count、home/capture 与求值区域事实证明等价性，只折叠“单目标 temp
//! 赋值，并且被紧邻下一条
//! 简单语句使用一次”的情况。调用表达式另有一条更窄的连续融合规则，用来处理
//! `callee_temp = f; arg_temp = expr; callee_temp(arg_temp)` 这种 bytecode 为保持 Lua
//! “先求 callee、再求参数”而拆出的形状；融合时必须把 callee 和参数一起放回同一条
//! call，不能只把 callee 延后到参数求值之后。run 中无读取且可安全丢弃的匿名 temp
//! 不构成求值事件，但带 debug/capture 身份的赋值仍会阻断整包融合。
//! 同一 transaction 还覆盖 `If` 条件中首个必达 call：只有连续 lookup/callee/arg run
//! 的每个节点都唯一进入该 call 的 eager 求值子图时才整体收回；短路 RHS、额外 use、
//! PhysicalRoot、capture/debug identity 或反向依赖均保留原形。
//! 同一 block 的独立 run 沿进入本函数时的语句索引批量判定：sink 原位改写，删除区间
//! 延迟到扫描结束后一次压缩，使 capture 与求值顺序快照始终处在同一坐标系。
//! order-sensitive def 索引由 proto 级 scratch 复用，每个 block 只清理上次实际写过的槽，
//! 避免结构块数量与全局 temp 数相乘的稠密初始化成本。
//! 相邻内联以可观察事件前缀而非语法子节点顺序判定：纯 local/param 读取本身不是
//! 屏障，但读取结果形成的 temp 快照不能越过可能改写 binding 的事件；lookup、调用、
//! 运算和 method sugar 的隐式 lookup 是屏障。while/repeat 条件还属于每轮重新求值的
//! 独立区域，不能接收循环外快照。跨边界折叠现在有四个窄合同：repeat body 尾写入与
//! until 属于同一轮；open return 的 fixed alias 必须先于完整保留的 tail setup；终态
//! fixed return 前的纯 nil 并行写可在候选自身无 physical-root/capture 冲突时直接并入 return；PUC Lua
//! 5.2–5.5 的单 upvalue table 左值可把相邻 producer 收回 key。四项仍要求唯一消费
//! 且不绕过原求值点；前两项不允许相关 home 被跨越区间写入或 capture，nil pack 的
//! raw temp 必须保有未失效的 `(slot, close epoch)`，table key 则继续服从内部前缀顺序证明。
//! numeric-for 前的连续 materialization run 还允许越过保留下来的状态赋值收回稳定字面量
//! header temp；未被引用 capture、且区间内没有其它同 home 写的 LocalRef/ParamRef 也可沿纯
//! TempRef 链收回。例如 `t0 = source; t1 = setup(); t2 = t0; for i = t2, 3` 在 setup
//! 不能改写 source 时恢复成 `t1 = setup(); for i = source, 3`。lookup/call/运算仍走相邻
//! 求值顺序证明，不跨状态赋值猜可变快照。
//! repeat 的 frozen condition prefix 因直接 continue 被移到 body 首句时，若它是只由 latch
//! 读取一次的稳定标量，也可直接收回条件；continue 仍抵达同一 latch，break/return 则跳过。
//! closure 的复杂度无法代表 child proto 函数体，因此不把 closure producer 内联进 loop head；
//! 普通 `local function iter()` 应保留为独立声明，避免生成多行匿名 iterator。
//! 具有返回值的 call 同样按 child proto 当前 body 判断：复杂 callee 保留 producer binding，
//! 单条简单 body 才继续内联，避免把命名函数压回赋值或 return 中的多行 IIFE。
//! call-root 的相邻同槽表达式覆盖直接消费 root-lifetime owner 冻结的配对 home；二元
//! RHS 只额外接受 primitive 或 param/local/upvalue 直接读取，保持 call、RHS、运算与覆盖
//! 的原顺序，不把 lookup、调用、分配或 closure 搬进该事务。
//! method 协议的 callee base 与隐式首参虽是两个语法 use，却只求值一次 receiver；相邻
//! 裸 binding 或命名字段链快照可在严格匹配这对 use 后原子收回，例如
//! `t = subject.worker; t:touch()` 会恢复成 `subject.worker:touch()`；终结调用的连续物化 run
//! 还可收回 owner 保持存活的裸 receiver。若独立 receiver owner 只是从另一个 pure scope-end
//! root 复制而来，allocation-root pair 与稳定 source home 可共同证明 alternate-root handoff；
//! 即使 receiver 的覆盖 RHS 可能触发 GC，也可删除该 copy。普通点调用仍按两次读取处理。
//! 纯 frame-end 的无读 copy 与 receiver 交接共用提交器；前层证明目标旧值非资源后，
//! 保留 source 的 PhysicalRoot 而删除副本，不把两个负向保护标记直接解释成可删除。
//! 相邻 sink 若是无条件 `Block`，只递归穿过零前缀的第一条语句；第二条及更晚消费仍需
//! block-prefix 的求值、写入、capture 与控制流摘要，不能把整个词法块视为透明。
//! branch-values 的定向入口只重用同一证明去处理本轮新暴露的根级 global-call run 或
//! 单值 terminal return，不递归，也不开放其它普通内联 site。
//! promotion 已失去单一 binding home 时，本 pass 使用 proto 的完整 `(slot, close epoch)`
//! 全集继续做 may-alias；Unknown 因而只能命中既有 capture/value-flow/lifetime 屏障，不能
//! 被不同 HIR identity 误当成物理不相交。
//! Indexed 构造器直接消费 HIR 分配事实；若内联引入模板初始化，则发布操作数保留
//! 身份，例如 `t=true; return {a,t,c}` 保持运行时 t，不将 TNEW 的容量改成 TDUP 裁尾。

mod rewrite;
mod site;
mod usage;

use std::collections::{BTreeMap, BTreeSet};

use crate::decompile::{DecompileDialect, ReadabilityOptions};
use crate::hir::common::{
    HirBlock, HirCallExpr, HirExpr, HirInlineDispositions, HirInlineRetentionReason, HirLValue,
    HirProto, HirStmt, HirTableField, TempId,
};
use crate::hir::expr_safety::{
    HirExprSafety, expr_observes_eval_order, expr_requires_ordered_snapshot,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use self::rewrite::{replace_temp_in_stmt, replace_temps_in_stmt};
use self::site::{
    InlineSite, expr_touches_temp, fastcall_callee_materialization_precedes_temp,
    inline_site_in_repeat_condition, inline_site_in_stmt, is_bare_method_receiver_snapshot_in_stmt,
    is_method_receiver_snapshot, is_stable_inline_value,
    puc_upvalue_table_key_with_deferred_base_read, temp_precedes_observable_eval_in_expr,
    temp_precedes_observable_eval_in_stmt, transparent_block_head,
};
use self::usage::{
    TempUseScratch, TempUseSummary, collect_expr_temp_uses_summary, collect_stmt_temp_uses,
    inline_candidate, max_temp_index_in_block,
};
use super::label_refs::count_label_references;
use super::mention::{
    ReferenceCapturedBindings, stmt_writes_temp, stmts_reference_captured_bindings,
    stmts_to_be_closed_temps, stmts_value_captured_bindings,
};
use super::object_flow::RootAnalysisContext;
use super::root_lifetimes::{
    CallRootLifetimeIndices, collect_call_root_lifetimes, collect_lookup_gc_root_lifetimes,
    materialize_generic_for_dispatch_root_releases, scope_end_copy_root_handoffs,
    scope_end_copy_roots_needing_materialization, stmt_has_argument_root_handoff,
};
use super::temp_touch::stmt_contains_nested_nonlocal_control;
use crate::hir::visit::{HirVisitor, visit_expr, visit_stmts};

const NESTED_INLINE_MAX_COMPLEXITY: usize = 5;
const CONTROL_HEAD_INLINE_MAX_COMPLEXITY: usize = 5;
struct TempInlineWorkspace<'a> {
    uses: TempUseScratch,
    order_sensitive_defs: OrderSensitiveDefWorkspace,
    block_depth: usize,
    scope: TempInlineScope,
    dialect: DecompileDialect,
    roots: RootAnalysisContext<'a>,
    readability: ReadabilityOptions,
    substantial_closure_bodies: &'a [bool],
    physical_root_temps: Vec<bool>,
    new_physical_root_temps: BTreeSet<TempId>,
    inline_dispositions: HirInlineDispositions,
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
            && call_stmt.call.method_key.is_none()
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
        scope: TempInlineScope,
        dialect: DecompileDialect,
        readability: ReadabilityOptions,
        substantial_closure_bodies: &'a [bool],
        inline_dispositions: HirInlineDispositions,
        roots: RootAnalysisContext<'a>,
    ) -> Self {
        let temp_count = temp_count_for_proto(proto);
        let mut physical_root_temps = vec![false; temp_count];
        for temp in &proto.physical_root_temps {
            if let Some(protected) = physical_root_temps.get_mut(temp.index()) {
                *protected = true;
            }
        }
        Self {
            uses: TempUseScratch::new(proto, temp_count),
            order_sensitive_defs: OrderSensitiveDefWorkspace::new(temp_count),
            block_depth: 0,
            scope,
            dialect,
            roots,
            readability,
            substantial_closure_bodies,
            physical_root_temps,
            new_physical_root_temps: BTreeSet::new(),
            inline_dispositions,
        }
    }
}

pub(super) fn inline_temps_in_proto_with_facts(
    proto: &mut HirProto,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    substantial_closure_bodies: &[bool],
    roots: RootAnalysisContext<'_>,
) -> bool {
    inline_temps_in_proto_with_scope(
        proto,
        readability,
        facts,
        TempInlineScope::All,
        dialect,
        substantial_closure_bodies,
        roots,
    )
}

pub(super) fn inline_exposed_branch_value_sinks_in_proto_with_facts(
    proto: &mut HirProto,
    exposed_temps: &[TempId],
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    roots: RootAnalysisContext<'_>,
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
        roots,
    );
}

fn inline_temps_in_proto_with_scope(
    proto: &mut HirProto,
    readability: ReadabilityOptions,
    facts: &ProtoPromotionFacts,
    scope: TempInlineScope,
    dialect: DecompileDialect,
    substantial_closure_bodies: &[bool],
    roots: RootAnalysisContext<'_>,
) -> bool {
    let mut identity_sensitive_temps = stmts_reference_captured_bindings(&proto.body.stmts).temps;
    identity_sensitive_temps.extend(stmts_value_captured_bindings(&proto.body.stmts).temps);
    identity_sensitive_temps.extend(stmts_to_be_closed_temps(&proto.body.stmts));
    let temp_debug_locals = &proto.temp_debug_locals;
    let mut release_temp_is_eligible = |temp: TempId| {
        !identity_sensitive_temps.contains(&temp)
            && temp_debug_locals
                .get(temp.index())
                .is_none_or(Option::is_none)
    };
    let mut changed = matches!(&scope, TempInlineScope::All)
        && materialize_generic_for_dispatch_root_releases(
            &mut proto.body,
            facts,
            roots,
            &mut release_temp_is_eligible,
        );
    let handoff_roots = collect_lookup_gc_root_lifetimes(
        &proto.body.stmts,
        facts,
        HirExprSafety::for_dialect(dialect),
        |_| true,
    )
    .into_handoff_roots();
    let scope_roots = scope_end_copy_roots_needing_materialization(&proto.body.stmts, facts);
    let original_root_count = proto.physical_root_temps.len();
    proto
        .physical_root_temps
        .extend(scope_roots.into_iter().chain(handoff_roots));
    changed |= proto.physical_root_temps.len() != original_root_count;
    let inline_dispositions = std::mem::take(&mut proto.inline_dispositions);
    let mut workspace = TempInlineWorkspace::new(
        proto,
        scope,
        dialect,
        readability,
        substantial_closure_bodies,
        inline_dispositions,
        roots,
    );
    let mut live_use_counts = collect_block_temp_use_totals(&proto.body.stmts, &mut workspace.uses);
    let reference_captured = super::mention::stmts_reference_captured_bindings(&proto.body.stmts);
    changed |= inline_temps_in_block(
        &mut proto.body,
        &mut workspace,
        &mut live_use_counts,
        &reference_captured,
        readability,
        facts,
        &BTreeSet::new(),
    );
    let physical_root_count = proto.physical_root_temps.len();
    proto
        .physical_root_temps
        .extend(workspace.new_physical_root_temps.iter().copied());
    changed |= proto.physical_root_temps.len() != physical_root_count;
    proto.inline_dispositions = workspace.inline_dispositions;
    changed
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

fn collect_temp_root_lifetimes(
    stmts: &[HirStmt],
    facts: &ProtoPromotionFacts,
    roots: RootAnalysisContext<'_>,
    protected_temps: &[bool],
) -> (CallRootLifetimeIndices, Vec<bool>) {
    // 分析停用[LayerBoundary]：普通潜在事件由后续 locals 以
    // `collect_call_root_lifetimes(..., true, ...)` 配对并物化 owner；locals 的 TempChain
    // invalidation 会让 temp-inline 针对已物化 owner 重跑。本轮只消费 lookup 的显式 GC/
    // return 后缀证明与已完成 overwrite pair，避免把尚未配对的普通观察扩成全局 barrier。
    let call_roots = collect_call_root_lifetimes(stmts, facts, roots, false, |_| true, |_| true);
    let mut marked = call_roots.marked_stmts(stmts.len());
    collect_lookup_gc_root_lifetimes(stmts, facts, roots.safety, |_| true).mark_stmts(&mut marked);
    for (index, stmt) in stmts.iter().enumerate() {
        if !marked[index]
            && inline_candidate(stmt).is_some_and(|(temp, _)| {
                facts.is_copy_root_endpoint(temp)
                    || protected_temps.get(temp.index()).copied().unwrap_or(false)
            })
        {
            // Raw CFG facts can pair a producer in the parent block with exact overwrites in
            // multiple terminal children. The block-local collector above cannot represent that
            // relation. Same-block pairs stay owned by the precise collector (including its
            // effectful-RHS fusion); only an otherwise unrepresented endpoint is protected here.
            // A scope-end copy root is protected here only when a direct if test controls a later
            // observing arm, or when a generic-for producer consumes it before a loop-body
            // observation. Direct return/protocol result slots already transfer the same value
            // into VM-owned homes and remain eligible for their dedicated inline owners.
            marked[index] = true;
        }
    }
    (call_roots, marked)
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
    let (mut call_root_indices, mut physical_root_lifetimes) = collect_temp_root_lifetimes(
        &block.stmts,
        facts,
        workspace.roots,
        &workspace.physical_root_temps,
    );
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
            &physical_root_lifetimes,
        )
    {
        changed = true;
        captured_slots_before_stmt =
            captured_slots_before_stmts(block, facts, inherited_captured_slots);
        (call_root_indices, physical_root_lifetimes) = collect_temp_root_lifetimes(
            &block.stmts,
            facts,
            workspace.roots,
            &workspace.physical_root_temps,
        );
    }

    if matches!(workspace.scope, TempInlineScope::All)
        && inline_covered_root_copies(
            block,
            &mut workspace.uses,
            live_use_counts,
            facts,
            &captured_slots_before_stmt,
            reference_captured,
            &call_root_indices,
            &mut workspace.physical_root_temps,
            &mut workspace.new_physical_root_temps,
            &workspace.inline_dispositions,
        )
    {
        changed = true;
        captured_slots_before_stmt =
            captured_slots_before_stmts(block, facts, inherited_captured_slots);
        (call_root_indices, physical_root_lifetimes) = collect_temp_root_lifetimes(
            &block.stmts,
            facts,
            workspace.roots,
            &workspace.physical_root_temps,
        );
    }

    if inline_terminal_nil_return_pack(
        block,
        &workspace.uses,
        live_use_counts,
        facts,
        &captured_slots_before_stmt,
        &physical_root_lifetimes,
    ) {
        changed = true;
        captured_slots_before_stmt =
            captured_slots_before_stmts(block, facts, inherited_captured_slots);
        (call_root_indices, physical_root_lifetimes) = collect_temp_root_lifetimes(
            &block.stmts,
            facts,
            workspace.roots,
            &workspace.physical_root_temps,
        );
    }

    if inline_materialization_runs(
        block,
        workspace,
        live_use_counts,
        facts,
        &captured_slots_before_stmt,
        reference_captured,
        &physical_root_lifetimes,
    ) {
        changed = true;
        captured_slots_before_stmt =
            captured_slots_before_stmts(block, facts, inherited_captured_slots);
        (call_root_indices, physical_root_lifetimes) = collect_temp_root_lifetimes(
            &block.stmts,
            facts,
            workspace.roots,
            &workspace.physical_root_temps,
        );
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
        (_, physical_root_lifetimes) = collect_temp_root_lifetimes(
            &block.stmts,
            facts,
            workspace.roots,
            &workspace.physical_root_temps,
        );
    }

    // proto 级 live use count 会随成功内联同步减少；当前 block 只需保留下一条
    // 语句和 callee 物化位置。这既保留相邻内联边界，也避免每个 nested block
    // 重新遍历整棵子树。fallback 回边上任何额外读取都会使 live count 大于 1，
    // 因此不会被当成可删的 forwarding temp。
    let mut kept_rev = Vec::with_capacity(block.stmts.len());
    let mut callee_materialized_at = None;
    let mut adjacent_changed = false;

    for (index, stmt) in std::mem::take(&mut block.stmts)
        .into_iter()
        .enumerate()
        .rev()
    {
        let preserves_table_initialization =
            inline_candidate(&stmt).is_some_and(|(temp, value)| {
                kept_rev.last().is_some_and(|sink| {
                    crate::hir::table_layout::inline_changes_table_initialization(sink, temp, value)
                })
            });
        if preserves_table_initialization {
            let (temp, _) = inline_candidate(&stmt).expect("checked table operand producer");
            changed |= workspace
                .inline_dispositions
                .preserve_temp(temp, HirInlineRetentionReason::TableInitialization);
        }
        if let Some((temp, _)) = inline_candidate(&stmt)
            && temp_rebinds_captured_slot(
                temp,
                facts,
                captured_slots_before_stmt
                    .get(index)
                    .expect("forward scan should record every statement"),
            )
        {
            // 该写入的物理 home 已按引用捕获；即使其它 guard 先拒绝候选，也必须把
            // “不能删除这次 binding 写入”的结论交给后续身份提升与 AST。
            changed |= workspace
                .inline_dispositions
                .preserve_temp(temp, HirInlineRetentionReason::CapturedValueEpoch);
        }
        if let Some((temp, value)) = inline_candidate(&stmt)
            // 候选拒绝[SemanticBarrier:TableShape]：regress_471 的常量字段会触发模板裁尾，改变 #table。
            && !preserves_table_initialization
            // 候选拒绝[SemanticBarrier:Lifetime]：被 physical-root lifetime 标记的 call/lookup 结果仍承担 VM root；提前删除会改变对象存活期（regress_356）。
            && !physical_root_lifetimes[index]
            && !workspace
                .physical_root_temps
                .get(temp.index())
                .copied()
                .unwrap_or(false)
            // 候选拒绝[SemanticBarrier:Lifetime]：`t=f(); box.x=t` 中 t 是写入完成前的唯一 VM root，删除可能改变 GC/析构可观察时机。
            // A call result stored in a table can outlive the immediate write. Removing the
            // temp would remove the only lexical/VM root before a later rawset or table clear;
            // keep that producer unless a separate lifetime proof exists.
            && !(matches!(value, HirExpr::Call(_))
                && kept_rev.last().is_some_and(|next_stmt| {
                    stmt_stores_temp_in_table(next_stmt, temp)
                        && !call_result_can_enter_set_list(temp, next_stmt, &workspace.uses, facts)
                }))
            // 候选拒绝[PolicyBoundary]：DebugScope 标注该 temp 是显式源码 binding，保留其独立声明身份。
            && !workspace.uses.has_debug_local_hint(temp)
            // 候选拒绝[SemanticBarrier:Capture]：若 closure 已按引用捕获该 home，删除写入会让 closure 观察旧值；见 regress_310。
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
            // 候选拒绝[SemanticBarrier:Lifetime]：`t=t+1; return t` 若删 producer，状态槽不再完成本次更新。
            && !expr_touches_temp(value, temp)
            && let Some(next_stmt) = kept_rev.last()
            && let use_count = total_use_count(temp, live_use_counts)
            // 候选拒绝[SemanticBarrier:Lifetime]：两个以上消费不能随 producer 一并替换；零消费属于 dead-temps owner。
            // 候选拒绝[LayerBoundary]：零消费 producer 的 effect-preserving 删除由 dead-temps pass 负责。
            && (use_count == 1
                || (use_count == 2
                    && is_method_receiver_snapshot(next_stmt, temp, value)))
            // 下一条语句没有受支持的直接消费站点时，不形成相邻候选；proto 内更晚的
            // 唯一 use 属于非紧邻形状，具体站点边界由 `inline_site_in_stmt` 标记。
            && let Some(site) = inline_site_in_stmt(next_stmt, temp)
            && prefixed_block_candidate_is_safe(
                site,
                temp,
                value,
                reference_captured,
                workspace.roots.safety,
            )
            // 候选拒绝[LayerBoundary]：branch-value 定向入口只消费 terminal return，完整相邻内联由正常 temp-inline 轮次负责。
            && workspace
                .scope
                .allows_adjacent(temp, site, next_stmt, kept_rev.len() == 1)
            // 候选拒绝[SemanticBarrier:EvalOrder]：`callee=f; arg=g(); callee(arg)` 不能只把 arg 移到 callee 物化之前。
            && !call_arg_inline_crosses_materialized_callee(
                site,
                value,
                index,
                callee_materialized_at,
            )
            // 候选拒绝[SemanticBarrier:EvalOrder]：sink 中 temp 之前的 call/lookup/可变快照会观察 producer 移动；见 regress_172、regress_211。
            && !inline_crosses_evaluation_boundary(
                site,
                value,
                next_stmt,
                temp,
                reference_captured,
                workspace.dialect,
                workspace.roots.safety,
            )
            // 候选拒绝[PolicyBoundary]：复杂 child closure 保留命名 binding，避免生成多行 IIFE。
            && !substantial_result_closure_prefers_binding(
                site,
                value,
                next_stmt,
                workspace.substantial_closure_bodies,
            )
            && (site.allows(value, readability, workspace.roots.safety)
                || (site == InlineSite::CallArg
                    && workspace.uses.has_unique_definition(temp)
                    && facts.temp_is_transferred_call_argument(temp)
                    && stmt_has_argument_root_handoff(next_stmt, temp)))
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
            adjacent_changed = true;
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

    // 相邻逆向扫描可能刚把 `rhs_temp = g()` 收进 same-home overwrite，形成
    // `root = f(); overwrite = root + g()`。若等下一轮，locals 会先把这对 temp 固化为
    // source binding；因此在同一坐标压缩完成后重算 root/capture 事实，并交回同一个
    // call-root owner 原子消费。
    if adjacent_changed && matches!(workspace.scope, TempInlineScope::All) {
        let (call_roots, _) = collect_temp_root_lifetimes(
            &block.stmts,
            facts,
            workspace.roots,
            &workspace.physical_root_temps,
        );
        let captured_slots = captured_slots_before_stmts(block, facts, inherited_captured_slots);
        changed |= inline_adjacent_call_root_expression_overwrites(
            block,
            &workspace.uses,
            live_use_counts,
            facts,
            &captured_slots,
            &call_roots,
        );
    }

    workspace.block_depth -= 1;
    changed
}

fn substantial_result_closure_prefers_binding(
    site: InlineSite,
    value: &HirExpr,
    sink: &HirStmt,
    substantial_closure_bodies: &[bool],
) -> bool {
    let Some(sink) = transparent_block_head(sink) else {
        return false;
    };
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
    safety: HirExprSafety,
) -> bool {
    // 候选拒绝[SemanticBarrier:ControlFlow]：循环外 `t=f()` 不能内联进 while 条件而改成每轮调用；见 regress_172#1/#2。
    // 候选拒绝[SemanticBarrier:EvalOrder]：无 capture closure 仍会分配新 identity；`a=f(); t=function() end; g(a,t)` 不能把分配移到 `f()` 之后。
    let producer_requires_order =
        expr_requires_ordered_snapshot(value) || !safety.is_discard_safe(value);
    let producer_has_observable_eval =
        expr_observes_eval_order(value) || !safety.is_discard_safe(value);
    (site.is_repeated_region() && !is_stable_inline_value(value))
        || (producer_requires_order
            && !puc_upvalue_table_key_with_deferred_base_read(site, next_stmt, dialect)
                .is_some_and(|key| {
                    temp_precedes_observable_eval_in_expr(
                        key,
                        temp,
                        producer_has_observable_eval,
                        reference_captured,
                    )
                })
            && !temp_precedes_observable_eval_in_stmt(
                next_stmt,
                temp,
                producer_has_observable_eval,
                reference_captured,
            ))
}

fn prefixed_block_candidate_is_safe(
    site: InlineSite,
    temp: TempId,
    value: &HirExpr,
    reference_captured: &ReferenceCapturedBindings,
    safety: HirExprSafety,
) -> bool {
    // 候选拒绝[SemanticBarrier:Capture]：`t = 1; closure = function() return t end;
    // return t` 中删除 producer 会让按引用捕获的 closure 失去其 cell，即使 replacement
    // 本身没有 GC lifetime。其它 PrefixedBlock 候选由 site 限制为 proto 常量持有的
    // stable value；它们的结果不依赖 target physical home 是否继续作为 root。
    site != InlineSite::PrefixedBlock
        || (!reference_captured.temps.contains(&temp) && safety.result_is_gc_inert(value))
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

/// 物理 root 终点只证明源程序的后缀；目标还需要 constructor 的强引用载体。
/// 任意已有表可能是弱表，删除显式释放再重编译会让隐藏调用结果槽存活更久（regress_396）。
fn call_result_can_enter_set_list(
    temp: TempId,
    stmt: &HirStmt,
    uses: &TempUseScratch,
    facts: &ProtoPromotionFacts,
) -> bool {
    let HirStmt::TableSetList(set_list) = stmt else {
        return false;
    };
    let HirExpr::TempRef(seed) = set_list.base else {
        return false;
    };
    uses.has_unique_definition(temp)
        && facts.call_result_root_ends_after_value_use(temp)
        && facts.is_direct_table_seed_temp(seed)
        && facts.trusted_temp_home_slot(seed).is_some()
}

fn stmt_stores_temp_in_table(stmt: &HirStmt, temp: TempId) -> bool {
    let Some(stmt) = transparent_block_head(stmt) else {
        return false;
    };
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
        HirStmt::GlobalDecl(global_decl) => global_decl.values.fixed.iter().any(|value| {
            matches!(value, HirExpr::TempRef(value_temp) if *value_temp == temp)
                || (matches!(value, HirExpr::TableConstructor(_)) && expr_touches_temp(value, temp))
        }),
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
        let Some(pair) = call_roots
            .overwrite_pairs(overwrite_index)
            .find(|pair| pair.root_index() == root_index)
        else {
            continue;
        };
        let Some((root, HirExpr::Call(call))) = inline_candidate(&block.stmts[root_index]) else {
            continue;
        };
        let Some((target, overwrite)) = inline_candidate(&block.stmts[overwrite_index]) else {
            continue;
        };
        if root == target {
            continue;
        }
        // 候选拒绝[SemanticBarrier:Lifetime]：例如 overwrite 后再次读取 root 时，删除 producer 会丢失原 call result。
        if total_use_count(root, live_use_counts) != 1 {
            continue;
        }
        // 候选拒绝[PolicyBoundary]：DebugScope 标注的 root/target 保留独立源码 binding 身份。
        if scratch.has_debug_local_hint(root) || scratch.has_debug_local_hint(target) {
            continue;
        }
        if !call_root_overwrite_is_inlineable(overwrite, root) {
            continue;
        }
        let mut captured_slots = captured_slots_before_stmt
            .get(overwrite_index)
            .expect("capture snapshots must cover the call-root overwrite")
            .clone();
        facts.collect_captured_home_slots_in_stmt(
            &block.stmts[overwrite_index],
            &mut captured_slots,
        );
        // 候选拒绝[SemanticBarrier:Capture]：已有 capture 或 overwrite RHS 新建的 closure
        // 若引用 root home，删除 producer 会让它观察 overwrite 前的旧 cell。
        if captured_slots.contains(&pair.home()) {
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

/// 由 root_lifetimes 冻结的同值覆盖计划；use_sites 只描述此次替换的 HIR 位置。
struct CoveredRootCopy {
    target: TempId,
    source: TempId,
    copy_index: usize,
    target_home: HomeSlotKey,
    source_home: HomeSlotKey,
    use_sites: Vec<usize>,
}

/// 统一提交 scope-end 死复制与 SELF receiver 的根交接。
/// 生命周期/协议来自 root_lifetimes，本层检查 debug、capture、TBC 与当前读取并保留
/// source 的 PhysicalRoot。例：t=u; u=nil; dead=t; callback() 删除 dead，保留 t 的求值点。
#[allow(clippy::too_many_arguments)]
fn inline_covered_root_copies(
    block: &mut HirBlock,
    scratch: &mut TempUseScratch,
    live_use_counts: &mut [usize],
    facts: &ProtoPromotionFacts,
    captured_slots_before_stmt: &CapturedSlotSnapshots,
    reference_captured: &ReferenceCapturedBindings,
    call_roots: &CallRootLifetimeIndices,
    physical_root_temps: &mut [bool],
    new_physical_root_temps: &mut BTreeSet<TempId>,
    inline_dispositions: &HirInlineDispositions,
) -> bool {
    let captured_homes = complete_reference_captured_home_slots(reference_captured, facts);
    let mut identity_sensitive = stmts_value_captured_bindings(&block.stmts).temps;
    identity_sensitive.extend(stmts_to_be_closed_temps(&block.stmts));
    let dead_copies = scope_end_copy_root_handoffs(&block.stmts, facts)
        .into_iter()
        // 仍有源码读取的 source 已有自己的 use owner；不额外冻结它而阻止普通 copy 消解。
        .filter(|handoff| total_use_count(handoff.source, live_use_counts) == 1)
        .map(|handoff| CoveredRootCopy {
            target: handoff.target,
            source: handoff.source,
            copy_index: handoff.copy_index,
            target_home: handoff.target_home,
            source_home: handoff.source_home,
            use_sites: Vec::new(),
        });
    let method_copies = call_roots
        .method_receiver_handoffs(&block.stmts, facts)
        .into_iter()
        .map(|handoff| {
            debug_assert!(handoff.sink_index() < handoff.overwrite_index());
            CoveredRootCopy {
                target: handoff.target(),
                source: handoff.source(),
                copy_index: handoff.producer_index(),
                target_home: handoff.target_home(),
                source_home: handoff.source_home(),
                use_sites: vec![handoff.lookup_index(), handoff.sink_index()],
            }
        });
    let plan = dead_copies.chain(method_copies).find(|handoff| {
        total_use_count(handoff.target, live_use_counts) == handoff.use_sites.len()
            && !scratch.has_debug_local_hint(handoff.target)
            && !inline_dispositions.temp(handoff.target).must_preserve()
            && !identity_sensitive.contains(&handoff.target)
            && !identity_sensitive.contains(&handoff.source)
            && !captured_homes.contains(&handoff.target_home)
            && !captured_homes.contains(&handoff.source_home)
            && !reference_captured.temps.contains(&handoff.target)
            && !reference_captured.temps.contains(&handoff.source)
            && materialization_run_candidate_is_safe(
                handoff.target,
                &HirExpr::TempRef(handoff.source),
                handoff.copy_index,
                scratch,
                facts,
                captured_slots_before_stmt,
            )
    });
    let Some(plan) = plan else {
        return false;
    };
    let replacement = HirExpr::TempRef(plan.source);
    for index in plan.use_sites {
        replace_temp_in_stmt(&mut block.stmts[index], plan.target, &replacement);
        remove_live_use(live_use_counts, plan.target);
        collect_expr_temp_uses_summary(&replacement, scratch).add_to_totals(live_use_counts);
    }
    block.stmts.remove(plan.copy_index);
    remove_live_use(live_use_counts, plan.source);
    physical_root_temps[plan.source.index()] = true;
    new_physical_root_temps.insert(plan.source);
    true
}

fn call_root_overwrite_is_inlineable(expr: &HirExpr, root: TempId) -> bool {
    match expr {
        HirExpr::Binary(binary) => {
            matches!(&binary.lhs, HirExpr::TempRef(source) if *source == root)
        }
        HirExpr::LogicalOr(logical) => {
            matches!(&logical.lhs, HirExpr::TempRef(source) if *source == root)
        }
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
    safety: HirExprSafety,
    removed_stmts: &'a mut [bool],
}

#[derive(Clone, Copy)]
enum EagerConditionCallCallee {
    Temp(TempId),
    Other,
}

fn first_eager_condition_call_callee(expr: &HirExpr) -> Option<EagerConditionCallCallee> {
    match expr {
        HirExpr::Call(call) => Some(match &call.callee {
            HirExpr::TempRef(temp) => EagerConditionCallCallee::Temp(*temp),
            _ => EagerConditionCallCallee::Other,
        }),
        HirExpr::Unary(unary) => first_eager_condition_call_callee(&unary.expr),
        HirExpr::Binary(binary) => first_eager_condition_call_callee(&binary.lhs)
            .or_else(|| first_eager_condition_call_callee(&binary.rhs)),
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            // The RHS is conditional. A producer evaluated before the If cannot move there.
            first_eager_condition_call_callee(&logical.lhs)
        }
        HirExpr::TableAccess(access) => first_eager_condition_call_callee(&access.base)
            .or_else(|| first_eager_condition_call_callee(&access.key)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Decision(_)
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => None,
    }
}

fn condition_materialization_value_is_supported(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_) => true,
        HirExpr::TableAccess(access) => {
            condition_materialization_value_is_supported(&access.base)
                && condition_materialization_value_is_supported(&access.key)
        }
        HirExpr::Unary(unary) => condition_materialization_value_is_supported(&unary.expr),
        HirExpr::Binary(binary) => {
            condition_materialization_value_is_supported(&binary.lhs)
                && condition_materialization_value_is_supported(&binary.rhs)
        }
        HirExpr::LogicalAnd(_)
        | HirExpr::LogicalOr(_)
        | HirExpr::Call(_)
        | HirExpr::Decision(_)
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}

struct EagerConditionMaterializationProof<'a> {
    scratch: &'a mut TempUseScratch,
    live_use_counts: &'a mut [usize],
    facts: &'a ProtoPromotionFacts,
    captured_slots_before_stmt: &'a CapturedSlotSnapshots,
    order_sensitive_defs: &'a OrderSensitiveDefWorkspace,
    reference_captured: &'a ReferenceCapturedBindings,
    dialect: DecompileDialect,
    safety: HirExprSafety,
}

fn inline_eager_condition_materialization_run(
    block: &mut HirBlock,
    run_start: usize,
    run_end: usize,
    physical_root_lifetimes: &[bool],
    proof: &mut EagerConditionMaterializationProof<'_>,
    removed_stmts: &mut [bool],
) -> bool {
    let Some(HirStmt::If(if_stmt)) = block.stmts.get(run_end) else {
        return false;
    };
    let Some(EagerConditionCallCallee::Temp(callee_temp)) =
        first_eager_condition_call_callee(&if_stmt.cond)
    else {
        return false;
    };
    if physical_root_lifetimes[run_start..run_end]
        .iter()
        .any(|preserve| *preserve)
    {
        // A real VM root cannot be consumed merely because the same value reaches a condition.
        return false;
    }

    let mut positions = BTreeMap::new();
    for index in run_start..run_end {
        let Some((temp, value)) = inline_candidate(&block.stmts[index]) else {
            return false;
        };
        if !condition_materialization_value_is_supported(value)
            || positions.insert(temp, index).is_some()
        {
            return false;
        }
    }
    if !positions.contains_key(&callee_temp) {
        return false;
    }

    for (&temp, &position) in &positions {
        let (_, value) = inline_candidate(&block.stmts[position])
            .expect("condition materialization position must retain its scalar definition");
        let mut dependencies_precede = true;
        collect_expr_temp_uses_summary(value, proof.scratch).for_each(|dependency, _| {
            if positions
                .get(&dependency)
                .is_some_and(|dependency_position| *dependency_position >= position)
            {
                dependencies_precede = false;
            }
        });
        if !dependencies_precede || total_use_count(temp, proof.live_use_counts) != 1 {
            return false;
        }
    }

    let mut rewritten_sink = block.stmts[run_end].clone();
    let mut removed_temps = Vec::with_capacity(run_end - run_start);
    for index in (run_start..run_end).rev() {
        let (temp, value) = inline_candidate(&block.stmts[index])
            .expect("condition materialization run must retain scalar definitions");
        if collect_stmt_temp_uses(&rewritten_sink, proof.scratch).count(temp) != 1 {
            // Every producer must belong to the dependency closure of the eager call. This also
            // rejects unrelated dead assignments instead of absorbing dead-temps responsibility.
            return false;
        }
        let Some(site) = inline_site_in_stmt(&rewritten_sink, temp) else {
            return false;
        };
        if matches!(
            site,
            InlineSite::ConditionalNested
                | InlineSite::RepeatedNested
                | InlineSite::LoopCondition
                | InlineSite::LoopHead
                | InlineSite::PrefixedBlock
        ) || !materialization_run_candidate_is_safe(
            temp,
            value,
            index,
            proof.scratch,
            proof.facts,
            proof.captured_slots_before_stmt,
        ) || !prefixed_block_candidate_is_safe(
            site,
            temp,
            value,
            proof.reference_captured,
            proof.safety,
        ) || arg_value_forwards_prior_order_sensitive_expr(
            value,
            run_start,
            proof.order_sensitive_defs,
        ) || inline_crosses_evaluation_boundary(
            site,
            value,
            &rewritten_sink,
            temp,
            proof.reference_captured,
            proof.dialect,
            proof.safety,
        ) {
            return false;
        }
        replace_temp_in_stmt(&mut rewritten_sink, temp, value);
        removed_temps.push(temp);
    }

    block.stmts[run_end] = rewritten_sink;
    removed_stmts[run_start..run_end].fill(true);
    for temp in removed_temps {
        remove_live_use(proof.live_use_counts, temp);
    }
    true
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
        // 候选拒绝[SemanticBarrier:Lifetime]：alias 链节点有额外 use 时不能随 run 整段删除。
        // 候选拒绝[SemanticBarrier:EvalOrder]：非 repeatable 值或转发更早 observable def 会被延后/重复求值。
        // 候选拒绝[PolicyBoundary]：nested sink 继续服从固定复杂度展示阈值。
        // 候选拒绝[SemanticBarrier:Capture]：capture/self-rebind 改写会改变闭包或状态所见值。
        // 候选拒绝[PolicyBoundary]：DebugScope 标注的 temp 保留独立源码 binding 身份。
        if total_use_count(temp, context.live_use_counts) != 1
            || !context.safety.is_repeatable(value)
            || !InlineSite::Nested.allows(value, context.readability, context.safety)
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
        // Pure substitution 以 temp 为 DAG 节点；同一 canonical temp 的多个 def 属于
        // 不同 epoch，不能让 map insertion 静默覆盖，留给后面的逐项路径处理。
        if positions.insert(temp, index).is_some() {
            return false;
        }
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
        // 候选拒绝[LayerBoundary]：不在 sink 依赖闭包内的是 dead assignment，由 dead-temps owner 处理。
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
            // 候选拒绝[SemanticBarrier:EvalOrder]：forward edge/cycle 会把依赖移动到其定义之前或改变求值拓扑。
            return false;
        }
    }

    let mut rewritten_sink = block.stmts[run_end].clone();
    assert_ne!(
        replace_temps_in_stmt(&mut rewritten_sink, &replacements),
        0,
        "pure materialization DAG must replace its direct call callee"
    );
    let mut remaining = false;
    collect_stmt_temp_uses(&rewritten_sink, context.scratch).for_each(|temp, _| {
        remaining |= positions.contains_key(&temp);
    });
    assert!(
        !remaining,
        "acyclic materialization substitution must consume every run temp"
    );

    // The source call already establishes that `callee_temp` is the direct call
    // target, and `callee_index == run_start` makes it a member of this complete map.
    assert!(
        replacements.contains_key(&callee_temp),
        "pure materialization map must contain its validated callee"
    );
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
    physical_root_lifetimes: &[bool],
) -> bool {
    // child block 已全部处理完才会到这里，因此同一个 proto 级 workspace 不会覆盖
    // 仍在活跃递归 frame 中的 parent 索引。
    let TempInlineWorkspace {
        uses,
        order_sensitive_defs,
        scope,
        dialect,
        roots: RootAnalysisContext { safety, .. },
        readability,
        ..
    } = workspace;
    order_sensitive_defs.rebuild(&block.stmts);
    let reference_captured_home_slots =
        complete_reference_captured_home_slots(reference_captured, facts);
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
        if matches!(scope, TempInlineScope::All)
            && inline_eager_condition_materialization_run(
                block,
                run_start,
                run_end,
                physical_root_lifetimes,
                &mut EagerConditionMaterializationProof {
                    scratch: uses,
                    live_use_counts,
                    facts,
                    captured_slots_before_stmt,
                    order_sensitive_defs,
                    reference_captured,
                    dialect: *dialect,
                    safety: *safety,
                },
                &mut removed_stmts,
            )
        {
            changed = true;
            index = run_end + 1;
            continue;
        }
        if physical_root_lifetimes[run_start..run_end]
            .iter()
            .any(|preserve| *preserve)
        {
            // 候选拒绝[SemanticBarrier:Lifetime]：run 内仍有 call/lookup result 充当显式 GC 或后续写前的 VM root，不能整段删除（regress_356）。
            index = run_end;
            continue;
        }
        if scope.allows_open_return()
            && inline_open_return_fixed_alias_run(
                block,
                run_start..run_end,
                live_use_counts,
                OpenReturnFixedAliasProof {
                    scratch: uses,
                    facts,
                    captured_slots_before_stmt,
                    reference_captured_home_slots: &reference_captured_home_slots,
                },
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
            live_use_counts,
            NumericForHeaderProof {
                scratch: uses,
                facts,
                safety: *safety,
                reference_captured,
                captured_slots_before_stmt,
                reference_captured_home_slots: &reference_captured_home_slots,
            },
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
        // 同一 canonical temp 可能由 loop-state coalescing 产生多个 def；直接调用读取的
        // 是 run 内最后一次写入，较早 producer 不属于本次融合事务。
        let Some(callee_index) = (run_start..run_end).rfind(|candidate_index| {
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
            // 候选拒绝[LayerBoundary]：branch-value 定向轮次仅接管 root global call + terminal exposed sink，其余留给完整 temp-inline。
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
            // 候选拒绝[SemanticBarrier:Capture]：callee home 被引用捕获或 producer 自引用时，删写会改变 closure/状态所见值。
            // 候选拒绝[PolicyBoundary]：DebugScope 标注的 callee 保留独立源码 binding 身份。
            // 候选拒绝[SemanticBarrier:Lifetime]：callee 存在额外消费时不能随本 call 一并删除。
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
            safety: *safety,
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
            // 候选拒绝[SemanticBarrier:Lifetime]：除 method 协议的同次 receiver 求值外，多 use 仍需原 temp 值。
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
            if matches!(value, HirExpr::Call(_))
                && stmt_stores_temp_in_table(&rewritten_sink, temp)
                && !call_result_can_enter_set_list(temp, &rewritten_sink, uses, facts)
            {
                // 候选拒绝[SemanticBarrier:Lifetime]：call result 写表前由 temp 保持存活，删除会改变 VM root 生命周期。
                complete_run = false;
                break;
            }
            if use_count == 0 {
                if candidate_is_safe && safety.is_discard_safe(value) {
                    discarded_uses.push(collect_expr_temp_uses_summary(value, uses));
                    continue;
                }
                // 候选拒绝[SemanticBarrier:EvalOrder]：零 use 但不可安全丢弃的 call/lookup/allocation 仍是原序列中的可观察事件。
                // 候选拒绝[SemanticBarrier:Capture]：被捕获/self-rebinding 的零 use 写也不能由 run 删除。
                // 候选拒绝[PolicyBoundary]：DebugScope 标注的零 use temp 仍保留源码 binding 身份。
                complete_run = false;
                break;
            }
            let Some(site) = inline_site_in_stmt(&rewritten_sink, temp) else {
                if collect_stmt_temp_uses(&rewritten_sink, uses).count(temp) == 0 {
                    let planned_discard_use_count = discarded_uses
                        .iter()
                        .map(|discarded: &TempUseSummary| discarded.count(temp))
                        .sum::<usize>();
                    if planned_discard_use_count == use_count
                        && candidate_is_safe
                        && safety.is_discard_safe(value)
                    {
                        // 逆序扫描已经证明该 temp 的全部 use 都位于随后将删除的纯表达式中；
                        // 把当前 value 的依赖继续并入 discard delta，整段提交时统一扣除。
                        discarded_uses.push(collect_expr_temp_uses_summary(value, uses));
                        continue;
                    }
                    // 候选拒绝[SemanticBarrier:Lifetime]：至少一份 live use 位于本次 sink/计划删除集之外，
                    // 删除 producer 会让该 use 失去原值。
                    // 候选拒绝[SemanticBarrier:EvalOrder]：即使唯一 use 位于计划删除集，带事件的 value 也不能随之丢弃。
                    // 候选拒绝[SemanticBarrier:Capture]：被捕获/self-rebinding 的 producer 不能作为纯依赖删除。
                    // 候选拒绝[PolicyBoundary]：DebugScope 标注的 temp 保留源码 binding 身份。
                    complete_run = false;
                    break;
                }
                // sink 内 use 的 Closure capture 等明确边界由 site classifier 标记。
                complete_run = false;
                break;
            };
            if !candidate_is_safe
                || !prefixed_block_candidate_is_safe(site, temp, value, reference_captured, *safety)
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
                        *safety,
                    ))
            {
                // 候选拒绝[SemanticBarrier:Capture]：candidate home capture/self-rebind 会改变 closure 或状态所见值。
                // 候选拒绝[PolicyBoundary]：DebugScope 标注的 candidate 保留源码 binding 身份。
                // 候选拒绝[SemanticBarrier:EvalOrder]：参数转发更早的 order-sensitive def，或 sink 前缀含 observable eval，移动会重排事件。
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
        let callee_site = inline_site_in_stmt(&rewritten_sink, callee_temp)
            .expect("non-callee substitutions must preserve the direct call callee");
        assert!(
            callee_site.is_call_callee(),
            "materialization run callee must remain in the direct call position"
        );
        if inline_crosses_evaluation_boundary(
            callee_site,
            &callee_value,
            &rewritten_sink,
            callee_temp,
            reference_captured,
            *dialect,
            *safety,
        ) {
            // 候选拒绝[SemanticBarrier:EvalOrder]：callee 前有可观察事件时，内联会把其求值延后。
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
    physical_root_lifetimes: &[bool],
) -> bool {
    let Some(plan) = root_open_return_nil_pack_plan(
        block,
        scratch,
        live_use_counts,
        facts,
        captured_slots_before_stmt,
        physical_root_lifetimes,
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
    physical_root_lifetimes: &[bool],
) -> Option<RootOpenReturnNilPackPlan> {
    let return_index = block.stmts.len().checked_sub(1)?;
    let HirStmt::Return(ret) = &block.stmts[return_index] else {
        return None;
    };
    let tail = ret.values.tail.as_ref()?;
    if tail.exact_width().is_some() || !matches!(tail.as_expr(), HirExpr::Call(_)) {
        return None;
    }
    let captured_slots = captured_slots_before_stmt
        .get(return_index)
        .expect("capture snapshots must cover the root return");

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
        {
            continue;
        }
        if *physical_root_lifetimes
            .get(assignment_index)
            .expect("physical-root snapshots must cover the open-return nil-pack assignment")
        {
            // 候选拒绝[SemanticBarrier:Lifetime]：nil producer 终止了仍可被 tail call 的 GC 观察到的物理 root（regress_360）。
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
        let mut non_entry_physical_read_protected_slots = BTreeSet::new();
        let mut targets_are_safe = true;
        let mut has_non_entry_physical_target = false;
        let mut all_physical_targets_have_exact_homes = true;
        for target in &targets {
            // 候选拒绝[SemanticBarrier:Lifetime]：额外 use 会继续观察原 nil 写入后的 temp。
            if total_use_count(*target, live_use_counts) != 1
                // 候选拒绝[PolicyBoundary]：DebugScope 标注的 temp 保留独立源码 binding 身份。
                || scratch.has_debug_local_hint(*target)
            {
                targets_are_safe = false;
                break;
            }
            let possible_homes = facts.complete_temp_home_slots(*target);
            // 候选拒绝[SemanticBarrier:Capture]：任一可能 target home 已被引用捕获时，
            // 删除 nil 写会让 closure 继续观察旧值。
            if possible_homes
                .iter()
                .any(|slot| captured_slots.contains(slot))
            {
                targets_are_safe = false;
                break;
            }
            let is_non_entry_physical =
                !facts.overwrites_entry_nil(*target) && !possible_homes.is_empty();
            has_non_entry_physical_target |= is_non_entry_physical;
            if is_non_entry_physical {
                non_entry_physical_read_protected_slots.extend(possible_homes.iter().copied());
            }
            all_physical_targets_have_exact_homes &=
                possible_homes.is_empty() || facts.trusted_temp_home_slot(*target).is_some();
            target_slots.extend(possible_homes);
        }
        if has_non_entry_physical_target && !all_physical_targets_have_exact_homes {
            // 候选拒绝[SemanticBarrier:Lifetime]：merged physical target 可沿不同路径落入
            // 不同 raw home；删除 nil 写会让实际 home 的旧资源继续跨 tail call/GC 存活，
            // 而单个静态 target 无法指认应结束的 root epoch。明确 home-free target 不参与。
            targets_are_safe = false;
        }
        if targets_are_safe {
            match root_open_return_remaining_read_relation(
                ret,
                fixed_start,
                targets.len(),
                &non_entry_physical_read_protected_slots,
                facts,
            ) {
                RootNilPackGapReadRelation::Disjoint => {}
                RootNilPackGapReadRelation::Overlap => {
                    // 候选拒绝[SemanticBarrier:ValueFlow]：return 的其它 fixed/tail 表达式若通过
                    // alias binding 读取 target home，删除 nil 写会让它读到此前 value。
                    targets_are_safe = false;
                }
            }
        }
        let protected_temps = targets.iter().copied().collect::<BTreeSet<_>>();
        let referenced_labels = count_label_references(&block.stmts)
            .into_keys()
            .collect::<BTreeSet<_>>();
        if !targets_are_safe
            || !block.stmts[assignment_index + 1..return_index]
                .iter()
                .all(|stmt| {
                    root_nil_pack_gap_preserves_slots_with_context(
                        stmt,
                        &protected_temps,
                        &target_slots,
                        &non_entry_physical_read_protected_slots,
                        &referenced_labels,
                        facts,
                    )
                })
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
/// 未失效的 home、无 debug/capture 且每个目标只有唯一 return 读取时才成立；带 tail 的
/// return、局部/参数目标和任何不可信 home 继续保留原始并行写。
fn inline_terminal_nil_return_pack(
    block: &mut HirBlock,
    scratch: &TempUseScratch,
    live_use_counts: &mut [usize],
    facts: &ProtoPromotionFacts,
    captured_slots_before_stmt: &CapturedSlotSnapshots,
    physical_root_lifetimes: &[bool],
) -> bool {
    let Some(return_index) = block.stmts.len().checked_sub(1) else {
        return false;
    };
    let Some(assign_index) = return_index.checked_sub(1) else {
        return false;
    };
    if *physical_root_lifetimes
        .get(assign_index)
        .expect("physical-root snapshots must cover the terminal nil-pack assignment")
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：nil producer 仍是 physical-root lifetime owner，删除会提前释放其先前值（regress_356）。
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

    let captured_slots = captured_slots_before_stmt
        .get(assign_index)
        .expect("capture snapshots must cover the terminal nil-pack assignment");
    for target in &targets {
        let possible_homes = facts.complete_temp_home_slots(*target);
        // 候选拒绝[SemanticBarrier:Capture]：closure 已引用捕获任一可能 target home 时，
        // 删除 nil 写会让其继续观察旧值。
        if possible_homes
            .iter()
            .any(|slot| captured_slots.contains(slot))
        {
            return false;
        }
        // 候选拒绝[PolicyBoundary]：DebugScope 标注的 temp 保留独立源码 binding 身份。
        if scratch.has_debug_local_hint(*target) {
            return false;
        }
        // 候选拒绝[SemanticBarrier:Lifetime]：额外 use 会继续观察被删除的 nil 写或 temp identity。
        if total_use_count(*target, live_use_counts) != 1 {
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

fn root_nil_pack_gap_preserves_slots_with_context(
    stmt: &HirStmt,
    protected_temps: &BTreeSet<TempId>,
    protected_slots: &BTreeSet<HomeSlotKey>,
    read_protected_slots: &BTreeSet<HomeSlotKey>,
    referenced_labels: &BTreeSet<crate::hir::common::HirLabelId>,
    facts: &ProtoPromotionFacts,
) -> bool {
    match root_nil_pack_gap_read_relation(stmt, read_protected_slots, facts) {
        RootNilPackGapReadRelation::Disjoint => {}
        RootNilPackGapReadRelation::Overlap => {
            // 候选拒绝[SemanticBarrier:ValueFlow]：gap 通过另一个 binding 读取同一 home 时，
            // 原程序看到 nil overwrite，删除后却会看到此前 value；target 的唯一 use 不能覆盖 alias read。
            return false;
        }
    }
    match stmt {
        HirStmt::Assign(assign) => {
            // 候选拒绝[SemanticBarrier:EvalOrder]：`t=nil; t=x; return t` 若跨过同槽写，会错误恢复成 `return nil`。
            assign.targets.iter().all(|target| {
                if matches!(target, HirLValue::Temp(temp) if protected_temps.contains(temp)) {
                    return false;
                }
                if protected_slots.is_empty() {
                    return true;
                }
                direct_lvalue_possible_home_slots(target, facts).is_disjoint(protected_slots)
            })
        }
        HirStmt::LocalDecl(local_decl) => {
            // 候选拒绝[SemanticBarrier:EvalOrder]：gap local 写复用 protected home 会覆盖 return 应读取的 nil temp。
            if protected_slots.is_empty() {
                return true;
            }
            local_decl.bindings.iter().all(|local| {
                facts
                    .complete_local_home_slots(*local)
                    .is_disjoint(protected_slots)
            })
        }
        HirStmt::GlobalDecl(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::CallStmt(_) => true,
        HirStmt::ToBeClosed(to_be_closed) => protected_slots
            .iter()
            .all(|home| home.slot() != to_be_closed.reg_index),
        HirStmt::Close(close) => {
            // 候选拒绝[SemanticBarrier:Lifetime]：关闭范围若包含 nil target 的物理槽，
            // 删除 overwrite 会让 cleanup 看到此前 value，而不是 nil（regress_433 覆盖无关槽可通过）。
            protected_slots
                .iter()
                .all(|home| home.slot() < close.from_reg)
        }
        HirStmt::If(if_stmt) => {
            root_nil_pack_gap_block_preserves_slots(
                &if_stmt.then_block,
                protected_temps,
                protected_slots,
                read_protected_slots,
                referenced_labels,
                facts,
            ) && if_stmt.else_block.as_ref().is_none_or(|else_block| {
                root_nil_pack_gap_block_preserves_slots(
                    else_block,
                    protected_temps,
                    protected_slots,
                    read_protected_slots,
                    referenced_labels,
                    facts,
                )
            })
        }
        HirStmt::While(while_stmt) => root_nil_pack_gap_block_preserves_slots(
            &while_stmt.body,
            protected_temps,
            protected_slots,
            read_protected_slots,
            referenced_labels,
            facts,
        ),
        HirStmt::Repeat(repeat_stmt) => root_nil_pack_gap_block_preserves_slots(
            &repeat_stmt.body,
            protected_temps,
            protected_slots,
            read_protected_slots,
            referenced_labels,
            facts,
        ),
        HirStmt::NumericFor(numeric_for) => {
            facts
                .complete_local_home_slots(numeric_for.binding)
                .is_disjoint(protected_slots)
                && root_nil_pack_gap_block_preserves_slots(
                    &numeric_for.body,
                    protected_temps,
                    protected_slots,
                    read_protected_slots,
                    referenced_labels,
                    facts,
                )
        }
        HirStmt::GenericFor(generic_for) => {
            generic_for.bindings.iter().all(|binding| {
                facts
                    .complete_local_home_slots(*binding)
                    .is_disjoint(protected_slots)
            }) && root_nil_pack_gap_block_preserves_slots(
                &generic_for.body,
                protected_temps,
                protected_slots,
                read_protected_slots,
                referenced_labels,
                facts,
            )
        }
        HirStmt::Block(block) => root_nil_pack_gap_block_preserves_slots(
            block,
            protected_temps,
            protected_slots,
            read_protected_slots,
            referenced_labels,
            facts,
        ),
        // Return/loop exits cannot reach the rewritten terminal sink on this path. Its expressions,
        // direct roots and cleanup effects were already checked above and by the assignment snapshot.
        HirStmt::Return(_) | HirStmt::Break | HirStmt::Continue => true,
        // 候选拒绝[SemanticBarrier:ControlFlow]：`goto L; t=nil; ::L::; return t, tail()`
        // 可从外部跳过 nil 写；把终态读取改成 literal nil 会错误覆盖该路径的旧 epoch。
        HirStmt::Goto(_) => false,
        HirStmt::Label(label) => {
            // 无引用 label 不改变路径；有引用 label 可能是上述外部跳入点，缺 CFG dominance 时保留。
            !referenced_labels.contains(&label.id)
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RootNilPackGapReadRelation {
    Disjoint,
    Overlap,
}

fn root_nil_pack_gap_read_relation(
    stmt: &HirStmt,
    protected_slots: &BTreeSet<HomeSlotKey>,
    facts: &ProtoPromotionFacts,
) -> RootNilPackGapReadRelation {
    if protected_slots.is_empty() {
        return RootNilPackGapReadRelation::Disjoint;
    }
    if direct_binding_read_homes_in_stmt(stmt, facts).is_disjoint(protected_slots) {
        RootNilPackGapReadRelation::Disjoint
    } else {
        RootNilPackGapReadRelation::Overlap
    }
}

fn root_open_return_remaining_read_relation(
    ret: &crate::hir::common::HirReturn,
    fixed_start: usize,
    target_count: usize,
    protected_slots: &BTreeSet<HomeSlotKey>,
    facts: &ProtoPromotionFacts,
) -> RootNilPackGapReadRelation {
    if protected_slots.is_empty() {
        return RootNilPackGapReadRelation::Disjoint;
    }
    let mut collector = DirectBindingReadHomeCollector {
        facts,
        homes: BTreeSet::new(),
    };
    for (index, value) in ret.values.fixed.iter().enumerate() {
        if index < fixed_start || index >= fixed_start + target_count {
            visit_expr(value, &mut collector);
        }
    }
    if let Some(tail) = &ret.values.tail {
        visit_expr(tail.as_expr(), &mut collector);
    }
    if collector.homes.is_disjoint(protected_slots) {
        RootNilPackGapReadRelation::Disjoint
    } else {
        RootNilPackGapReadRelation::Overlap
    }
}

fn direct_binding_read_homes_in_stmt(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
) -> BTreeSet<HomeSlotKey> {
    let mut collector = DirectBindingReadHomeCollector {
        facts,
        homes: BTreeSet::new(),
    };
    visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.homes
}

fn direct_binding_read_homes_in_expr(
    expr: &HirExpr,
    facts: &ProtoPromotionFacts,
) -> BTreeSet<HomeSlotKey> {
    let mut collector = DirectBindingReadHomeCollector {
        facts,
        homes: BTreeSet::new(),
    };
    visit_expr(expr, &mut collector);
    collector.homes
}

struct DirectBindingReadHomeCollector<'a> {
    facts: &'a ProtoPromotionFacts,
    homes: BTreeSet<HomeSlotKey>,
}

impl DirectBindingReadHomeCollector<'_> {
    fn note_homes(&mut self, homes: BTreeSet<HomeSlotKey>) {
        self.homes.extend(homes);
    }
}

impl HirVisitor for DirectBindingReadHomeCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::ParamRef(param) => {
                self.note_homes(self.facts.complete_param_home_slots(*param));
            }
            HirExpr::LocalRef(local) => {
                self.note_homes(self.facts.complete_local_home_slots(*local));
            }
            HirExpr::TempRef(temp) => {
                self.note_homes(self.facts.complete_temp_home_slots(*temp));
            }
            _ => {}
        }
    }
}

fn root_nil_pack_gap_block_preserves_slots(
    block: &HirBlock,
    protected_temps: &BTreeSet<TempId>,
    protected_slots: &BTreeSet<HomeSlotKey>,
    read_protected_slots: &BTreeSet<HomeSlotKey>,
    referenced_labels: &BTreeSet<crate::hir::common::HirLabelId>,
    facts: &ProtoPromotionFacts,
) -> bool {
    block.stmts.iter().all(|stmt| {
        root_nil_pack_gap_preserves_slots_with_context(
            stmt,
            protected_temps,
            protected_slots,
            read_protected_slots,
            referenced_labels,
            facts,
        )
    })
}

#[cfg(test)]
fn root_nil_pack_gap_preserves_slots(
    stmt: &HirStmt,
    protected_temps: &BTreeSet<TempId>,
    protected_slots: &BTreeSet<HomeSlotKey>,
    facts: &ProtoPromotionFacts,
) -> bool {
    root_nil_pack_gap_preserves_slots_with_context(
        stmt,
        protected_temps,
        protected_slots,
        protected_slots,
        &BTreeSet::new(),
        facts,
    )
}

fn direct_lvalue_possible_home_slots(
    target: &HirLValue,
    facts: &ProtoPromotionFacts,
) -> BTreeSet<HomeSlotKey> {
    match target {
        HirLValue::Param(param) => facts.complete_param_home_slots(*param),
        HirLValue::Temp(temp) => facts.complete_temp_home_slots(*temp),
        HirLValue::Local(local) => facts.complete_local_home_slots(*local),
        HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => BTreeSet::new(),
    }
}

fn inline_numeric_for_stable_header_aliases(
    block: &mut HirBlock,
    run: std::ops::Range<usize>,
    live_use_counts: &mut [usize],
    proof: NumericForHeaderProof<'_>,
    removed_stmts: &mut [bool],
) -> bool {
    let (run_start, run_end) = (run.start, run.end);
    if !matches!(block.stmts.get(run_end), Some(HirStmt::NumericFor(_))) {
        return false;
    }

    let mut rewritten_sink = block.stmts[run_end].clone();
    let mut last_def_indices = vec![None; proof.scratch.temp_count()];
    for candidate_index in run_start..run_end {
        let (temp, _) = inline_candidate(&block.stmts[candidate_index])
            .expect("numeric-for materialization run must contain only scalar temp definitions");
        last_def_indices[temp.index()] = Some(candidate_index);
    }
    let mut changed = false;
    for candidate_index in run_start..run_end {
        if removed_stmts[candidate_index] {
            continue;
        }
        let Some((temp, value)) = inline_candidate(&block.stmts[candidate_index]) else {
            continue;
        };
        if last_def_indices[temp.index()] != Some(candidate_index) {
            // 候选拒绝[SemanticBarrier:Lifetime]：同一 canonical temp 的较早定义不是 loop-head reaching def；删除它并替换 sink 会切到旧 value epoch。
            continue;
        }
        let site = inline_site_in_stmt(&rewritten_sink, temp);
        let dependencies_are_stable = materialization_run_preserves_value_reads(
            block,
            candidate_index + 1..run_end,
            value,
            proof.facts,
        );
        if proof.safety.is_repeatable_in_single_value_context(value)
            && proof
                .safety
                .is_effect_invariant_in_single_value_context(value)
            && dependencies_are_stable
        {
            // 候选拒绝[SemanticBarrier:Lifetime]：额外 use、capture 或 self-rebind 仍要求 producer 存在。
            // 候选拒绝[PolicyBoundary]：DebugScope 标注的 temp 保留独立源码 binding 身份。
            if total_use_count(temp, live_use_counts) != 1
                || !materialization_run_candidate_is_safe(
                    temp,
                    value,
                    candidate_index,
                    proof.scratch,
                    proof.facts,
                    proof.captured_slots_before_stmt,
                )
                || site != Some(InlineSite::LoopHead)
            {
                continue;
            }
            replace_temp_in_stmt(&mut rewritten_sink, temp, value);
            assert!(
                inline_site_in_stmt(&rewritten_sink, temp).is_none(),
                "validated numeric-for literal alias must consume its only loop-head use"
            );
            removed_stmts[candidate_index] = true;
            remove_live_use(live_use_counts, temp);
            changed = true;
            continue;
        }
        if expr_observes_eval_order(value) {
            // 候选拒绝[SemanticBarrier:EvalOrder]：lookup/call/元方法运算移入 numeric-for
            // header 会跨过其它状态准备求值，改变 lookup/call/metamethod 的先后（regress_144）。
            continue;
        }
        // 候选拒绝[SemanticBarrier:Lifetime]：额外 use、capture 或 self-rebind 仍要求 producer 存在。
        // 候选拒绝[PolicyBoundary]：DebugScope 标注的 temp 保留独立源码 binding 身份。
        if site != Some(InlineSite::LoopHead) {
            continue;
        }
        let Some(plan) = numeric_for_binding_header_alias_plan(
            block,
            run_start..run_end,
            candidate_index,
            live_use_counts,
            &proof,
        ) else {
            continue;
        };
        replace_temp_in_stmt(&mut rewritten_sink, temp, &plan.replacement);
        assert!(
            inline_site_in_stmt(&rewritten_sink, temp).is_none(),
            "validated numeric-for binding alias must consume its only loop-head use"
        );
        for (chain_index, chain_temp) in plan.chain {
            assert!(
                !removed_stmts[chain_index],
                "numeric-for binding alias chains must be disjoint"
            );
            removed_stmts[chain_index] = true;
            remove_live_use(live_use_counts, chain_temp);
        }
        changed = true;
    }
    if changed {
        block.stmts[run_end] = rewritten_sink;
    }
    changed
}

fn materialization_run_preserves_value_reads(
    block: &HirBlock,
    later_run: std::ops::Range<usize>,
    value: &HirExpr,
    facts: &ProtoPromotionFacts,
) -> bool {
    let read_homes = direct_binding_read_homes_in_expr(value, facts);
    if read_homes.is_empty() {
        return true;
    }
    block.stmts[later_run].iter().all(|stmt| {
        let (target, _) = inline_candidate(stmt)
            .expect("numeric-for materialization run must contain only scalar temp definitions");
        if expr_touches_temp(value, target) {
            return false;
        }
        let target_write_homes = complete_materialization_write_homes(target, facts);
        if !target_write_homes.is_disjoint(&read_homes) {
            // 候选拒绝[SemanticBarrier:ValueFlow]：后续 run target 覆盖 expression source home 时，
            // producer 保存的是旧快照，移入 loop header 会改读新 epoch。
            return false;
        }
        true
    })
}

struct NumericForBindingHeaderAliasPlan {
    replacement: HirExpr,
    chain: Vec<(usize, TempId)>,
}

struct NumericForHeaderProof<'a> {
    scratch: &'a TempUseScratch,
    facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
    reference_captured: &'a ReferenceCapturedBindings,
    captured_slots_before_stmt: &'a CapturedSlotSnapshots,
    reference_captured_home_slots: &'a BTreeSet<HomeSlotKey>,
}

fn complete_reference_captured_home_slots(
    captured: &ReferenceCapturedBindings,
    facts: &ProtoPromotionFacts,
) -> BTreeSet<HomeSlotKey> {
    let mut homes = BTreeSet::new();
    for param in &captured.params {
        homes.extend(facts.complete_param_home_slots(*param));
    }
    for local in &captured.locals {
        homes.extend(facts.complete_local_home_slots(*local));
    }
    for temp in &captured.temps {
        homes.extend(facts.complete_temp_home_slots(*temp));
    }
    homes
}

fn complete_materialization_write_homes(
    temp: TempId,
    facts: &ProtoPromotionFacts,
) -> BTreeSet<HomeSlotKey> {
    let mut homes = facts.complete_temp_home_slots(temp);
    if homes.is_empty() {
        return homes;
    }
    homes.extend(facts.complete_immediate_move_write_homes(temp));
    homes
}

fn numeric_for_binding_header_alias_plan(
    block: &HirBlock,
    run: std::ops::Range<usize>,
    sink_temp_index: usize,
    live_use_counts: &[usize],
    proof: &NumericForHeaderProof<'_>,
) -> Option<NumericForBindingHeaderAliasPlan> {
    let (sink_temp, _) = inline_candidate(&block.stmts[sink_temp_index])?;
    let sink_captured_slots = proof
        .captured_slots_before_stmt
        .get(run.end)
        .expect("capture snapshots must cover the numeric-for sink");
    let mut chain = Vec::new();
    let mut current_index = sink_temp_index;
    let (replacement, source_homes, source_temp, source_requires_event_free_gap, source_index) = loop {
        let (temp, value) = inline_candidate(&block.stmts[current_index])?;
        if total_use_count(temp, live_use_counts) != 1 || expr_touches_temp(value, temp) {
            // 候选拒绝[SemanticBarrier:Lifetime]：链节点有额外 use 或自写时，删除整条快照链会丢失仍可观察的值或状态更新。
            return None;
        }
        if proof.scratch.has_debug_local_hint(temp) {
            // 候选拒绝[PolicyBoundary]：DebugScope 标注的 temp 保留独立源码 binding 身份。
            return None;
        }
        let chain_write_homes = complete_materialization_write_homes(temp, proof.facts);
        if !chain_write_homes.is_disjoint(sink_captured_slots) {
            // 候选拒绝[SemanticBarrier:Capture]：chain primary/hidden-MOVE 写入了 sink 前已捕获的 home；删除 producer 会让 closure 继续观察旧 cell 值。
            return None;
        }
        if !chain_write_homes.is_empty()
            && !chain_write_homes.is_disjoint(proof.reference_captured_home_slots)
        {
            // 候选拒绝[SemanticBarrier:Capture]：删除写入 captured home 的 chain producer
            // 会让现有或随后创建的 closure 观察此前 cell value（regress_310）。
            return None;
        }
        chain.push((current_index, temp));
        match value {
            HirExpr::ParamRef(param) => {
                let homes = proof.facts.complete_param_home_slots(*param);
                break (value.clone(), homes, None, false, current_index);
            }
            HirExpr::LocalRef(local) => {
                let homes = proof.facts.complete_local_home_slots(*local);
                break (value.clone(), homes, None, false, current_index);
            }
            HirExpr::TempRef(source) => {
                if let Some(source_index) = (run.start..current_index).rfind(|index| {
                    inline_candidate(&block.stmts[*index])
                        .is_some_and(|(candidate, _)| candidate == *source)
                }) {
                    current_index = source_index;
                } else {
                    let homes = proof.facts.complete_temp_home_slots(*source);
                    break (value.clone(), homes, Some(*source), false, current_index);
                }
            }
            HirExpr::UpvalueRef(_) => {
                // Upvalue 没有当前 proto 的 physical home；只要跨越区间无 lookup/call/元方法事件，
                // 读取位置从 producer 延到 header 不会获得外部改写机会。
                break (value.clone(), BTreeSet::new(), None, true, current_index);
            }
            _ => {
                // 候选拒绝[SemanticBarrier:EvalOrder]：lookup/call/元方法运算若作为 chain root，
                // 延到 numeric-for header 会跨过状态准备求值并改变事件顺序（regress_144）。
                return None;
            }
        }
    };

    let source_is_reference_captured = if source_homes.is_empty() {
        false
    } else {
        !source_homes.is_disjoint(proof.reference_captured_home_slots)
    };

    let chain_indices = chain
        .iter()
        .map(|(index, _)| *index)
        .collect::<BTreeSet<_>>();
    for stmt_index in (source_index + 1)..run.end {
        if chain_indices.contains(&stmt_index) {
            continue;
        }
        let (target, value) = inline_candidate(&block.stmts[stmt_index])
            .expect("numeric-for materialization run must contain only scalar temp definitions");
        if source_temp == Some(target) {
            // 候选拒绝[SemanticBarrier:ValueFlow]：链外状态准备按同一 HIR identity
            // 重写 source 时，原 producer 保留旧快照，延后读取会切到新 value epoch。
            return None;
        }
        let target_write_homes = complete_materialization_write_homes(target, proof.facts);
        if !target_write_homes.is_disjoint(&source_homes) {
            // 候选拒绝[SemanticBarrier:ValueFlow]：链外状态准备写覆盖 source possible-home 时，
            // 原 temp 冻结旧值；延后读取会切到新 epoch。
            return None;
        }
        if (source_is_reference_captured || source_requires_event_free_gap)
            && expr_observes_eval_order(value)
        {
            // 候选拒绝[SemanticBarrier:ValueFlow]：区间 call/lookup/元方法可经引用 closure
            // 改写 captured source（或 upvalue）；延后读取会破坏定义点快照（regress_145）。
            return None;
        }
    }

    if (source_is_reference_captured || source_requires_event_free_gap)
        && !temp_precedes_observable_eval_in_stmt(
            &block.stmts[run.end],
            sink_temp,
            true,
            proof.reference_captured,
        )
    {
        // 候选拒绝[SemanticBarrier:ValueFlow]：numeric-for 的 start/limit/step 或其表达式
        // 前缀若先执行 call/lookup/元方法，可在 replacement 读取前改写 captured source/upvalue；
        // 原 producer 已冻结旧值，延后到 header 会切到新 epoch（regress_145）。
        return None;
    }

    Some(NumericForBindingHeaderAliasPlan { replacement, chain })
}

struct OpenReturnFixedAliasProof<'a> {
    scratch: &'a TempUseScratch,
    facts: &'a ProtoPromotionFacts,
    captured_slots_before_stmt: &'a CapturedSlotSnapshots,
    reference_captured_home_slots: &'a BTreeSet<HomeSlotKey>,
}

fn inline_open_return_fixed_alias_run(
    block: &mut HirBlock,
    run: std::ops::Range<usize>,
    live_use_counts: &mut [usize],
    proof: OpenReturnFixedAliasProof<'_>,
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

    let captured_slots = proof
        .captured_slots_before_stmt
        .get(run_end)
        .expect("capture snapshots must cover the planned open-return sink");
    let mut target_temps = BTreeSet::new();
    let mut source_temps = BTreeSet::new();
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
            || proof.scratch.has_debug_local_hint(target)
        {
            // 候选拒绝[SemanticBarrier:Lifetime]：fixed prefix 非对应唯一 target use 时，删除 alias 会改变其它消费者所见值。
            // 候选拒绝[PolicyBoundary]：DebugScope 标注的 alias 保留独立源码 binding 身份。
            return false;
        }
        let target_homes = proof.facts.complete_temp_home_slots(target);
        let source_homes = proof.facts.complete_temp_home_slots(*source);
        let touches_captured_home = target_homes
            .iter()
            .chain(&source_homes)
            .any(|home| captured_slots.contains(home));
        if touches_captured_home {
            // 候选拒绝[SemanticBarrier:Capture]：source/target 的任一可能 home 已捕获，
            // 当前 HIR 事务不能证明移动读取安全；这不是“任何后续源码改写都非法”的
            // 绝对结论，因此不能把本次证明不足升级成跨层 Preserve。
            return false;
        }
        if !target_temps.insert(target) || !target_slots.is_disjoint(&target_homes) {
            // 候选拒绝[SemanticBarrier:Capture]：多个 target 可能共享 HIR/物理槽时，
            // 移动读取会改变 closure/slot 生命周期。per-definition certificate 尚未覆盖
            // 此关系，本阶段不把它错误聚合成整个 TempId 的 retention。
            return false;
        }
        source_temps.insert(*source);
        target_slots.extend(target_homes);
        source_slots.extend(source_homes);
    }
    if !(target_slots.is_empty() && source_slots.is_empty())
        && (!target_slots.is_disjoint(proof.reference_captured_home_slots)
            || !source_slots.is_disjoint(proof.reference_captured_home_slots))
    {
        // 候选拒绝[SemanticBarrier:Capture]：删除 captured target 写或把 captured source
        // 读取延到 open tail setup 之后超出当前 HIR 证明；AST 仍可针对 Lua 源码的
        // left-to-right return 求值规则证明另一种合法改写，所以这里只拒绝本事务。
        return false;
    }
    if !target_temps.is_disjoint(&source_temps) || !target_slots.is_disjoint(&source_slots) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：source/target 同槽会让 fixed return 读到 tail setup 后的新值；见 regress_310。
        return false;
    }

    for stmt in &block.stmts[(run_start + alias_count)..run_end] {
        let Some((target, _)) = inline_candidate(stmt) else {
            return false;
        };
        if target_temps.contains(&target) || source_temps.contains(&target) {
            // 候选拒绝[SemanticBarrier:EvalOrder]：tail setup 直接重写 fixed alias 的 source/target
            // HIR binding 时，延后读取会切到 setup 后的新值。
            return false;
        }
        let protected_slots_are_empty = target_slots.is_empty() && source_slots.is_empty();
        let possible_homes = proof.facts.complete_temp_home_slots(target);
        if !protected_slots_are_empty
            && (!possible_homes.is_disjoint(&target_slots)
                || !possible_homes.is_disjoint(&source_slots))
        {
            // 候选拒绝[SemanticBarrier:EvalOrder]：tail setup 覆盖 fixed alias 槽时，内联会把读取延后到覆盖之后。
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
    // 候选拒绝[PolicyBoundary]：DebugScope 标注的 temp 保留独立源码 binding 身份。
    !scratch.has_debug_local_hint(temp)
        // 候选拒绝[SemanticBarrier:Capture]：引用捕获该 home 的 closure 必须观察 producer 写入后的值；见 regress_310。
        && !temp_rebinds_captured_slot(
            temp,
            facts,
            captured_slots_before_stmt
                .get(stmt_index)
                .expect("captured slot scan should cover every statement"),
        )
        // 候选拒绝[SemanticBarrier:Lifetime]：`t=t+1; sink(t)` 的 producer 是状态更新而非 forwarding temp；见 regress_263#2。
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
            let policy = RepeatInlinePolicy {
                readability,
                safety: workspace.roots.safety,
            };
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
                reference_captured,
                policy,
                facts,
                inherited_captured_slots,
            );
            changed |= inline_repeat_tail_temp(
                repeat_stmt,
                &mut workspace.uses,
                live_use_counts,
                reference_captured,
                policy,
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
        | HirStmt::GlobalDecl(_)
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

#[derive(Clone, Copy)]
struct RepeatInlinePolicy {
    readability: ReadabilityOptions,
    safety: HirExprSafety,
}

fn inline_repeat_head_scalar_temp(
    repeat_stmt: &mut crate::hir::common::HirRepeat,
    scratch: &mut TempUseScratch,
    live_use_counts: &mut [usize],
    reference_captured: &ReferenceCapturedBindings,
    policy: RepeatInlinePolicy,
    facts: &ProtoPromotionFacts,
    inherited_captured_slots: &BTreeSet<HomeSlotKey>,
) -> bool {
    let Some((temp, _)) = repeat_stmt.body.stmts.first().and_then(inline_candidate) else {
        return false;
    };
    // 这里的 producer 已由 structure fact 证明是 continue 重定位出的 latch prefix；
    // 删除它会把 RHS 从每轮 body 前移动到 body 后的 until 求值点。
    if !facts.is_repeat_condition_prefix_temp(temp) {
        // 普通 body 首句不形成 repeat-prefix 候选；只有 structure 已标注的 before-body
        // condition prefix 才属于本事务。
        return false;
    }
    inline_repeat_head_scalar_temp_with_proven_prefix(
        repeat_stmt,
        scratch,
        live_use_counts,
        reference_captured,
        policy,
        facts,
        inherited_captured_slots,
    )
}

fn inline_repeat_head_scalar_temp_with_proven_prefix(
    repeat_stmt: &mut crate::hir::common::HirRepeat,
    scratch: &mut TempUseScratch,
    live_use_counts: &mut [usize],
    reference_captured: &ReferenceCapturedBindings,
    policy: RepeatInlinePolicy,
    facts: &ProtoPromotionFacts,
    inherited_captured_slots: &BTreeSet<HomeSlotKey>,
) -> bool {
    let Some((temp, value)) = repeat_stmt.body.stmts.first().and_then(inline_candidate) else {
        return false;
    };
    // 候选拒绝[PolicyBoundary]：DebugScope 标注的 temp 保留独立源码 binding 身份。
    // 候选拒绝[SemanticBarrier:Lifetime]：非唯一 condition use 仍需要原 temp。
    if scratch.has_debug_local_hint(temp)
        || total_use_count(temp, live_use_counts) != 1
        || collect_expr_temp_uses_summary(&repeat_stmt.cond, scratch).count(temp) != 1
    {
        return false;
    }
    let Some(site) = inline_site_in_repeat_condition(&repeat_stmt.cond, temp) else {
        // 候选拒绝[SemanticBarrier:Capture]：唯一 use 位于 closure capture 时，内联会把定义点快照
        // 改成 closure 的按引用 cell/value capture。
        return false;
    };
    if !site.allows(value, policy.readability, policy.safety) {
        // 候选拒绝[PolicyBoundary]：repeat condition 服从控制头复杂度展示阈值。
        return false;
    }

    let mut captured_slots = inherited_captured_slots.clone();
    for stmt in &repeat_stmt.body.stmts[1..] {
        if collect_stmt_temp_uses(stmt, scratch).count(temp) != 0
            || stmt_writes_temp(stmt, temp)
            || stmt_contains_nested_nonlocal_control(stmt)
        {
            // 候选拒绝[SemanticBarrier:ControlFlow]：中间 use/write 或 break/return/goto 会让 producer 与 condition 不再位于每轮同一路径；见 regress_263#2。
            return false;
        }
        facts.collect_captured_home_slots_in_stmt(stmt, &mut captured_slots);
    }
    if temp_rebinds_captured_slot(temp, facts, &captured_slots) {
        // 候选拒绝[SemanticBarrier:Capture]：closure 已引用捕获该 home，删除首句写入会让其观察上一轮值。
        return false;
    }
    if !repeat_head_dependencies_are_stable(
        value,
        temp,
        &repeat_stmt.body.stmts[1..],
        &repeat_stmt.cond,
        &RepeatHeadDependencyProof {
            reference_captured,
            safety: policy.safety,
            facts,
            captured_slots: &captured_slots,
        },
    ) {
        return false;
    }

    let value = value.clone();
    assert_eq!(
        rewrite::replace_temp_in_expr(&mut repeat_stmt.cond, temp, &value),
        1,
        "validated repeat-head candidate must have exactly one rewrite site"
    );
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

struct RepeatHeadDependencyProof<'a> {
    reference_captured: &'a ReferenceCapturedBindings,
    safety: HirExprSafety,
    facts: &'a ProtoPromotionFacts,
    captured_slots: &'a BTreeSet<HomeSlotKey>,
}

fn repeat_head_dependencies_are_stable(
    value: &HirExpr,
    temp: TempId,
    body_suffix: &[HirStmt],
    condition: &HirExpr,
    proof: &RepeatHeadDependencyProof<'_>,
) -> bool {
    if !is_repeat_header_rootless_scalar(value) {
        if !proof.safety.is_repeatable_in_single_value_context(value) {
            if expr_observes_eval_order(value) {
                // 候选拒绝[SemanticBarrier:EvalOrder]：call/lookup/元方法运算原本在 body 前求值；
                // 移进 until 会把调用、__index 或元方法延到整个 body 之后。
            } else {
                // 候选拒绝[SemanticBarrier:ValueFlow]：不能证明可重复求值的动态值仍需 producer 快照。
            }
            return false;
        }

        let read_homes = direct_binding_read_homes_in_expr(value, proof.facts);
        let read_identities = direct_binding_identities_in_expr(value);
        let body_writes = direct_binding_writes_in_stmts(body_suffix, proof.facts);
        if read_identities.overlaps(&body_writes.identities)
            || !read_homes.is_disjoint(&body_writes.homes)
        {
            // 候选拒绝[SemanticBarrier:ValueFlow]：body 重写 source identity 或任一 possible-home 时，
            // body 前 producer 保存旧 epoch；移进 until 会读取 body 后的新 epoch。
            return false;
        }
        if body_writes
            .close_from_regs
            .iter()
            .any(|from| read_homes.iter().any(|home| home.slot() >= *from))
        {
            // 候选拒绝[SemanticBarrier:Lifetime]：body Close 若结束 source home，producer 是
            // cleanup 前的快照/root；移到 until 会在生命周期结束后读取。
            return false;
        }

        let crosses_observable_eval = stmts_observe_eval_order(body_suffix, proof.safety)
            || !temp_precedes_observable_eval_in_expr(
                condition,
                temp,
                true,
                proof.reference_captured,
            );
        if crosses_observable_eval {
            let source_is_identity_captured = read_identities
                .overlaps_reference_captured(proof.reference_captured)
                || !read_identities.upvalues.is_empty();
            let source_is_home_captured = if read_homes.is_empty() {
                false
            } else {
                let reference_captured_homes =
                    complete_reference_captured_home_slots(proof.reference_captured, proof.facts);
                !read_homes.is_disjoint(&reference_captured_homes)
            };
            if source_is_identity_captured || source_is_home_captured {
                // 候选拒绝[SemanticBarrier:ValueFlow]：body 或 until 前缀的 call/lookup/元方法
                // 可在延后读取前改写 captured identity/home；producer 冻结的旧值会丢失。
                return false;
            }
        }
    }

    let target_write_homes = complete_materialization_write_homes(temp, proof.facts);
    if proof.reference_captured.temps.contains(&temp)
        || !target_write_homes.is_disjoint(proof.captured_slots)
    {
        // 候选拒绝[SemanticBarrier:Capture]：删除写入 captured temp identity/home 的 prefix
        // producer 会让 closure 观察上一轮 cell value。
        return false;
    }
    if !target_write_homes.is_empty() {
        let reference_captured_homes =
            complete_reference_captured_home_slots(proof.reference_captured, proof.facts);
        if !target_write_homes.is_disjoint(&reference_captured_homes) {
            // 候选拒绝[SemanticBarrier:Capture]：prefix target 的 primary/hidden write 命中
            // captured home 时，删除 producer 会改变 closure 观察值。
            return false;
        }
    }
    true
}

#[derive(Default)]
struct DirectBindingIdentities {
    params: BTreeSet<crate::hir::common::ParamId>,
    locals: BTreeSet<crate::hir::common::LocalId>,
    temps: BTreeSet<TempId>,
    upvalues: BTreeSet<crate::hir::common::UpvalueId>,
}

impl DirectBindingIdentities {
    fn overlaps(&self, other: &Self) -> bool {
        !self.params.is_disjoint(&other.params)
            || !self.locals.is_disjoint(&other.locals)
            || !self.temps.is_disjoint(&other.temps)
            || !self.upvalues.is_disjoint(&other.upvalues)
    }

    fn overlaps_reference_captured(&self, captured: &ReferenceCapturedBindings) -> bool {
        !self.params.is_disjoint(&captured.params)
            || !self.locals.is_disjoint(&captured.locals)
            || !self.temps.is_disjoint(&captured.temps)
    }
}

fn direct_binding_identities_in_expr(expr: &HirExpr) -> DirectBindingIdentities {
    let mut collector = DirectBindingIdentityCollector::default();
    visit_expr(expr, &mut collector);
    collector.identities
}

#[derive(Default)]
struct DirectBindingIdentityCollector {
    identities: DirectBindingIdentities,
}

impl HirVisitor for DirectBindingIdentityCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::ParamRef(param) => {
                self.identities.params.insert(*param);
            }
            HirExpr::LocalRef(local) => {
                self.identities.locals.insert(*local);
            }
            HirExpr::TempRef(temp) => {
                self.identities.temps.insert(*temp);
            }
            HirExpr::UpvalueRef(upvalue) => {
                self.identities.upvalues.insert(*upvalue);
            }
            _ => {}
        }
    }
}

struct DirectBindingWriteSummary {
    identities: DirectBindingIdentities,
    homes: BTreeSet<HomeSlotKey>,
    close_from_regs: BTreeSet<usize>,
}

fn direct_binding_writes_in_stmts(
    stmts: &[HirStmt],
    facts: &ProtoPromotionFacts,
) -> DirectBindingWriteSummary {
    let mut collector = DirectBindingWriteCollector {
        facts,
        identities: DirectBindingIdentities::default(),
        homes: BTreeSet::new(),
        close_from_regs: BTreeSet::new(),
    };
    visit_stmts(stmts, &mut collector);
    DirectBindingWriteSummary {
        identities: collector.identities,
        homes: collector.homes,
        close_from_regs: collector.close_from_regs,
    }
}

struct DirectBindingWriteCollector<'a> {
    facts: &'a ProtoPromotionFacts,
    identities: DirectBindingIdentities,
    homes: BTreeSet<HomeSlotKey>,
    close_from_regs: BTreeSet<usize>,
}

impl DirectBindingWriteCollector<'_> {
    fn note_homes(&mut self, homes: BTreeSet<HomeSlotKey>) {
        self.homes.extend(homes);
    }
}

impl HirVisitor for DirectBindingWriteCollector<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl(decl) => {
                for local in &decl.bindings {
                    self.identities.locals.insert(*local);
                    self.note_homes(self.facts.complete_local_home_slots(*local));
                }
            }
            HirStmt::NumericFor(for_stmt) => {
                self.identities.locals.insert(for_stmt.binding);
                self.note_homes(self.facts.complete_local_home_slots(for_stmt.binding));
            }
            HirStmt::GenericFor(for_stmt) => {
                for local in &for_stmt.bindings {
                    self.identities.locals.insert(*local);
                    self.note_homes(self.facts.complete_local_home_slots(*local));
                }
            }
            HirStmt::Close(close) => {
                self.close_from_regs.insert(close.from_reg);
            }
            _ => {}
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        match lvalue {
            HirLValue::Param(param) => {
                self.identities.params.insert(*param);
                self.note_homes(self.facts.complete_param_home_slots(*param));
            }
            HirLValue::Local(local) => {
                self.identities.locals.insert(*local);
                self.note_homes(self.facts.complete_local_home_slots(*local));
            }
            HirLValue::Temp(temp) => {
                self.identities.temps.insert(*temp);
                self.homes
                    .extend(complete_materialization_write_homes(*temp, self.facts));
            }
            HirLValue::Upvalue(upvalue) => {
                self.identities.upvalues.insert(*upvalue);
            }
            HirLValue::Global(_) | HirLValue::TableAccess(_) => {}
        }
    }
}

fn stmts_observe_eval_order(stmts: &[HirStmt], safety: HirExprSafety) -> bool {
    struct ObservableEvalCollector {
        found: bool,
        safety: HirExprSafety,
    }

    impl HirVisitor for ObservableEvalCollector {
        fn visit_stmt(&mut self, stmt: &HirStmt) {
            self.found |= matches!(
                stmt,
                HirStmt::GlobalDecl(_)
                    | HirStmt::TableSetList(_)
                    | HirStmt::Close(_)
                    | HirStmt::ErrNil(_)
            );
        }

        fn visit_expr(&mut self, expr: &HirExpr) {
            self.found |= !self.safety.is_discard_safe_without_residual(expr);
        }

        fn visit_lvalue(&mut self, lvalue: &HirLValue) {
            self.found |= matches!(lvalue, HirLValue::Global(_) | HirLValue::TableAccess(_));
        }

        fn visit_call(&mut self, _call: &HirCallExpr) {
            self.found = true;
        }
    }

    let mut collector = ObservableEvalCollector {
        found: false,
        safety,
    };
    visit_stmts(stmts, &mut collector);
    collector.found
}

fn inline_repeat_tail_temp(
    repeat_stmt: &mut crate::hir::common::HirRepeat,
    scratch: &mut TempUseScratch,
    live_use_counts: &mut [usize],
    reference_captured: &ReferenceCapturedBindings,
    policy: RepeatInlinePolicy,
    facts: &ProtoPromotionFacts,
    inherited_captured_slots: &BTreeSet<HomeSlotKey>,
) -> bool {
    let Some(tail_index) = repeat_stmt.body.stmts.len().checked_sub(1) else {
        return false;
    };
    let Some((temp, value)) = inline_candidate(&repeat_stmt.body.stmts[tail_index]) else {
        return false;
    };
    // 候选拒绝[PolicyBoundary]：DebugScope 标注的 temp 保留独立源码 binding 身份。
    // 候选拒绝[SemanticBarrier:Lifetime]：self-reference 或额外 use 需要保留状态写入/temp 值。
    if scratch.has_debug_local_hint(temp)
        || expr_touches_temp(value, temp)
        || total_use_count(temp, live_use_counts) != 1
        || collect_expr_temp_uses_summary(&repeat_stmt.cond, scratch).count(temp) != 1
    {
        return false;
    }
    let Some(site) = inline_site_in_repeat_condition(&repeat_stmt.cond, temp) else {
        // 候选拒绝[SemanticBarrier:Capture]：唯一 use 位于 closure capture 时，内联会把定义点快照
        // 改成 closure 的按引用 cell/value capture。
        return false;
    };
    if !site.allows(value, policy.readability, policy.safety)
        || expr_requires_ordered_snapshot(value)
            && !temp_precedes_observable_eval_in_expr(
                &repeat_stmt.cond,
                temp,
                expr_observes_eval_order(value),
                reference_captured,
            )
    {
        // 候选拒绝[PolicyBoundary]：repeat condition 服从控制头复杂度展示阈值。
        // 候选拒绝[SemanticBarrier:EvalOrder]：condition 中 temp 前的 observable eval 会在内联后先于 producer value 执行。
        return false;
    }

    let mut captured_slots = inherited_captured_slots.clone();
    for stmt in &repeat_stmt.body.stmts[..tail_index] {
        if collect_stmt_temp_uses(stmt, scratch).count(temp) != 0
            || stmt_writes_temp(stmt, temp)
            || stmt_contains_nested_nonlocal_control(stmt)
        {
            // 候选拒绝[SemanticBarrier:ControlFlow]：中间 use/write 或非局部控制转移破坏同轮路径证明；见 regress_263#2。
            return false;
        }
        facts.collect_captured_home_slots_in_stmt(stmt, &mut captured_slots);
    }
    if temp_rebinds_captured_slot(temp, facts, &captured_slots) {
        // 候选拒绝[SemanticBarrier:Capture]：closure 引用捕获该 home 时，删除尾写会改变闭包观察值。
        return false;
    }

    let value = value.clone();
    assert_eq!(
        rewrite::replace_temp_in_expr(&mut repeat_stmt.cond, temp, &value),
        1,
        "validated repeat-tail candidate must have exactly one rewrite site"
    );
    repeat_stmt.body.stmts.pop();
    remove_live_use(live_use_counts, temp);
    true
}

fn temp_rebinds_captured_slot(
    temp: TempId,
    facts: &ProtoPromotionFacts,
    captured_slots: &BTreeSet<HomeSlotKey>,
) -> bool {
    !facts
        .complete_temp_home_slots(temp)
        .is_disjoint(captured_slots)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{
        HirAssign, HirBinaryExpr, HirBinaryOpKind, HirCapture, HirCaptureMode, HirClosureExpr,
        HirGlobalDecl, HirGlobalRef, HirIf, HirLogicalExpr, HirPackTail, HirReturn, HirTableAccess,
        HirValuePack, LocalId,
    };
    use crate::parser::{ProtoLineRange, ProtoSignature};

    fn empty_proto(body: HirBlock, temps: Vec<TempId>) -> HirProto {
        let temp_count = temps.len();
        HirProto {
            id: crate::hir::common::HirProtoRef(0),
            source: None,
            line_range: ProtoLineRange {
                defined_start: 0,
                defined_end: 0,
            },
            signature: ProtoSignature {
                num_params: 0,
                is_vararg: false,
                has_vararg_param_reg: false,
                named_vararg_table: false,
                legacy_arg_slot: false,
            },
            params: Vec::new(),
            param_debug_hints: Vec::new(),
            locals: Vec::new(),
            vararg_param_local: None,
            local_debug_hints: Vec::new(),
            local_debug_scopes: Vec::new(),
            debug_scopes: Vec::new(),
            physical_root_temps: BTreeSet::new(),
            physical_root_locals: BTreeSet::new(),
            inline_dispositions: Default::default(),
            upvalues: Vec::new(),
            environment_upvalues: BTreeSet::new(),
            mutable_upvalues: BTreeSet::new(),
            upvalue_debug_hints: Vec::new(),
            temps,
            temp_debug_locals: vec![None; temp_count],
            temp_debug_scopes: vec![None; temp_count],
            exit_requirements: Vec::new(),
            body,
            children: Vec::new(),
            failure: None,
            detached_children: Vec::new(),
        }
    }

    fn terminal_nil_pack_block() -> HirBlock {
        HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0)), HirLValue::Temp(TempId(1))],
                    values: HirValuePack::fixed(vec![HirExpr::Nil, HirExpr::Nil]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: HirValuePack::fixed(vec![
                        HirExpr::TempRef(TempId(0)),
                        HirExpr::TempRef(TempId(1)),
                    ]),
                })),
            ],
        }
    }

    fn root_open_nil_pack_block() -> HirBlock {
        let mut block = terminal_nil_pack_block();
        let HirStmt::Return(ret) = &mut block.stmts[1] else {
            unreachable!("terminal nil-pack fixture must end in return")
        };
        ret.values.tail = Some(HirPackTail::open(HirExpr::Call(Box::new(HirCallExpr {
            argument_roots: Vec::new(),
            callee: HirExpr::GlobalRef(HirGlobalRef { key: "tail".into() }),
            args: HirValuePack::default(),
            method: false,
            fastcall: None,
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
        }))));
        block
    }

    fn open_return_alias_block(setup_target: TempId) -> HirBlock {
        let alias = |target, source| {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(target)],
                values: HirValuePack::fixed(vec![HirExpr::TempRef(source)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };
        HirBlock {
            stmts: vec![
                alias(TempId(0), TempId(2)),
                alias(TempId(1), TempId(3)),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(setup_target)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: HirValuePack::expanding(
                        vec![HirExpr::TempRef(TempId(0)), HirExpr::TempRef(TempId(1))],
                        HirPackTail::open(HirExpr::Call(Box::new(HirCallExpr {
                            argument_roots: Vec::new(),
                            callee: HirExpr::GlobalRef(HirGlobalRef { key: "tail".into() }),
                            args: HirValuePack::default(),
                            method: false,
                            fastcall: None,
                            method_key: None,
                            callee_root_handoff: None,
                            method_rewrite_transaction: None,
                        }))),
                    ),
                })),
            ],
        }
    }

    fn empty_capture_snapshots(stmt_count: usize) -> CapturedSlotSnapshots {
        let empty = BTreeSet::new();
        let mut snapshots = CapturedSlotSnapshots::new(stmt_count, &empty);
        for _ in 0..stmt_count {
            snapshots.push(&empty);
        }
        snapshots
    }

    fn call_stmt(name: &str) -> HirStmt {
        HirStmt::CallStmt(Box::new(crate::hir::common::HirCallStmt {
            call: HirCallExpr {
                argument_roots: Vec::new(),
                callee: HirExpr::GlobalRef(HirGlobalRef { key: name.into() }),
                args: HirValuePack::default(),
                method: false,
                fastcall: None,
                method_key: None,
                callee_root_handoff: None,
                method_rewrite_transaction: None,
            },
        }))
    }

    fn scalar_temp_assign(target: TempId, value: HirExpr) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(target)],
            values: HirValuePack::fixed(vec![value]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }))
    }

    fn table_access(base: HirExpr, key: &str) -> HirExpr {
        HirExpr::TableAccess(Box::new(HirTableAccess {
            base,
            key: HirExpr::String(key.into()),
            method_setup_protocol: None,
        }))
    }

    fn normal_call(callee: HirExpr, args: Vec<HirExpr>) -> HirExpr {
        HirExpr::Call(Box::new(HirCallExpr {
            argument_roots: Vec::new(),
            callee,
            args: HirValuePack::fixed(args),
            method: false,
            fastcall: None,
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
        }))
    }

    fn eager_condition_materialization_block() -> HirBlock {
        let root = TempId(0);
        let native = TempId(1);
        let callee = TempId(2);
        let argument = TempId(3);
        HirBlock {
            stmts: vec![
                scalar_temp_assign(root, HirExpr::GlobalRef(HirGlobalRef { key: "_G".into() })),
                scalar_temp_assign(native, table_access(HirExpr::TempRef(root), "native")),
                scalar_temp_assign(
                    callee,
                    table_access(HirExpr::TempRef(native), "checkIfDatePassed"),
                ),
                scalar_temp_assign(
                    argument,
                    table_access(
                        HirExpr::GlobalRef(HirGlobalRef { key: "page".into() }),
                        "year",
                    ),
                ),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Eq,
                        lhs: normal_call(
                            HirExpr::TempRef(callee),
                            vec![HirExpr::TempRef(argument)],
                        ),
                        rhs: HirExpr::Integer(1),
                    })),
                    then_block: HirBlock::default(),
                    else_block: None,
                })),
            ],
        }
    }

    #[test]
    fn eager_condition_transaction_consumes_the_complete_lookup_call_run() {
        let mut block = eager_condition_materialization_block();
        let temps = (0..4).map(TempId).collect::<Vec<_>>();
        let proto = empty_proto(block.clone(), temps.clone());
        let mut scratch = TempUseScratch::new(&proto, temps.len());
        let mut facts = ProtoPromotionFacts::default();
        for temp in temps {
            facts.record_home_free_temp(temp);
        }
        let snapshots = empty_capture_snapshots(block.stmts.len());
        let mut live_use_counts = vec![1; 4];
        let mut order_sensitive_defs = OrderSensitiveDefWorkspace::new(4);
        order_sensitive_defs.rebuild(&block.stmts);
        let reference_captured = ReferenceCapturedBindings::default();
        let mut removed = vec![false; block.stmts.len()];

        assert!(inline_eager_condition_materialization_run(
            &mut block,
            0,
            4,
            &[false; 5],
            &mut EagerConditionMaterializationProof {
                scratch: &mut scratch,
                live_use_counts: &mut live_use_counts,
                facts: &facts,
                captured_slots_before_stmt: &snapshots,
                order_sensitive_defs: &order_sensitive_defs,
                reference_captured: &reference_captured,
                dialect: DecompileDialect::Lua54,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
            },
            &mut removed,
        ));
        assert_eq!(removed, vec![true, true, true, true, false]);
        assert_eq!(live_use_counts, vec![0; 4]);
        for temp in 0..4 {
            assert_eq!(
                collect_stmt_temp_uses(&block.stmts[4], &mut scratch).count(TempId(temp)),
                0
            );
        }
    }

    #[test]
    fn eager_condition_transaction_rejects_short_circuit_and_physical_roots() {
        let callee = TempId(0);
        let short_circuit = HirBlock {
            stmts: vec![
                scalar_temp_assign(
                    callee,
                    HirExpr::GlobalRef(HirGlobalRef {
                        key: "callee".into(),
                    }),
                ),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                        lhs: HirExpr::GlobalRef(HirGlobalRef { key: "gate".into() }),
                        rhs: normal_call(HirExpr::TempRef(callee), Vec::new()),
                    })),
                    then_block: HirBlock::default(),
                    else_block: None,
                })),
            ],
        };
        let proto = empty_proto(short_circuit.clone(), vec![callee]);
        let mut scratch = TempUseScratch::new(&proto, 1);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(callee);
        let snapshots = empty_capture_snapshots(2);
        let mut live_use_counts = vec![1];
        let mut order_sensitive_defs = OrderSensitiveDefWorkspace::new(1);
        order_sensitive_defs.rebuild(&short_circuit.stmts);
        let reference_captured = ReferenceCapturedBindings::default();
        let mut block = short_circuit.clone();
        let mut removed = vec![false; 2];

        assert!(!inline_eager_condition_materialization_run(
            &mut block,
            0,
            1,
            &[false; 2],
            &mut EagerConditionMaterializationProof {
                scratch: &mut scratch,
                live_use_counts: &mut live_use_counts,
                facts: &facts,
                captured_slots_before_stmt: &snapshots,
                order_sensitive_defs: &order_sensitive_defs,
                reference_captured: &reference_captured,
                dialect: DecompileDialect::Lua54,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
            },
            &mut removed,
        ));
        assert_eq!(block, short_circuit);

        let mut rooted = eager_condition_materialization_block();
        let rooted_proto = empty_proto(rooted.clone(), (0..4).map(TempId).collect());
        let mut rooted_scratch = TempUseScratch::new(&rooted_proto, 4);
        let mut rooted_facts = ProtoPromotionFacts::default();
        for temp in 0..4 {
            rooted_facts.record_home_free_temp(TempId(temp));
        }
        let rooted_snapshots = empty_capture_snapshots(rooted.stmts.len());
        let mut rooted_live_use_counts = vec![1; 4];
        let mut rooted_order_sensitive_defs = OrderSensitiveDefWorkspace::new(4);
        rooted_order_sensitive_defs.rebuild(&rooted.stmts);
        let original_rooted = rooted.clone();
        let mut rooted_removed = vec![false; rooted.stmts.len()];
        assert!(!inline_eager_condition_materialization_run(
            &mut rooted,
            0,
            4,
            &[false, true, false, false, false],
            &mut EagerConditionMaterializationProof {
                scratch: &mut rooted_scratch,
                live_use_counts: &mut rooted_live_use_counts,
                facts: &rooted_facts,
                captured_slots_before_stmt: &rooted_snapshots,
                order_sensitive_defs: &rooted_order_sensitive_defs,
                reference_captured: &reference_captured,
                dialect: DecompileDialect::Lua54,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
            },
            &mut rooted_removed,
        ));
        assert_eq!(rooted, original_rooted);

        let first = TempId(0);
        let later = TempId(1);
        let forward_dependency = HirBlock {
            stmts: vec![
                scalar_temp_assign(first, HirExpr::TempRef(later)),
                scalar_temp_assign(
                    later,
                    HirExpr::GlobalRef(HirGlobalRef {
                        key: "callee".into(),
                    }),
                ),
                HirStmt::If(Box::new(HirIf {
                    cond: normal_call(HirExpr::TempRef(first), Vec::new()),
                    then_block: HirBlock::default(),
                    else_block: None,
                })),
            ],
        };
        let forward_proto = empty_proto(forward_dependency.clone(), vec![first, later]);
        let mut forward_scratch = TempUseScratch::new(&forward_proto, 2);
        let mut forward_facts = ProtoPromotionFacts::default();
        forward_facts.record_home_free_temp(first);
        forward_facts.record_home_free_temp(later);
        let forward_snapshots = empty_capture_snapshots(forward_dependency.stmts.len());
        let mut forward_live_use_counts = vec![1; 2];
        let mut forward_order_sensitive_defs = OrderSensitiveDefWorkspace::new(2);
        forward_order_sensitive_defs.rebuild(&forward_dependency.stmts);
        let mut forward_block = forward_dependency.clone();
        let mut forward_removed = vec![false; forward_block.stmts.len()];
        assert!(!inline_eager_condition_materialization_run(
            &mut forward_block,
            0,
            2,
            &[false; 3],
            &mut EagerConditionMaterializationProof {
                scratch: &mut forward_scratch,
                live_use_counts: &mut forward_live_use_counts,
                facts: &forward_facts,
                captured_slots_before_stmt: &forward_snapshots,
                order_sensitive_defs: &forward_order_sensitive_defs,
                reference_captured: &reference_captured,
                dialect: DecompileDialect::Lua54,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
            },
            &mut forward_removed,
        ));
        assert_eq!(forward_block, forward_dependency);
        assert_eq!(forward_removed, vec![false; 3]);
        assert_eq!(forward_live_use_counts, vec![1; 2]);
    }

    fn prefixed_block_sink(temp: TempId, prefix: HirStmt) -> HirStmt {
        HirStmt::Block(Box::new(HirBlock {
            stmts: vec![
                prefix,
                HirStmt::Return(Box::new(HirReturn {
                    values: HirValuePack::fixed(vec![HirExpr::TempRef(temp)]),
                })),
            ],
        }))
    }

    #[test]
    fn later_block_site_accepts_gc_inert_physical_producers() {
        let target = TempId(0);
        let prefix_temp = TempId(1);
        let prefix = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(prefix_temp)],
            values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }));
        let producer = |value| {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(target)],
                values: HirValuePack::fixed(vec![value]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };

        let mut literal = empty_proto(
            HirBlock {
                stmts: vec![
                    producer(HirExpr::Integer(7)),
                    prefixed_block_sink(target, prefix.clone()),
                ],
            },
            vec![target, prefix_temp],
        );
        let mut literal_facts = ProtoPromotionFacts::default();
        literal_facts.record_temp_home_slot_for_test(target, HomeSlotKey::new(0, 0));
        assert!(inline_temps_in_proto_with_facts(
            &mut literal,
            ReadabilityOptions::default(),
            &literal_facts,
            DecompileDialect::Lua54,
            &[],
            RootAnalysisContext {
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                effects: &[]
            },
        ));
        assert!(matches!(
            literal.body.stmts.as_slice(),
            [HirStmt::Block(block)]
                if matches!(block.stmts.as_slice(),
                    [HirStmt::Assign(_), HirStmt::Return(ret)]
                        if ret.values.fixed == vec![HirExpr::Integer(7)])
        ));

        let string_value = HirExpr::String("stable".into());
        let mut string = empty_proto(
            HirBlock {
                stmts: vec![
                    producer(string_value.clone()),
                    prefixed_block_sink(
                        target,
                        HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Temp(prefix_temp)],
                            values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                            initializer_merge_transaction: None,
                            generic_for_initializer_producer: None,
                            method_rewrite_transaction: None,
                        })),
                    ),
                ],
            },
            vec![target, prefix_temp],
        );
        let mut string_facts = ProtoPromotionFacts::default();
        string_facts.record_temp_home_slot_for_test(target, HomeSlotKey::new(0, 0));
        assert!(inline_temps_in_proto_with_facts(
            &mut string,
            ReadabilityOptions::default(),
            &string_facts,
            DecompileDialect::Lua54,
            &[],
            RootAnalysisContext {
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                effects: &[]
            },
        ));
        assert!(matches!(
            string.body.stmts.as_slice(),
            [HirStmt::Block(block)]
                if matches!(block.stmts.as_slice(),
                    [HirStmt::Assign(_), HirStmt::Return(ret)]
                        if ret.values.fixed == vec![string_value])
        ));

        let source = LocalId(0);
        let source_write = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Local(source)],
            values: HirValuePack::fixed(vec![HirExpr::Integer(2)]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }));
        let mut local = empty_proto(
            HirBlock {
                stmts: vec![
                    producer(HirExpr::LocalRef(source)),
                    prefixed_block_sink(target, source_write),
                ],
            },
            vec![target],
        );
        local.locals.push(source);
        local.local_debug_hints.push(None);
        local.local_debug_scopes.push(None);
        let original = local.body.clone();
        let mut local_facts = ProtoPromotionFacts::default();
        local_facts.record_temp_home_slot_for_test(target, HomeSlotKey::new(0, 0));
        local_facts.record_local_home_slot(source, HomeSlotKey::new(1, 0));
        assert!(!inline_temps_in_proto_with_facts(
            &mut local,
            ReadabilityOptions::default(),
            &local_facts,
            DecompileDialect::Lua54,
            &[],
            RootAnalysisContext {
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                effects: &[]
            },
        ));
        assert_eq!(local.body, original);

        let sink = prefixed_block_sink(target, prefix);
        let site = inline_site_in_stmt(&sink, target)
            .expect("later unconditional return must expose a prefixed block site");
        assert!(matches!(site, InlineSite::PrefixedBlock));
        assert!(!site.allows(
            &HirExpr::Call(Box::new(HirCallExpr {
                argument_roots: Vec::new(),
                callee: HirExpr::GlobalRef(HirGlobalRef { key: "f".into() }),
                args: HirValuePack::default(),
                method: false,
                fastcall: None,
                method_key: None,
                callee_root_handoff: None,
                method_rewrite_transaction: None,
            })),
            ReadabilityOptions::default(),
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        ));

        let rewritten_prefix = prefixed_block_sink(
            target,
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(target)],
                values: HirValuePack::fixed(vec![HirExpr::Integer(8)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
        );
        assert!(inline_site_in_stmt(&rewritten_prefix, target).is_none());
    }

    #[test]
    fn repeat_head_transaction_inlines_a_stable_local_dependency() {
        let source = LocalId(0);
        let temp = TempId(0);
        let mut repeat = crate::hir::common::HirRepeat {
            body: HirBlock {
                stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(temp)],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(source)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                }))],
            },
            cond: HirExpr::TempRef(temp),
            lifetime: Default::default(),
        };
        let proto = empty_proto(
            HirBlock {
                stmts: vec![HirStmt::Repeat(Box::new(repeat.clone()))],
            },
            vec![temp],
        );
        let mut scratch = TempUseScratch::new(&proto, 1);
        let mut live_uses = vec![1];
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(temp);
        facts.record_local_home_slot(source, HomeSlotKey::new(0, 0));

        assert!(inline_repeat_head_scalar_temp_with_proven_prefix(
            &mut repeat,
            &mut scratch,
            &mut live_uses,
            &ReferenceCapturedBindings::default(),
            RepeatInlinePolicy {
                readability: ReadabilityOptions::default(),
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
            },
            &facts,
            &BTreeSet::new(),
        ));
        assert!(repeat.body.stmts.is_empty());
        assert_eq!(repeat.cond, HirExpr::LocalRef(source));
        assert_eq!(live_uses, vec![0]);
    }

    #[test]
    fn repeat_head_local_dependency_requires_a_stable_body_epoch() {
        let source = LocalId(0);
        let other = LocalId(1);
        let temp = TempId(0);
        let value = HirExpr::LocalRef(source);
        let condition = HirExpr::TempRef(temp);
        let direct_write = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Local(source)],
            values: HirValuePack::fixed(vec![HirExpr::Integer(2)]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }));
        let alias_write = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Local(other)],
            values: HirValuePack::fixed(vec![HirExpr::Integer(3)]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }));
        let empty_captures = ReferenceCapturedBindings::default();
        let empty_slots = BTreeSet::new();

        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(temp);
        facts.record_local_home_slot(source, HomeSlotKey::new(0, 0));
        facts.record_local_home_slot(other, HomeSlotKey::new(1, 0));
        let proof = RepeatHeadDependencyProof {
            reference_captured: &empty_captures,
            safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
            facts: &facts,
            captured_slots: &empty_slots,
        };
        assert!(repeat_head_dependencies_are_stable(
            &value,
            temp,
            std::slice::from_ref(&alias_write),
            &condition,
            &proof,
        ));
        assert!(!repeat_head_dependencies_are_stable(
            &value,
            temp,
            std::slice::from_ref(&direct_write),
            &condition,
            &proof,
        ));

        let mut alias_facts = ProtoPromotionFacts::default();
        alias_facts.record_home_free_temp(temp);
        alias_facts.record_local_home_slot(source, HomeSlotKey::new(0, 0));
        alias_facts.record_local_home_slot(other, HomeSlotKey::new(0, 0));
        assert!(!repeat_head_dependencies_are_stable(
            &value,
            temp,
            std::slice::from_ref(&alias_write),
            &condition,
            &RepeatHeadDependencyProof {
                reference_captured: &empty_captures,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                facts: &alias_facts,
                captured_slots: &empty_slots,
            },
        ));
    }

    #[test]
    fn repeat_head_captured_dependency_cannot_cross_observable_eval() {
        let source = LocalId(0);
        let captured_alias = LocalId(1);
        let temp = TempId(0);
        let value = HirExpr::LocalRef(source);
        let condition = HirExpr::TempRef(temp);
        let body = [call_stmt("mutate")];
        let empty_slots = BTreeSet::new();
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(temp);
        facts.record_home_free_temp(TempId(1));
        facts.record_local_home_slot(source, HomeSlotKey::new(0, 0));
        facts.record_local_home_slot(captured_alias, HomeSlotKey::new(0, 0));

        let empty_captures = ReferenceCapturedBindings::default();
        assert!(repeat_head_dependencies_are_stable(
            &value,
            temp,
            &body,
            &condition,
            &RepeatHeadDependencyProof {
                reference_captured: &empty_captures,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                facts: &facts,
                captured_slots: &empty_slots,
            },
        ));

        let mut captured = ReferenceCapturedBindings::default();
        captured.locals.insert(captured_alias);
        assert!(!repeat_head_dependencies_are_stable(
            &value,
            temp,
            &body,
            &condition,
            &RepeatHeadDependencyProof {
                reference_captured: &captured,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                facts: &facts,
                captured_slots: &empty_slots,
            },
        ));

        let closure_allocation = [HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(1))],
            values: HirValuePack::fixed(vec![HirExpr::Closure(Box::new(
                crate::hir::common::HirClosureExpr {
                    proto: crate::hir::common::HirProtoRef(1),
                    captures: Vec::new(),
                },
            ))]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }))];
        assert!(!repeat_head_dependencies_are_stable(
            &value,
            temp,
            &closure_allocation,
            &condition,
            &RepeatHeadDependencyProof {
                reference_captured: &captured,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                facts: &facts,
                captured_slots: &empty_slots,
            },
        ));

        let close = [HirStmt::Close(Box::new(crate::hir::common::HirClose {
            from_reg: 1,
        }))];
        assert!(!repeat_head_dependencies_are_stable(
            &value,
            temp,
            &close,
            &condition,
            &RepeatHeadDependencyProof {
                reference_captured: &captured,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                facts: &facts,
                captured_slots: &empty_slots,
            },
        ));
    }

    #[test]
    fn repeat_head_dynamic_producer_keeps_its_pre_body_eval_order() {
        let temp = TempId(0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(temp);
        let empty_captures = ReferenceCapturedBindings::default();
        let empty_slots = BTreeSet::new();
        let call = HirExpr::Call(Box::new(HirCallExpr {
            argument_roots: Vec::new(),
            callee: HirExpr::GlobalRef(HirGlobalRef {
                key: "produce".into(),
            }),
            args: HirValuePack::default(),
            method: false,
            fastcall: None,
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
        }));
        assert!(!repeat_head_dependencies_are_stable(
            &call,
            temp,
            &[],
            &HirExpr::TempRef(temp),
            &RepeatHeadDependencyProof {
                reference_captured: &empty_captures,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                facts: &facts,
                captured_slots: &empty_slots,
            },
        ));
    }

    #[test]
    fn terminal_nil_pack_accepts_explicitly_home_free_temps() {
        let mut block = terminal_nil_pack_block();
        let proto = empty_proto(block.clone(), vec![TempId(0), TempId(1)]);
        let scratch = TempUseScratch::new(&proto, 2);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(TempId(0));
        facts.record_home_free_temp(TempId(1));
        let snapshots = empty_capture_snapshots(2);
        let mut live_uses = vec![1, 1];

        assert!(inline_terminal_nil_return_pack(
            &mut block,
            &scratch,
            &mut live_uses,
            &facts,
            &snapshots,
            &[false, false],
        ));
        assert!(matches!(
            block.stmts.as_slice(),
            [HirStmt::Return(ret)]
                if ret.values.fixed == vec![HirExpr::Nil, HirExpr::Nil]
                    && ret.values.tail.is_none()
        ));
    }

    #[test]
    fn terminal_nil_pack_accepts_complete_invalidated_home_unions() {
        let mut block = terminal_nil_pack_block();
        let proto = empty_proto(block.clone(), vec![TempId(0), TempId(1)]);
        let scratch = TempUseScratch::new(&proto, 2);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(TempId(0), HomeSlotKey::new(0, 0));
        facts.record_temp_home_slot_for_test(TempId(1), HomeSlotKey::new(1, 0));
        facts.record_temp_home_merge(TempId(0), Some(BTreeSet::from([HomeSlotKey::new(2, 0)])));
        facts.record_temp_home_merge(TempId(1), Some(BTreeSet::from([HomeSlotKey::new(3, 0)])));
        let snapshots = empty_capture_snapshots(2);
        let mut live_uses = vec![1, 1];

        assert!(inline_terminal_nil_return_pack(
            &mut block,
            &scratch,
            &mut live_uses,
            &facts,
            &snapshots,
            &[false, false],
        ));
    }

    #[test]
    fn root_open_nil_pack_accepts_non_entry_exact_home_transaction() {
        let block = root_open_nil_pack_block();
        let proto = empty_proto(block.clone(), vec![TempId(0), TempId(1)]);
        let scratch = TempUseScratch::new(&proto, 2);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(TempId(0), HomeSlotKey::new(0, 0));
        facts.record_temp_home_slot_for_test(TempId(1), HomeSlotKey::new(1, 0));
        let snapshots = empty_capture_snapshots(2);
        let live_uses = vec![1, 1];

        assert!(
            root_open_return_nil_pack_plan(
                &block,
                &scratch,
                &live_uses,
                &facts,
                &snapshots,
                &[false, false],
            )
            .is_some()
        );
        assert!(
            root_open_return_nil_pack_plan(
                &block,
                &scratch,
                &live_uses,
                &facts,
                &snapshots,
                &[true, false],
            )
            .is_none()
        );

        let mut alias_read = block;
        let HirStmt::Return(ret) = &mut alias_read.stmts[1] else {
            unreachable!("open nil-pack fixture must end in return")
        };
        ret.values
            .tail
            .as_mut()
            .and_then(HirPackTail::call_mut)
            .expect("open nil-pack fixture must keep a tail call")
            .args = HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(0))]);
        facts.record_local_home_slot(LocalId(0), HomeSlotKey::new(0, 0));
        assert!(
            root_open_return_nil_pack_plan(
                &alias_read,
                &scratch,
                &live_uses,
                &facts,
                &snapshots,
                &[false, false],
            )
            .is_none()
        );
    }

    #[test]
    fn root_open_nil_pack_mixed_homefree_target_uses_physical_root_fact() {
        let mut block = root_open_nil_pack_block();
        let proto = empty_proto(block.clone(), vec![TempId(0), TempId(1)]);
        let scratch = TempUseScratch::new(&proto, 2);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(TempId(0), HomeSlotKey::new(0, 0));
        facts.record_home_free_temp(TempId(1));
        let snapshots = empty_capture_snapshots(2);
        let mut live_uses = vec![1, 1];
        let (_, physical_roots) = collect_temp_root_lifetimes(
            &block.stmts,
            &facts,
            RootAnalysisContext {
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                effects: &[],
            },
            &[],
        );

        assert!(!physical_roots[0]);
        assert!(inline_root_open_return_nil_pack(
            &mut block,
            &scratch,
            &mut live_uses,
            &facts,
            &snapshots,
            &physical_roots,
        ));
        assert!(matches!(
            block.stmts.as_slice(),
            [HirStmt::Return(ret)]
                if ret.values.fixed == vec![HirExpr::Nil, HirExpr::Nil]
                    && ret.values.tail.is_some()
        ));

        let mut rooted = root_open_nil_pack_block();
        rooted.stmts.insert(
            0,
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(2))],
                values: HirValuePack::fixed(vec![HirExpr::Call(Box::new(HirCallExpr {
                    argument_roots: Vec::new(),
                    callee: HirExpr::GlobalRef(HirGlobalRef {
                        key: "resource".into(),
                    }),
                    args: HirValuePack::default(),
                    method: false,
                    fastcall: None,
                    method_key: None,
                    callee_root_handoff: None,
                    method_rewrite_transaction: None,
                }))]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
        );
        rooted.stmts.insert(1, call_stmt("collectgarbage"));
        let rooted_proto = empty_proto(rooted.clone(), vec![TempId(0), TempId(1), TempId(2)]);
        let rooted_scratch = TempUseScratch::new(&rooted_proto, 3);
        let mut rooted_facts = facts;
        rooted_facts.record_temp_home_slot_for_test(TempId(2), HomeSlotKey::new(0, 0));
        let rooted_snapshots = empty_capture_snapshots(4);
        let (_, rooted_physical_roots) = collect_temp_root_lifetimes(
            &rooted.stmts,
            &rooted_facts,
            RootAnalysisContext {
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                effects: &[],
            },
            &[],
        );

        assert!(rooted_physical_roots[2]);
        assert!(
            root_open_return_nil_pack_plan(
                &rooted,
                &rooted_scratch,
                &[1, 1, 0],
                &rooted_facts,
                &rooted_snapshots,
                &rooted_physical_roots,
            )
            .is_none()
        );
    }

    #[test]
    fn terminal_nil_pack_uses_home_universe_for_unknown_targets() {
        let mut block = terminal_nil_pack_block();
        let proto = empty_proto(block.clone(), vec![TempId(0), TempId(1)]);
        let scratch = TempUseScratch::new(&proto, 2);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(TempId(0), HomeSlotKey::new(0, 0));
        facts.record_temp_home_slot_for_test(TempId(1), HomeSlotKey::new(1, 0));
        facts.record_temp_home_merge(TempId(0), None);
        facts.record_temp_home_merge(TempId(1), None);
        let mut live_uses = vec![1, 1];

        assert!(inline_terminal_nil_return_pack(
            &mut block,
            &scratch,
            &mut live_uses,
            &facts,
            &empty_capture_snapshots(2),
            &[false, false],
        ));

        let mut captured = terminal_nil_pack_block();
        let original = captured.clone();
        let captured_home = BTreeSet::from([HomeSlotKey::new(0, 0)]);
        let mut snapshots = CapturedSlotSnapshots::new(2, &captured_home);
        snapshots.push(&captured_home);
        snapshots.push(&captured_home);
        let mut live_uses = vec![1, 1];
        assert!(!inline_terminal_nil_return_pack(
            &mut captured,
            &scratch,
            &mut live_uses,
            &facts,
            &snapshots,
            &[false, false],
        ));
        assert_eq!(captured, original);
    }

    #[test]
    #[should_panic(
        expected = "unknown physical binding requires a non-empty physical-home universe"
    )]
    fn unknown_home_without_a_physical_universe_is_an_invalid_fact_set() {
        let _ = ProtoPromotionFacts::default().complete_temp_home_slots(TempId(0));
    }

    #[test]
    fn root_nil_gap_uses_complete_possible_home_sets_for_clobbers() {
        let gap = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(2))],
            values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }));
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(TempId(0), HomeSlotKey::new(0, 0));
        facts.record_temp_home_slot_for_test(TempId(2), HomeSlotKey::new(2, 0));
        facts.record_temp_home_merge(TempId(2), Some(BTreeSet::from([HomeSlotKey::new(3, 0)])));
        facts.record_local_home_slot(LocalId(0), HomeSlotKey::new(3, 0));

        assert!(root_nil_pack_gap_preserves_slots(
            &gap,
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::from([HomeSlotKey::new(0, 0)]),
            &facts,
        ));
        assert!(!root_nil_pack_gap_preserves_slots(
            &gap,
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::from([HomeSlotKey::new(3, 0)]),
            &facts,
        ));
        assert!(!root_nil_pack_gap_preserves_slots(
            &HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(9))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(8)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::from([HomeSlotKey::new(0, 0)]),
            &facts,
        ));
        assert!(root_nil_pack_gap_preserves_slots(
            &HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(9))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(8)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::new(),
            &facts,
        ));
        assert!(!root_nil_pack_gap_preserves_slots(
            &HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(0))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::new(),
            &facts,
        ));

        let alias_read = HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
            names: vec!["observed".into()],
            values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(0))]),
        }));
        assert!(root_nil_pack_gap_preserves_slots(
            &alias_read,
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::from([HomeSlotKey::new(0, 0)]),
            &facts,
        ));
        assert!(!root_nil_pack_gap_preserves_slots(
            &alias_read,
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::from([HomeSlotKey::new(3, 0)]),
            &facts,
        ));
        assert!(root_nil_pack_gap_preserves_slots_with_context(
            &alias_read,
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::from([HomeSlotKey::new(3, 0)]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &facts,
        ));

        let early_return = HirStmt::If(Box::new(crate::hir::common::HirIf {
            cond: HirExpr::Boolean(true),
            then_block: HirBlock {
                stmts: vec![HirStmt::Return(Box::new(HirReturn {
                    values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
                }))],
            },
            else_block: None,
        }));
        assert!(root_nil_pack_gap_preserves_slots(
            &early_return,
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::from([HomeSlotKey::new(3, 0)]),
            &facts,
        ));

        let label_id = crate::hir::common::HirLabelId(0);
        let label = HirStmt::Label(Box::new(crate::hir::common::HirLabel {
            id: label_id,
            tbc_barriers: Vec::new(),
        }));
        assert!(root_nil_pack_gap_preserves_slots_with_context(
            &label,
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::from([HomeSlotKey::new(3, 0)]),
            &BTreeSet::from([HomeSlotKey::new(3, 0)]),
            &BTreeSet::new(),
            &facts,
        ));
        assert!(!root_nil_pack_gap_preserves_slots_with_context(
            &label,
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::from([HomeSlotKey::new(3, 0)]),
            &BTreeSet::from([HomeSlotKey::new(3, 0)]),
            &BTreeSet::from([label_id]),
            &facts,
        ));

        let nested_disjoint = HirStmt::Block(Box::new(HirBlock { stmts: vec![gap] }));
        assert!(root_nil_pack_gap_preserves_slots(
            &nested_disjoint,
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::from([HomeSlotKey::new(0, 0)]),
            &facts,
        ));
        assert!(!root_nil_pack_gap_preserves_slots(
            &nested_disjoint,
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::from([HomeSlotKey::new(3, 0)]),
            &facts,
        ));
        assert!(root_nil_pack_gap_preserves_slots(
            &HirStmt::Close(Box::new(crate::hir::common::HirClose { from_reg: 1 })),
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::from([HomeSlotKey::new(0, 0)]),
            &facts,
        ));
        assert!(!root_nil_pack_gap_preserves_slots(
            &HirStmt::Close(Box::new(crate::hir::common::HirClose { from_reg: 0 })),
            &BTreeSet::from([TempId(0)]),
            &BTreeSet::from([HomeSlotKey::new(0, 0)]),
            &facts,
        ));
    }

    #[test]
    fn numeric_for_header_accepts_stable_vararg_but_rejects_dynamic_call() {
        let numeric_for = || {
            HirStmt::NumericFor(Box::new(crate::hir::common::HirNumericFor {
                binding: crate::hir::common::LocalId(0),
                start: HirExpr::TempRef(TempId(0)),
                limit: HirExpr::Integer(1),
                step: HirExpr::Integer(1),
                body: HirBlock::default(),
            }))
        };
        let candidate = |value| {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(0))],
                values: HirValuePack::fixed(vec![value]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };
        let mut stable = HirBlock {
            stmts: vec![candidate(HirExpr::VarArg), numeric_for()],
        };
        let proto = empty_proto(stable.clone(), vec![TempId(0)]);
        let scratch = TempUseScratch::new(&proto, 1);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(TempId(0));
        let snapshots = empty_capture_snapshots(2);
        let mut live_uses = vec![1];
        let mut removed = vec![false; 2];

        assert!(inline_numeric_for_stable_header_aliases(
            &mut stable,
            0..1,
            &mut live_uses,
            NumericForHeaderProof {
                scratch: &scratch,
                facts: &facts,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                reference_captured: &ReferenceCapturedBindings::default(),
                captured_slots_before_stmt: &snapshots,
                reference_captured_home_slots: &BTreeSet::new(),
            },
            &mut removed,
        ));
        assert!(matches!(
            &stable.stmts[1],
            HirStmt::NumericFor(numeric_for) if numeric_for.start == HirExpr::VarArg
        ));
        assert_eq!(removed, vec![true, false]);

        let dynamic_call = HirExpr::Call(Box::new(HirCallExpr {
            argument_roots: Vec::new(),
            callee: HirExpr::GlobalRef(HirGlobalRef {
                key: "next_start".into(),
            }),
            args: HirValuePack::default(),
            method: false,
            fastcall: None,
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
        }));
        let mut dynamic = HirBlock {
            stmts: vec![candidate(dynamic_call), numeric_for()],
        };
        let proto = empty_proto(dynamic.clone(), vec![TempId(0)]);
        let scratch = TempUseScratch::new(&proto, 1);
        let mut live_uses = vec![1];
        let mut removed = vec![false; 2];
        assert!(!inline_numeric_for_stable_header_aliases(
            &mut dynamic,
            0..1,
            &mut live_uses,
            NumericForHeaderProof {
                scratch: &scratch,
                facts: &facts,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                reference_captured: &ReferenceCapturedBindings::default(),
                captured_slots_before_stmt: &snapshots,
                reference_captured_home_slots: &BTreeSet::new(),
            },
            &mut removed,
        ));
        assert_eq!(removed, vec![false, false]);
    }

    #[test]
    fn numeric_for_header_value_requires_disjoint_later_write_homes() {
        let block = || HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: HirValuePack::fixed(vec![HirExpr::TempRef(TempId(2))]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(1))],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(9)]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
                HirStmt::NumericFor(Box::new(crate::hir::common::HirNumericFor {
                    binding: LocalId(0),
                    start: HirExpr::TempRef(TempId(0)),
                    limit: HirExpr::Integer(1),
                    step: HirExpr::Integer(1),
                    body: HirBlock::default(),
                })),
            ],
        };
        let snapshots = empty_capture_snapshots(3);

        let mut disjoint = block();
        let proto = empty_proto(disjoint.clone(), vec![TempId(0), TempId(1), TempId(2)]);
        let scratch = TempUseScratch::new(&proto, 3);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(TempId(0));
        facts.record_home_free_temp(TempId(1));
        facts.record_temp_home_slot_for_test(TempId(2), HomeSlotKey::new(2, 0));
        let mut live_uses = vec![1, 0, 1];
        let mut removed = vec![false; 3];
        assert!(inline_numeric_for_stable_header_aliases(
            &mut disjoint,
            0..2,
            &mut live_uses,
            NumericForHeaderProof {
                scratch: &scratch,
                facts: &facts,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                reference_captured: &ReferenceCapturedBindings::default(),
                captured_slots_before_stmt: &snapshots,
                reference_captured_home_slots: &BTreeSet::new(),
            },
            &mut removed,
        ));
        assert_eq!(removed, vec![true, false, false]);

        let mut overlapping = block();
        let proto = empty_proto(overlapping.clone(), vec![TempId(0), TempId(1), TempId(2)]);
        let scratch = TempUseScratch::new(&proto, 3);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_temp(TempId(0));
        facts.record_temp_home_slot_for_test(TempId(1), HomeSlotKey::new(2, 0));
        facts.record_temp_home_slot_for_test(TempId(2), HomeSlotKey::new(2, 0));
        let mut live_uses = vec![1, 0, 1];
        let mut removed = vec![false; 3];
        assert!(!inline_numeric_for_stable_header_aliases(
            &mut overlapping,
            0..2,
            &mut live_uses,
            NumericForHeaderProof {
                scratch: &scratch,
                facts: &facts,
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                reference_captured: &ReferenceCapturedBindings::default(),
                captured_slots_before_stmt: &snapshots,
                reference_captured_home_slots: &BTreeSet::new(),
            },
            &mut removed,
        ));
        assert_eq!(removed, vec![false, false, false]);
    }

    #[test]
    fn open_return_aliases_accept_home_free_bindings_but_not_identity_clobbers() {
        let mut block = open_return_alias_block(TempId(4));
        let mut facts = ProtoPromotionFacts::default();
        for temp in [TempId(0), TempId(1), TempId(2), TempId(3), TempId(4)] {
            facts.record_home_free_temp(temp);
        }
        let snapshots = empty_capture_snapshots(4);
        let mut live_uses = vec![1; 5];
        let mut removed = vec![false; 4];
        let proto = empty_proto(block.clone(), (0..5).map(TempId).collect());
        let scratch = TempUseScratch::new(&proto, 5);

        assert!(inline_open_return_fixed_alias_run(
            &mut block,
            0..3,
            &mut live_uses,
            OpenReturnFixedAliasProof {
                scratch: &scratch,
                facts: &facts,
                captured_slots_before_stmt: &snapshots,
                reference_captured_home_slots: &BTreeSet::new(),
            },
            &mut removed,
        ));
        let HirStmt::Return(ret) = &block.stmts[3] else {
            panic!("validated alias run must keep the return sink")
        };
        assert!(ret.values.fixed == vec![HirExpr::TempRef(TempId(2)), HirExpr::TempRef(TempId(3))]);
        assert_eq!(removed, vec![true, true, false, false]);

        let mut clobbered = open_return_alias_block(TempId(2));
        let original = clobbered.clone();
        let mut live_uses = vec![1; 5];
        let mut removed = vec![false; 4];
        let proto = empty_proto(clobbered.clone(), (0..5).map(TempId).collect());
        let scratch = TempUseScratch::new(&proto, 5);
        assert!(!inline_open_return_fixed_alias_run(
            &mut clobbered,
            0..3,
            &mut live_uses,
            OpenReturnFixedAliasProof {
                scratch: &scratch,
                facts: &facts,
                captured_slots_before_stmt: &snapshots,
                reference_captured_home_slots: &BTreeSet::new(),
            },
            &mut removed,
        ));
        assert_eq!(clobbered, original);
    }

    #[test]
    fn numeric_for_binding_chain_uses_complete_source_and_capture_homes() {
        let candidate = |target, value| {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(target)],
                values: HirValuePack::fixed(vec![value]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };
        let loop_sink = || {
            HirStmt::NumericFor(Box::new(crate::hir::common::HirNumericFor {
                binding: LocalId(1),
                start: HirExpr::TempRef(TempId(2)),
                limit: HirExpr::Integer(1),
                step: HirExpr::Integer(1),
                body: HirBlock::default(),
            }))
        };
        let block = |middle| HirBlock {
            stmts: vec![
                candidate(TempId(0), HirExpr::LocalRef(LocalId(0))),
                candidate(TempId(1), middle),
                candidate(TempId(2), HirExpr::TempRef(TempId(0))),
                loop_sink(),
            ],
        };
        let stable = block(HirExpr::Integer(7));
        let proto = empty_proto(stable.clone(), vec![TempId(0), TempId(1), TempId(2)]);
        let scratch = TempUseScratch::new(&proto, 3);
        let mut facts = ProtoPromotionFacts::default();
        for temp in [TempId(0), TempId(1), TempId(2)] {
            facts.record_home_free_temp(temp);
        }
        let source_home = HomeSlotKey::new(5, 0);
        facts.record_local_home_slot(LocalId(0), source_home);
        let snapshots = empty_capture_snapshots(4);
        let captured_homes = BTreeSet::from([source_home]);
        let mut reference_captured = ReferenceCapturedBindings::default();
        reference_captured.locals.insert(LocalId(0));
        let live_uses = vec![1, 0, 1];
        let proof = NumericForHeaderProof {
            scratch: &scratch,
            facts: &facts,
            safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
            reference_captured: &reference_captured,
            captured_slots_before_stmt: &snapshots,
            reference_captured_home_slots: &captured_homes,
        };

        let plan = numeric_for_binding_header_alias_plan(&stable, 0..3, 2, &live_uses, &proof)
            .expect("event-free setup cannot mutate the captured source");
        assert_eq!(plan.replacement, HirExpr::LocalRef(LocalId(0)));
        assert_eq!(plan.chain, vec![(2, TempId(2)), (0, TempId(0))]);

        let dynamic = block(HirExpr::Call(Box::new(HirCallExpr {
            argument_roots: Vec::new(),
            callee: HirExpr::GlobalRef(HirGlobalRef {
                key: "mutate_source".into(),
            }),
            args: HirValuePack::default(),
            method: false,
            fastcall: None,
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
        })));
        assert!(
            numeric_for_binding_header_alias_plan(&dynamic, 0..3, 2, &live_uses, &proof).is_none()
        );

        let mut sink_prefix = stable;
        let HirStmt::NumericFor(numeric_for) = &mut sink_prefix.stmts[3] else {
            unreachable!("fixture must end in numeric-for")
        };
        numeric_for.start = HirExpr::Call(Box::new(HirCallExpr {
            argument_roots: Vec::new(),
            callee: HirExpr::GlobalRef(HirGlobalRef {
                key: "mutate_source".into(),
            }),
            args: HirValuePack::default(),
            method: false,
            fastcall: None,
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
        }));
        numeric_for.limit = HirExpr::TempRef(TempId(2));
        assert!(
            numeric_for_binding_header_alias_plan(&sink_prefix, 0..3, 2, &live_uses, &proof)
                .is_none()
        );
    }

    #[test]
    fn numeric_for_binding_chain_accepts_unknown_external_home_without_interference() {
        let candidate = |target, value| {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(target)],
                values: HirValuePack::fixed(vec![value]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };
        let block = |middle_target| HirBlock {
            stmts: vec![
                candidate(TempId(0), HirExpr::TempRef(TempId(3))),
                candidate(middle_target, HirExpr::Integer(7)),
                candidate(TempId(2), HirExpr::TempRef(TempId(0))),
                HirStmt::NumericFor(Box::new(crate::hir::common::HirNumericFor {
                    binding: LocalId(0),
                    start: HirExpr::TempRef(TempId(2)),
                    limit: HirExpr::Integer(1),
                    step: HirExpr::Integer(1),
                    body: HirBlock::default(),
                })),
            ],
        };
        let stable = block(TempId(1));
        let proto = empty_proto(
            stable.clone(),
            vec![TempId(0), TempId(1), TempId(2), TempId(3)],
        );
        let scratch = TempUseScratch::new(&proto, 4);
        let mut facts = ProtoPromotionFacts::default();
        for temp in [TempId(0), TempId(1), TempId(2)] {
            facts.record_home_free_temp(temp);
        }
        facts.record_temp_home_slot_for_test(TempId(3), HomeSlotKey::new(3, 0));
        facts.record_temp_home_merge(TempId(3), None);
        let snapshots = empty_capture_snapshots(4);
        let live_uses = vec![1, 0, 1, 1];
        let proof = NumericForHeaderProof {
            scratch: &scratch,
            facts: &facts,
            safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
            reference_captured: &ReferenceCapturedBindings::default(),
            captured_slots_before_stmt: &snapshots,
            reference_captured_home_slots: &BTreeSet::new(),
        };

        let plan = numeric_for_binding_header_alias_plan(&stable, 0..3, 2, &live_uses, &proof)
            .expect("external source remains stable across a disjoint setup");
        assert_eq!(plan.replacement, HirExpr::TempRef(TempId(3)));
        assert!(
            numeric_for_binding_header_alias_plan(&block(TempId(3)), 0..3, 2, &live_uses, &proof,)
                .is_none()
        );
    }

    #[test]
    fn open_return_aliases_use_complete_home_unions_and_capture_relation() {
        let build_facts = || {
            let mut facts = ProtoPromotionFacts::default();
            for index in 0..5 {
                let temp = TempId(index);
                facts.record_temp_home_slot_for_test(temp, HomeSlotKey::new(index, 0));
                facts.record_temp_home_merge(
                    temp,
                    Some(BTreeSet::from([HomeSlotKey::new(index + 10, 0)])),
                );
            }
            facts
        };
        let snapshots = empty_capture_snapshots(4);

        let mut accepted = open_return_alias_block(TempId(4));
        let facts = build_facts();
        let proto = empty_proto(accepted.clone(), (0..5).map(TempId).collect());
        let scratch = TempUseScratch::new(&proto, 5);
        let mut live_uses = vec![1; 5];
        let mut removed = vec![false; 4];
        assert!(inline_open_return_fixed_alias_run(
            &mut accepted,
            0..3,
            &mut live_uses,
            OpenReturnFixedAliasProof {
                scratch: &scratch,
                facts: &facts,
                captured_slots_before_stmt: &snapshots,
                reference_captured_home_slots: &BTreeSet::new(),
            },
            &mut removed,
        ));

        let mut captured = open_return_alias_block(TempId(4));
        let mut live_uses = vec![1; 5];
        let mut removed = vec![false; 4];
        assert!(!inline_open_return_fixed_alias_run(
            &mut captured,
            0..3,
            &mut live_uses,
            OpenReturnFixedAliasProof {
                scratch: &scratch,
                facts: &facts,
                captured_slots_before_stmt: &snapshots,
                reference_captured_home_slots: &BTreeSet::from([HomeSlotKey::new(2, 0)]),
            },
            &mut removed,
        ));

        let mut clobbered = open_return_alias_block(TempId(4));
        let mut overlapping_facts = build_facts();
        overlapping_facts
            .record_temp_home_merge(TempId(4), Some(BTreeSet::from([HomeSlotKey::new(2, 0)])));
        let mut live_uses = vec![1; 5];
        let mut removed = vec![false; 4];
        assert!(!inline_open_return_fixed_alias_run(
            &mut clobbered,
            0..3,
            &mut live_uses,
            OpenReturnFixedAliasProof {
                scratch: &scratch,
                facts: &overlapping_facts,
                captured_slots_before_stmt: &snapshots,
                reference_captured_home_slots: &BTreeSet::new(),
            },
            &mut removed,
        ));

        let captured_temp = TempId(0);
        let closure_temp = TempId(1);
        let assign = |target, value| {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(target)],
                values: HirValuePack::fixed(vec![value]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };
        let mut captured_rebind = empty_proto(
            HirBlock {
                stmts: vec![
                    assign(
                        closure_temp,
                        HirExpr::Closure(Box::new(HirClosureExpr {
                            proto: crate::hir::common::HirProtoRef(1),
                            captures: vec![HirCapture {
                                mode: HirCaptureMode::ByReference,
                                value: HirExpr::TempRef(captured_temp),
                            }],
                        })),
                    ),
                    assign(captured_temp, HirExpr::Integer(7)),
                    HirStmt::Return(Box::new(HirReturn {
                        values: HirValuePack::fixed(vec![
                            HirExpr::TempRef(captured_temp),
                            HirExpr::TempRef(closure_temp),
                        ]),
                    })),
                ],
            },
            vec![captured_temp, closure_temp],
        );
        let mut captured_rebind_facts = ProtoPromotionFacts::default();
        captured_rebind_facts.record_temp_home_slot_for_test(captured_temp, HomeSlotKey::new(0, 0));
        captured_rebind_facts.record_temp_home_slot_for_test(closure_temp, HomeSlotKey::new(1, 0));
        inline_temps_in_proto_with_facts(
            &mut captured_rebind,
            ReadabilityOptions::default(),
            &captured_rebind_facts,
            DecompileDialect::Lua54,
            &[],
            RootAnalysisContext {
                safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
                effects: &[],
            },
        );
        assert_eq!(
            captured_rebind.inline_dispositions.temp(captured_temp),
            crate::hir::common::HirInlineDisposition::Preserve(BTreeSet::from([
                HirInlineRetentionReason::CapturedValueEpoch,
            ]))
        );
    }
}
