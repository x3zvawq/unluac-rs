//! 这个文件实现 HIR 的第一批 temp inlining。
//!
//! 常规路径以 use-count、home/capture 与求值区域事实证明等价性，只折叠“单目标 temp
//! 赋值，并且被紧邻下一条
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
//! 还可收回 owner 保持存活的裸 receiver，普通点调用仍按两次读取处理。
//! 相邻 sink 若是无条件 `Block`，只递归穿过零前缀的第一条语句；第二条及更晚消费仍需
//! block-prefix 的求值、写入、capture 与控制流摘要，不能把整个词法块视为透明。
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
    expr_is_discard_safe, expr_is_effect_invariant_in_single_value_context, expr_is_repeatable,
    expr_is_repeatable_in_single_value_context, expr_observes_eval_order,
    expr_requires_ordered_snapshot,
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
    TempUseScratch, collect_expr_temp_uses_summary, collect_stmt_temp_uses, inline_candidate,
    max_temp_index_in_block,
};
use super::mention::{ReferenceCapturedBindings, stmt_writes_temp};
use super::root_lifetimes::{
    CallRootLifetimeIndices, collect_call_root_lifetimes, collect_lookup_gc_root_lifetimes,
};
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

fn collect_temp_root_lifetimes(
    stmts: &[HirStmt],
    facts: &ProtoPromotionFacts,
) -> (CallRootLifetimeIndices, Vec<bool>) {
    let call_roots = collect_call_root_lifetimes(stmts, facts, |_| true);
    let mut marked = call_roots.marked_stmts(stmts.len());
    collect_lookup_gc_root_lifetimes(stmts, facts, |_| true).mark_stmts(&mut marked);
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
    let (mut call_root_indices, mut physical_root_lifetimes) =
        collect_temp_root_lifetimes(&block.stmts, facts);
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
        (call_root_indices, physical_root_lifetimes) =
            collect_temp_root_lifetimes(&block.stmts, facts);
    }

    if inline_terminal_nil_return_pack(
        block,
        &workspace.uses,
        live_use_counts,
        facts,
        &captured_slots_before_stmt,
        workspace.has_resource_boundary,
        &physical_root_lifetimes,
    ) {
        changed = true;
        captured_slots_before_stmt =
            captured_slots_before_stmts(block, facts, inherited_captured_slots);
        (call_root_indices, physical_root_lifetimes) =
            collect_temp_root_lifetimes(&block.stmts, facts);
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
        (call_root_indices, physical_root_lifetimes) =
            collect_temp_root_lifetimes(&block.stmts, facts);
    }

    if matches!(workspace.scope, TempInlineScope::All)
        && inline_adjacent_call_root_expression_overwrites(
            block,
            &workspace.uses,
            live_use_counts,
            &captured_slots_before_stmt,
            &call_root_indices,
        )
    {
        changed = true;
        captured_slots_before_stmt =
            captured_slots_before_stmts(block, facts, inherited_captured_slots);
        (_, physical_root_lifetimes) = collect_temp_root_lifetimes(&block.stmts, facts);
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
            // 候选拒绝[SemanticBarrier:Lifetime]：被 physical-root lifetime 标记的 call/lookup 结果仍承担 VM root；提前删除会改变对象存活期（regress_356）。
            && !physical_root_lifetimes[index]
            // 候选拒绝[SemanticBarrier:Lifetime]：`t=f(); box.x=t` 中 t 是写入完成前的唯一 VM root，删除可能改变 GC/析构可观察时机。
            // A call result stored in a table can outlive the immediate write. Removing the
            // temp would remove the only lexical/VM root before a later rawset or table clear;
            // keep that producer unless a separate lifetime proof exists.
            && !(matches!(value, HirExpr::Call(_))
                && kept_rev
                    .last()
                    .is_some_and(|next_stmt| stmt_stores_temp_in_table(next_stmt, temp)))
            // 候选拒绝[LayerBoundary]：debug temp 是显式源码 binding，交给 locals/source identity owner。
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
            )
            // 候选拒绝[PolicyBoundary]：复杂 child closure 保留命名 binding，避免生成多行 IIFE。
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
) -> bool {
    // 候选拒绝[SemanticBarrier:ControlFlow]：循环外 `t=f()` 不能内联进 while 条件而改成每轮调用；见 regress_172#1/#2。
    // 候选拒绝[SemanticBarrier:EvalOrder]：无 capture closure 仍会分配新 identity；`a=f(); t=function() end; g(a,t)` 不能把分配移到 `f()` 之后。
    let producer_requires_order =
        expr_requires_ordered_snapshot(value) || !expr_is_discard_safe(value);
    let producer_has_observable_eval =
        expr_observes_eval_order(value) || !expr_is_discard_safe(value);
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
        // 候选拒绝[LayerBoundary]：debug identity 由 locals/source-binding owner 保留。
        if scratch.has_debug_local_hint(root) || scratch.has_debug_local_hint(target) {
            continue;
        }
        // 候选拒绝[ProofIncomplete]：RHS 含 lookup/call/allocation/closure 等事件时，尚无同句事件与新 capture 的完整证明。
        if !call_root_overwrite_is_inlineable(overwrite, root) {
            continue;
        }
        // 候选拒绝[SemanticBarrier:Capture]：已引用捕获 root home 时，删除 producer 会让 closure 看不到 call result。
        if captured_slots_before_stmt
            .get(overwrite_index)
            .expect("capture snapshots must cover the call-root overwrite")
            .contains(&pair.home())
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
                && call_root_rhs_is_stable_direct_value(&binary.rhs)
        }
        HirExpr::LogicalOr(logical) => {
            matches!(&logical.lhs, HirExpr::TempRef(source) if *source == root)
                && call_root_rhs_is_stable_direct_value(&logical.rhs)
        }
        _ => false,
    }
}

fn call_root_rhs_is_stable_direct_value(expr: &HirExpr) -> bool {
    call_root_rhs_is_primitive_literal(expr)
        || matches!(
            expr,
            HirExpr::ParamRef(_) | HirExpr::LocalRef(_) | HirExpr::UpvalueRef(_)
        )
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
        // 候选拒绝[SemanticBarrier:Lifetime]：alias 链节点有额外 use 时不能随 run 整段删除。
        // 候选拒绝[SemanticBarrier:EvalOrder]：非 repeatable 值或转发更早 observable def 会被延后/重复求值。
        // 候选拒绝[PolicyBoundary]：nested sink 继续服从固定复杂度展示阈值。
        // 候选拒绝[SemanticBarrier:Capture]：capture/self-rebind 改写会改变闭包或状态所见值。
        // 候选拒绝[LayerBoundary]：debug temp 是源码 binding。
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
            live_use_counts,
            NumericForHeaderProof {
                scratch: uses,
                facts,
                captured_slots_before_stmt,
                reference_captured_home_slots: trusted_reference_captured_home_slots(
                    reference_captured,
                    facts,
                ),
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
            // 候选拒绝[LayerBoundary]：debug callee 是源码 binding；由 locals owner 保留。
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
            if matches!(value, HirExpr::Call(_)) && stmt_stores_temp_in_table(&rewritten_sink, temp)
            {
                // 候选拒绝[SemanticBarrier:Lifetime]：call result 写表前由 temp 保持存活，删除会改变 VM root 生命周期。
                complete_run = false;
                break;
            }
            if use_count == 0 {
                if candidate_is_safe && expr_is_discard_safe(value) {
                    discarded_uses.push(collect_expr_temp_uses_summary(value, uses));
                    continue;
                }
                // 候选拒绝[SemanticBarrier:EvalOrder]：零 use 但不可安全丢弃的 call/lookup/allocation 仍是原序列中的可观察事件。
                // 候选拒绝[SemanticBarrier:Capture]：被捕获/self-rebinding 的零 use 写也不能由 run 删除。
                // 候选拒绝[LayerBoundary]：debug temp 即使零 use 也属于 source binding。
                complete_run = false;
                break;
            }
            let Some(site) = inline_site_in_stmt(&rewritten_sink, temp) else {
                if collect_stmt_temp_uses(&rewritten_sink, uses).count(temp) == 0 {
                    // 候选拒绝[ProofIncomplete]：sink 外 live use 或 planned discard 的暂存 use 会阻断整包融合；当前计划缺少 call 依赖切片与计划内 use delta。
                    complete_run = false;
                    break;
                }
                // sink 内 use 的 Closure capture 等明确边界由 site classifier 标记。
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
                // 候选拒绝[SemanticBarrier:Capture]：candidate home capture/self-rebind 会改变 closure 或状态所见值。
                // 候选拒绝[LayerBoundary]：debug candidate 是源码 binding。
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
    // 分析停用[ProofIncomplete]：home compaction 下缺少跨 gap 的稳定物理槽证明；应让 promotion 暴露最终 slot epoch。
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
            // 候选拒绝[LayerBoundary]：local/param/upvalue 等源码 identity 不由 raw-temp nil-pack 规则删除。
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
            // 候选拒绝[ProofIncomplete]：非 entry-nil materialization 尚未证明可跨整段 root 前缀消除；应以目标 epoch 的完整 def/use 取代来源形状。
            !facts.overwrites_entry_nil(*target)
                // 候选拒绝[SemanticBarrier:Lifetime]：额外 use 会继续观察原 nil 写入后的 temp。
                || total_use_count(*target, live_use_counts) != 1
                // 候选拒绝[LayerBoundary]：debug temp 是源码 binding。
                || scratch.has_debug_local_hint(*target)
                // 候选拒绝[ProofIncomplete]：缺可信 home 时，当前计划没有精确 slot epoch 证明。
                // 候选拒绝[SemanticBarrier:Capture]：已引用捕获 target home 时，删除写入会让 closure 观察旧值。
                || facts
                    .trusted_temp_home_slot(*target)
                    .is_none_or(|slot| {
                        target_slots.insert(slot);
                        captured_slots.contains(&slot)
                    })
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
    physical_root_lifetimes: &[bool],
) -> bool {
    // 分析停用[ProofIncomplete]：home compaction 或 proto 内任意 resource boundary 会 blanket 禁用本规则；应改用候选区间的精确 slot/lifetime 事实。
    if facts.compacts_home_slots() || has_resource_boundary {
        return false;
    }
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
        // 候选拒绝[LayerBoundary]：并行写含 local/param/upvalue 等 identity 时由 locals/resource owner 处理，不删其声明或写入。
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
        let Some(slot) = facts.trusted_temp_home_slot(*target) else {
            // 候选拒绝[ProofIncomplete]：目标缺可信 home，无法证明 nil 写与 return 读取保持同槽同 epoch。
            return false;
        };
        // 候选拒绝[SemanticBarrier:Capture]：closure 已引用捕获目标 home 时，删除 nil 写会让其继续观察旧值。
        if captured_slots.contains(&slot) {
            return false;
        }
        // 候选拒绝[LayerBoundary]：debug temp 是源码 binding。
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

fn root_nil_pack_gap_preserves_slots(
    stmt: &HirStmt,
    protected: &BTreeSet<HomeSlotKey>,
    facts: &ProtoPromotionFacts,
) -> bool {
    match stmt {
        HirStmt::Assign(assign) => {
            // 候选拒绝[ProofIncomplete]：gap 目标缺可信 home 时没有区间 clobber 证明；应消费统一 stmt write-set。
            // 候选拒绝[SemanticBarrier:EvalOrder]：`t=nil; t=x; return t` 若跨过同槽写，会错误恢复成 `return nil`。
            assign.targets.iter().all(|target| {
                direct_lvalue_home_slot(target, facts)
                    .is_some_and(|slot| slot.is_none_or(|slot| !protected.contains(&slot)))
            })
        }
        HirStmt::LocalDecl(local_decl) => {
            // 候选拒绝[ProofIncomplete]：local 缺可信 home 时没有区间 clobber 证明。
            // 候选拒绝[SemanticBarrier:EvalOrder]：gap local 写复用 protected home 会覆盖 return 应读取的 nil temp。
            local_decl.bindings.iter().all(|local| {
                facts
                    .trusted_local_home_slot(*local)
                    .is_some_and(|slot| !protected.contains(&slot))
            })
        }
        HirStmt::TableSetList(_) | HirStmt::CallStmt(_) => true,
        // 候选拒绝[ProofIncomplete]：结构化/资源/control gap 当前没有精确 may-write 与路径事实，blanket 停止跨越；应由结构区域 effect summary 替代。
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
        if is_stable_inline_value(value) {
            // 候选拒绝[SemanticBarrier:Lifetime]：额外 use、capture 或 self-rebind 仍要求 producer 存在。
            // 候选拒绝[LayerBoundary]：debug temp 是源码 binding。
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
        // 候选拒绝[ProofIncomplete]：lookup/call/运算等非 binding 值仍缺跨状态准备区间的求值顺序与可变来源证明。
        // 候选拒绝[SemanticBarrier:Lifetime]：额外 use、capture 或 self-rebind 仍要求 producer 存在。
        // 候选拒绝[LayerBoundary]：debug temp 是源码 binding。
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

struct NumericForBindingHeaderAliasPlan {
    replacement: HirExpr,
    chain: Vec<(usize, TempId)>,
}

struct NumericForHeaderProof<'a> {
    scratch: &'a TempUseScratch,
    facts: &'a ProtoPromotionFacts,
    captured_slots_before_stmt: &'a CapturedSlotSnapshots,
    reference_captured_home_slots: Option<BTreeSet<HomeSlotKey>>,
}

fn trusted_reference_captured_home_slots(
    captured: &ReferenceCapturedBindings,
    facts: &ProtoPromotionFacts,
) -> Option<BTreeSet<HomeSlotKey>> {
    captured
        .params
        .iter()
        .map(|param| facts.trusted_param_home_slot(*param))
        .chain(
            captured
                .locals
                .iter()
                .map(|local| facts.trusted_local_home_slot(*local)),
        )
        .chain(
            captured
                .temps
                .iter()
                .map(|temp| facts.trusted_temp_home_slot(*temp)),
        )
        .collect()
}

fn numeric_for_binding_header_alias_plan(
    block: &HirBlock,
    run: std::ops::Range<usize>,
    sink_temp_index: usize,
    live_use_counts: &[usize],
    proof: &NumericForHeaderProof<'_>,
) -> Option<NumericForBindingHeaderAliasPlan> {
    let sink_captured_slots = proof
        .captured_slots_before_stmt
        .get(run.end)
        .expect("capture snapshots must cover the numeric-for sink");
    let Some(reference_captured_home_slots) = &proof.reference_captured_home_slots else {
        // 候选拒绝[ProofIncomplete]：proto 内存在缺可信 home 的引用 capture，无法排除它与 source/chain cell 别名。
        return None;
    };
    let mut chain = Vec::new();
    let mut current_index = sink_temp_index;
    let (replacement, source_home, source_index) = loop {
        let (temp, value) = inline_candidate(&block.stmts[current_index])?;
        if total_use_count(temp, live_use_counts) != 1 || expr_touches_temp(value, temp) {
            // 候选拒绝[SemanticBarrier:Lifetime]：链节点有额外 use 或自写时，删除整条快照链会丢失仍可观察的值或状态更新。
            return None;
        }
        if proof.scratch.has_debug_local_hint(temp) {
            // 候选拒绝[LayerBoundary]：debug temp 是源码 binding，由 locals/source identity owner 保留。
            return None;
        }
        let Some(chain_home) = proof.facts.trusted_temp_home_slot(temp) else {
            // 候选拒绝[ProofIncomplete]：链节点缺可信 primary home 时，无法排除它与 captured/source cell 别名。
            return None;
        };
        if sink_captured_slots.contains(&chain_home) {
            // 候选拒绝[SemanticBarrier:Capture]：sink 前已有 closure 引用捕获链节点 home 时，删除 producer 会让它观察旧值。
            return None;
        }
        let Some(immediate_move_homes) = proof.facts.trusted_immediate_move_write_homes(temp)
        else {
            // 候选拒绝[ProofIncomplete]：链节点缺可信 immediate-MOVE write set 时，无法排除被 HIR 吞掉的写入命中 captured home。
            return None;
        };
        if !immediate_move_homes.is_disjoint(sink_captured_slots) {
            // 候选拒绝[SemanticBarrier:Capture]：相邻透明 MOVE 写入了 sink 前已捕获的 home；删除 producer 会让 closure 继续观察旧 cell 值。
            return None;
        }
        if reference_captured_home_slots.contains(&chain_home)
            || !immediate_move_homes.is_disjoint(reference_captured_home_slots)
        {
            // 候选拒绝[ProofIncomplete]：proto 其它区间捕获了链节点 primary/hidden-MOVE home，但当前缺 interval capture lifetime，不能证明捕获发生在本次 sink 之后。
            return None;
        }
        chain.push((current_index, temp));
        match value {
            HirExpr::ParamRef(param) => {
                let Some(home) = proof.facts.trusted_param_home_slot(*param) else {
                    // 候选拒绝[ProofIncomplete]：参数缺可信 home 时，无法证明状态准备区间没有覆盖其物理 cell。
                    return None;
                };
                break (value.clone(), home, current_index);
            }
            HirExpr::LocalRef(local) => {
                let Some(home) = proof.facts.trusted_local_home_slot(*local) else {
                    // 候选拒绝[ProofIncomplete]：local 缺可信 home 时，无法证明状态准备区间没有覆盖其物理 cell。
                    return None;
                };
                break (value.clone(), home, current_index);
            }
            HirExpr::TempRef(source) => {
                let Some(source_index) = (run.start..current_index).rfind(|index| {
                    inline_candidate(&block.stmts[*index])
                        .is_some_and(|(candidate, _)| candidate == *source)
                }) else {
                    // 候选拒绝[ProofIncomplete]：TempRef 来源位于连续 run 外时，缺少跨 gap 的写入与控制流证明。
                    return None;
                };
                current_index = source_index;
            }
            _ => {
                // 候选拒绝[ProofIncomplete]：Upvalue/lookup/call/运算等来源缺少区间可变性与求值顺序证明，不能作为稳定 binding chain root。
                return None;
            }
        }
    };

    if reference_captured_home_slots.contains(&source_home) {
        // 候选拒绝[ProofIncomplete]：source home 存在 proto-wide 引用 capture，当前缺 interval call/capture may-write；直接放行会破坏 regress_145 的定义点快照。
        return None;
    }

    let chain_indices = chain
        .iter()
        .map(|(index, _)| *index)
        .collect::<BTreeSet<_>>();
    for stmt_index in (source_index + 1)..run.end {
        if chain_indices.contains(&stmt_index) {
            continue;
        }
        let (target, _) = inline_candidate(&block.stmts[stmt_index])
            .expect("numeric-for materialization run must contain only scalar temp definitions");
        let (Some(target_home), Some(immediate_move_homes)) = (
            proof.facts.trusted_temp_home_slot(target),
            proof.facts.trusted_immediate_move_write_homes(target),
        ) else {
            // 候选拒绝[ProofIncomplete]：链外状态写缺可信 primary/immediate-move home 集时，不能证明 source cell 未被覆盖。
            return None;
        };
        if target_home == source_home || immediate_move_homes.contains(&source_home) {
            // 候选拒绝[SemanticBarrier:Lifetime]：链外状态准备写覆盖 source home 时，原 temp 冻结旧值；延后 LocalRef/ParamRef 读取会切到新 epoch。
            return None;
        }
    }

    Some(NumericForBindingHeaderAliasPlan { replacement, chain })
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
        // 候选拒绝[ConvergenceGuard]：capture 快照必须覆盖 open-return sink；缺项表示语句索引失配。
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
            // 候选拒绝[SemanticBarrier:Lifetime]：fixed prefix 非对应唯一 target use 时，删除 alias 会改变其它消费者所见值。
            // 候选拒绝[LayerBoundary]：debug alias 是源码 binding。
            return false;
        }
        let (Some(target_slot), Some(source_slot)) = (
            facts.trusted_temp_home_slot(target),
            facts.trusted_temp_home_slot(*source),
        ) else {
            // 候选拒绝[ProofIncomplete]：alias source/target 缺可信 home，不能证明 open tail setup 不覆盖它们。
            return false;
        };
        if captured_slots.contains(&target_slot)
            || captured_slots.contains(&source_slot)
            || !target_slots.insert(target_slot)
        {
            // 候选拒绝[SemanticBarrier:Capture]：source/target home 已捕获，或多个 target 共享槽时，移动读取会改变 closure/slot 生命周期。
            return false;
        }
        source_slots.insert(source_slot);
    }
    if !target_slots.is_disjoint(&source_slots) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：source/target 同槽会让 fixed return 读到 tail setup 后的新值；见 regress_310。
        return false;
    }

    for stmt in &block.stmts[(run_start + alias_count)..run_end] {
        let Some((target, _)) = inline_candidate(stmt) else {
            return false;
        };
        let Some(slot) = facts.trusted_temp_home_slot(target) else {
            // 候选拒绝[ProofIncomplete]：tail setup 目标缺可信 home，无法证明它不覆盖 fixed source/target。
            return false;
        };
        if target_slots.contains(&slot) || source_slots.contains(&slot) {
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
    // 候选拒绝[LayerBoundary]：debug temp 是源码 binding，由 locals/source identity owner 保留。
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
    // 候选拒绝[ProofIncomplete]：home compaction、缺 prefix/home fact 时不能证明首句 producer 就是 continue 重定位出的 latch prefix；应补 slot epoch/provenance。
    // 候选拒绝[ProofIncomplete]：这里只证明 rootless 标量；local/lookup/call 依赖在 body 后是否稳定需要表达式 read/effect summary。
    // 候选拒绝[LayerBoundary]：debug temp 是源码 binding。
    // 候选拒绝[SemanticBarrier:Lifetime]：非唯一 condition use 仍需要原 temp。
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
        // 候选拒绝[LayerBoundary]：condition 的唯一 use 位于 closure capture；其 source identity 由 locals/promotion owner 消费。
        return false;
    };
    if !site.allows(value, readability) {
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
    // 候选拒绝[LayerBoundary]：debug temp 是源码 binding。
    // 候选拒绝[SemanticBarrier:Lifetime]：self-reference 或额外 use 需要保留状态写入/temp 值。
    if scratch.has_debug_local_hint(temp)
        || expr_touches_temp(value, temp)
        || total_use_count(temp, live_use_counts) != 1
        || collect_expr_temp_uses_summary(&repeat_stmt.cond, scratch).count(temp) != 1
    {
        return false;
    }
    let Some(site) = inline_site_in_repeat_condition(&repeat_stmt.cond, temp) else {
        // 候选拒绝[LayerBoundary]：condition 的唯一 use 位于 closure capture；其 source identity 由 locals/promotion owner 消费。
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
    facts
        .home_slot(temp)
        .is_some_and(|slot| captured_slots.contains(&slot))
}
