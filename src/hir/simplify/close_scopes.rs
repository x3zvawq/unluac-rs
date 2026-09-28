//! 将显式 TBC 清理事件原子地物化为 HIR 词法块。
//!
//! 消费前层的 origin、返回事务与共享 HIR 活跃事实，发布资源作用域和已接管的 cleanup。

use std::{
    cell::OnceCell,
    collections::{BTreeMap, BTreeSet},
};

use crate::graph::{LabelReferenceIndex, PositionIndex};

use crate::hir::common::{
    HirBlock, HirClose, HirDebugScope, HirExpr, HirLValue, HirLabelId, HirProto, HirStmt, LocalId,
    TempId,
};
use crate::transformer::InstrRef;

use super::label_refs::label_references_by_stmt;
use super::walk::{HirRewritePass, for_each_nested_block_mut, rewrite_stmts};
use crate::hir::visit::{HirVisitor, visit_proto, visit_stmt_structure, visit_stmts};

mod closes;
mod labels;
mod lifetimes;
use closes::{CloseSelection, DirectCloseIndex};
use labels::DirectLabelIndex;

#[derive(Debug, Clone, PartialEq, Eq)]
struct ScopeInterval {
    origin: InstrRef,
    start: usize,
    end: usize,
    reg_index: usize,
    close_selections: Vec<CloseSelection>,
    use_function_scope: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ScopeEnd {
    end: usize,
    close_selections: Vec<CloseSelection>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ScopeBinding {
    Local(LocalId),
    Temp(TempId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScopeCandidate {
    start: usize,
    origin: InstrRef,
    reg_index: usize,
    binding: ScopeBinding,
    epoch_end: usize,
}

struct TbcEpoch {
    origin: InstrRef,
    tbc_index: usize,
    end: usize,
}

struct ScopeFacts<'a> {
    stmts: &'a [HirStmt],
    candidates: Vec<ScopeCandidate>,
    labels: OnceCell<LabelReferenceIndex<HirLabelId>>,
    direct_labels: OnceCell<DirectLabelIndex<'a>>,
    direct_closes: OnceCell<DirectCloseIndex<'a>>,
    closes: OnceCell<PositionIndex<InstrRef>>,
    bindings: OnceCell<PositionIndex<ScopeBinding>>,
}

impl<'a> ScopeFacts<'a> {
    fn new(stmts: &'a [HirStmt]) -> Self {
        Self {
            stmts,
            candidates: scope_candidates(stmts),
            labels: OnceCell::new(),
            direct_labels: OnceCell::new(),
            direct_closes: OnceCell::new(),
            closes: OnceCell::new(),
            bindings: OnceCell::new(),
        }
    }

    fn label_references(&self) -> &LabelReferenceIndex<HirLabelId> {
        self.labels
            .get_or_init(|| LabelReferenceIndex::new(&label_references_by_stmt(self.stmts)))
    }

    fn direct_labels(&self) -> &DirectLabelIndex<'a> {
        self.direct_labels
            .get_or_init(|| DirectLabelIndex::new(self.stmts))
    }

    fn direct_closes(&self) -> &DirectCloseIndex<'a> {
        self.direct_closes
            .get_or_init(|| DirectCloseIndex::new(self.stmts))
    }

    fn last_close(&self, scope: ScopeCandidate) -> Option<usize> {
        self.closes
            .get_or_init(|| {
                let mut positions = PositionIndex::default();
                for (index, stmt) in self.stmts.iter().enumerate() {
                    visit_stmt_structure(stmt, &mut |stmt| {
                        if let HirStmt::Close(close) = stmt {
                            for &origin in &close.origins {
                                positions.record(origin, index);
                            }
                        }
                    });
                }
                positions
            })
            .last_in(&scope.origin, scope.start + 2..scope.epoch_end)
    }

    fn last_binding_activity(&self, scope: ScopeCandidate) -> Option<usize> {
        self.bindings
            .get_or_init(|| {
                let mut collector = BindingActivityCollector {
                    positions: PositionIndex::default(),
                    owner: 0,
                };
                for (index, stmt) in self.stmts.iter().enumerate() {
                    collector.owner = index;
                    visit_stmts(std::slice::from_ref(stmt), &mut collector);
                }
                collector.positions
            })
            .last_in(&scope.binding, scope.start + 2..scope.epoch_end)
    }
}

pub(super) fn materialize_tbc_close_scopes_in_proto(
    proto: &mut HirProto,
    safety: crate::hir::expr_safety::HirExprSafety,
) -> bool {
    let mut pass = CloseScopePass {
        safety,
        local_debug_scopes: &proto.local_debug_scopes,
        temp_debug_scopes: &proto.temp_debug_scopes,
        debug_scopes: &proto.debug_scopes,
    };
    let nested_changed = rewrite_stmts(&mut proto.body.stmts, &mut pass);
    let root_changed = materialize_block(
        &mut proto.body,
        &proto.local_debug_scopes,
        &proto.temp_debug_scopes,
        &proto.debug_scopes,
        safety,
        true,
    );
    nested_changed || root_changed
}

/// 返回仍被 close-scope materialization 当作 TBC active-set 边界读取的 label。
///
/// 事实必须按直接 block 与同槽 TBC epoch 收集：active label 决定资源作用域仍在继续，
/// 第一个 inactive label 决定作用域终点，二者在 raw Close 被消费前都不能由 dead-labels
/// 删除。嵌套 block 有自己的词法 owner，不能因为 sibling 存在 TBC/Close 就整棵 proto
/// 一律保护。
pub(super) fn pending_tbc_boundary_labels_in_proto(proto: &HirProto) -> BTreeSet<HirLabelId> {
    let mut labels = BTreeSet::new();
    visit_proto(
        proto,
        &mut PendingTbcBoundaryCollector {
            labels: &mut labels,
        },
    );
    labels
}

struct PendingTbcBoundaryCollector<'a> {
    labels: &'a mut BTreeSet<HirLabelId>,
}

impl HirVisitor<'_> for PendingTbcBoundaryCollector<'_> {
    fn visit_block(&mut self, block: &HirBlock) {
        collect_direct_pending_tbc_boundary_labels(&block.stmts, self.labels);
    }
}

fn collect_direct_pending_tbc_boundary_labels(
    stmts: &[HirStmt],
    labels: &mut BTreeSet<HirLabelId>,
) {
    let facts = ScopeFacts::new(stmts);
    let mut covered_end = 0;
    for &scope in &facts.candidates {
        // 候选起点升序，已覆盖的区间无需再次检查 cleanup 或枚举 label。
        if scope.epoch_end <= covered_end {
            continue;
        }
        let search_start = scope.start + 2;
        if facts.last_close(scope).is_none() {
            continue;
        }

        labels.extend(
            facts
                .direct_labels()
                .in_range(search_start.max(covered_end)..scope.epoch_end)
                .iter()
                .map(|(_, label)| label.id),
        );
        covered_end = scope.epoch_end;
    }
}

struct CloseScopePass<'a> {
    safety: crate::hir::expr_safety::HirExprSafety,
    local_debug_scopes: &'a [Option<usize>],
    temp_debug_scopes: &'a [Option<usize>],
    debug_scopes: &'a [Option<HirDebugScope>],
}

impl HirRewritePass for CloseScopePass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        materialize_block(
            block,
            self.local_debug_scopes,
            self.temp_debug_scopes,
            self.debug_scopes,
            self.safety,
            false,
        )
    }
}

fn materialize_block(
    block: &mut HirBlock,
    local_debug_scopes: &[Option<usize>],
    temp_debug_scopes: &[Option<usize>],
    debug_scopes: &[Option<HirDebugScope>],
    safety: crate::hir::expr_safety::HirExprSafety,
    function_body: bool,
) -> bool {
    let facts = ScopeFacts::new(&block.stmts);
    let mut intervals =
        collect_scope_intervals(&facts, local_debug_scopes, temp_debug_scopes, debug_scopes);
    if !intervals.is_empty() {
        let ends = lifetimes::scope_ends(&block.stmts, &facts.candidates, safety);
        intervals.retain_mut(|interval| {
            let scope = &facts.candidates[facts
                .candidates
                .binary_search_by_key(&interval.start, |scope| scope.start)
                .expect("scope interval retains its candidate")];
            let Some(Some(end)) = ends.get(&scope.origin) else {
                return false;
            };
            if facts
                .last_binding_activity(*scope)
                .is_some_and(|last| last >= *end)
            {
                return false;
            }
            interval.end = interval.end.min(*end);
            true
        });
        intervals = retain_well_nested_interval_components(intervals);
    }
    if intervals.is_empty() {
        return remove_paired_frame_cleanup(&mut block.stmts);
    }

    if function_body
        && let Some(close_index) = block.stmts.len().checked_sub(2)
        && paired_return_cleanup(&block.stmts, close_index)
        && let HirStmt::Close(close) = &block.stmts[close_index]
    {
        // 原 RETURN 清理在结果求值后退出整个函数。已通过活跃域和嵌套验证的
        // 尾区间可由函数本身承载，但 debug 不能另有内层来源终点。
        // 仍保留 interval 的 cleanup 所有权，和普通建块事务一起退休原 origins。
        let returned_origins = close.origins.iter().copied().collect::<BTreeSet<_>>();
        for interval in &mut intervals {
            let scope = &facts.candidates[facts
                .candidates
                .binary_search_by_key(&interval.start, |scope| scope.start)
                .expect("scope interval retains its candidate")];
            interval.use_function_scope = interval.end == block.stmts.len()
                && returned_origins.contains(&interval.origin)
                // 内层 do 中的非空 return 也会延长 cleanup 区间，但 debug 仍给出
                // 早于函数尾的独立来源终点；不能将其冒充函数级资源声明。
                && !binding_debug_scope_ends_before_return(
                    scope.binding,
                    local_debug_scopes,
                    temp_debug_scopes,
                    debug_scopes,
                );
        }
    }

    let owned_close_indices = facts.direct_closes().owned_closes(
        intervals
            .iter()
            .flat_map(|interval| &interval.close_selections),
    );
    let owned_origins = intervals
        .iter()
        .map(|interval| interval.origin)
        .collect::<BTreeSet<_>>();
    let len = block.stmts.len();
    // 区间已在原始序列上证明；提交只移动节点，递归消费仍按原始下标前进。
    // 无需为父块再次复制已经处理完的子树。
    block.stmts = rebuild_slice(
        &mut std::mem::take(&mut block.stmts).into_iter(),
        0..len,
        &intervals,
        &mut 0,
        &mut BTreeSet::new(),
        &owned_close_indices,
        &owned_origins,
    );
    remove_paired_frame_cleanup(&mut block.stmts);
    true
}

fn remove_paired_frame_cleanup(stmts: &mut Vec<HirStmt>) -> bool {
    let len = stmts.len();
    let mut retained = 0;
    for index in 0..len {
        let (prefix, suffix) = stmts.split_at_mut(index + 1);
        let remove = matches!(&prefix[index], HirStmt::Close(close)
            if !matches!(close.kind, crate::transformer::CloseKind::Explicit)
                && consume_cleanup_return_identity(close, suffix.first_mut()));
        if !remove {
            prefix.swap(retained, index);
            retained += 1;
        }
    }
    // 只移动到已读取的位置，判定仍看到原始后继；不会把连续 cleanup 重新拼成返回事务。
    stmts.truncate(retained);
    retained != len
}

fn collect_scope_intervals(
    facts: &ScopeFacts<'_>,
    local_debug_scopes: &[Option<usize>],
    temp_debug_scopes: &[Option<usize>],
    debug_scopes: &[Option<HirDebugScope>],
) -> Vec<ScopeInterval> {
    let intervals = facts
        .candidates
        .iter()
        .copied()
        .filter_map(|scope_start| {
            let scope_end = find_scope_end(
                facts,
                scope_start,
                binding_debug_scope_ends_before_return(
                    scope_start.binding,
                    local_debug_scopes,
                    temp_debug_scopes,
                    debug_scopes,
                ),
            )?;
            assert!(
                scope_start.start < scope_end.end,
                "validated close-scope interval must advance past its declaration"
            );
            Some(ScopeInterval {
                origin: scope_start.origin,
                start: scope_start.start,
                end: scope_end.end,
                reg_index: scope_start.reg_index,
                close_selections: scope_end.close_selections,
                use_function_scope: false,
            })
        })
        .collect();

    retain_well_nested_interval_components(intervals)
}

/// epoch 是候选搜索的上界，不是最终词法终点。逆序继承同槽同 origin 的边界，
/// 遇到不同 origin 才切断；未能配对声明的 TBC 仍参与这个判定。
/// 候选按起点升序发布，保护区间的并集可以只向右扩展。
fn scope_candidates(stmts: &[HirStmt]) -> Vec<ScopeCandidate> {
    let mut next_epochs = BTreeMap::<usize, TbcEpoch>::new();
    let mut candidates = Vec::new();
    for (index, stmt) in stmts.iter().enumerate().rev() {
        let HirStmt::ToBeClosed(tbc) = stmt else {
            continue;
        };
        let epoch_end = next_epochs.get(&tbc.reg_index).map_or(stmts.len(), |next| {
            if next.origin == tbc.origin {
                next.end
            } else {
                next.tbc_index - 1
            }
        });
        next_epochs.insert(
            tbc.reg_index,
            TbcEpoch {
                origin: tbc.origin,
                tbc_index: index,
                end: epoch_end,
            },
        );
        let Some(start) = index.checked_sub(1) else {
            continue;
        };
        if let Some(binding) =
            binding_from_expr(&tbc.value).filter(|_| tbc.declaration(&stmts[start]).is_some())
        {
            candidates.push(ScopeCandidate {
                start,
                origin: tbc.origin,
                reg_index: tbc.reg_index,
                binding,
                epoch_end,
            });
        }
    }
    candidates.reverse();
    candidates
}

fn binding_from_expr(expr: &HirExpr) -> Option<ScopeBinding> {
    match expr {
        HirExpr::LocalRef(local) => Some(ScopeBinding::Local(*local)),
        HirExpr::TempRef(temp) => Some(ScopeBinding::Temp(*temp)),
        _ => None,
    }
}

fn find_scope_end(
    facts: &ScopeFacts<'_>,
    scope: ScopeCandidate,
    debug_scope_ends_before_return: bool,
) -> Option<ScopeEnd> {
    let ScopeCandidate {
        start: scope_start,
        binding: _,
        origin,
        reg_index,
        epoch_end,
    } = scope;
    let start_index = scope_start + 2;
    let epoch_stmts = &facts.stmts[..epoch_end];
    // origin 已退休后，同槽其它资源的残余 Close 不能再次提供候选或外部 label 边界。
    let nested_close = facts.last_close(scope)?;

    match externally_entered_scope_end(facts, scope) {
        Ok(Some(scope_end)) => return Some(scope_end),
        Ok(None) => {}
        Err(()) => return None,
    }

    // 一个寄存器可能在 scope 内有多次 `close from rX`（如 goto 反复进入的
    // iteration early-exit），真正的词法 scope 结束应是能覆盖到当前寄存器的
    // 最“靠后”的一次 close 事件（可能是精确匹配，也可能是更外层 scope 的
    // 组合 close）。早期的 close 只是 scope 内部的 iteration 边界，把它们
    // 当成 scope 末端会把后续仍在同一 scope 内的表达式错误地挤出块外。
    let label_scope_end = facts
        .direct_labels()
        .active_scope_end(start_index..epoch_end, origin)
        .ok()?;
    let selection = CloseSelection::scope(start_index..epoch_end, reg_index);
    let direct_close = facts.direct_closes().last(&selection);
    let mut end = Some(nested_close + 1)
        .max(facts.last_binding_activity(scope).map(|index| index + 1))
        .max(label_scope_end);
    if let Some(index) = direct_close {
        end = end.max(Some(index + 1));
        // 更早的零槽 close 最多延伸到下一条 Return，已被最后 cleanup 的末端覆盖。
        // 只有最后一条可能继续延伸；debug 的空 Return 边界保持原 scope endpoint。
        if matches!(epoch_stmts[index], HirStmt::Close(ref close) if close.from_reg == 0)
            && (!debug_scope_ends_before_return
                || matches!(epoch_stmts.get(index + 1),
                Some(HirStmt::Return(stmt)) if !stmt.values.is_empty()))
        {
            end = end.max(frame_cleanup_end(epoch_stmts, index));
        }
    }
    Some(ScopeEnd {
        end: end.expect("a validated cleanup supplies the scope endpoint"),
        close_selections: direct_close.map(|_| selection).into_iter().collect(),
    })
}

fn binding_debug_scope_ends_before_return(
    binding: ScopeBinding,
    local_debug_scopes: &[Option<usize>],
    temp_debug_scopes: &[Option<usize>],
    debug_scopes: &[Option<HirDebugScope>],
) -> bool {
    let scope = match binding {
        ScopeBinding::Local(local) => local_debug_scopes.get(local.index()),
        ScopeBinding::Temp(temp) => temp_debug_scopes.get(temp.index()),
    }
    .copied()
    .flatten();
    scope
        .and_then(|scope| debug_scopes.get(scope).copied().flatten())
        .is_some_and(|scope| scope.ends_before_return)
}

/// 只验证前层发布的配对身份，不从邻接形状推导原始 RETURN 协议。
fn paired_return_cleanup(stmts: &[HirStmt], index: usize) -> bool {
    matches!((stmts.get(index), stmts.get(index + 1)),
        (Some(HirStmt::Close(close)), Some(HirStmt::Return(ret)))
        if matches!(close.kind, crate::transformer::CloseKind::Return(source)
            if ret.pending_cleanup_source == Some(source)))
}

fn frame_cleanup_end(stmts: &[HirStmt], index: usize) -> Option<usize> {
    matches!(stmts.get(index), Some(HirStmt::Close(close))
        if paired_frame_cleanup(close, stmts.get(index + 1)))
    .then_some(index + 2)
}

fn paired_frame_cleanup(close: &HirClose, next: Option<&HirStmt>) -> bool {
    let source = match close.kind {
        crate::transformer::CloseKind::Return(source) => source,
        crate::transformer::CloseKind::TailCall(source) if close.origins.is_empty() => source,
        _ => return false,
    };
    matches!(next, Some(HirStmt::Return(ret)) if ret.pending_cleanup_source == Some(source))
}

/// 删除 cleanup 的原子提交入口；next 必须来自改写前同一直属 block 的真实后继。
fn consume_cleanup_return_identity(close: &HirClose, next: Option<&mut HirStmt>) -> bool {
    if matches!(close.kind, crate::transformer::CloseKind::Explicit) {
        return true;
    }
    if !paired_frame_cleanup(close, next.as_deref()) {
        return false;
    }
    let Some(HirStmt::Return(ret)) = next else {
        unreachable!("validated frame cleanup has its original return successor");
    };
    ret.pending_cleanup_source = None;
    true
}

fn externally_entered_scope_end(
    facts: &ScopeFacts<'_>,
    scope: ScopeCandidate,
) -> Result<Option<ScopeEnd>, ()> {
    let scope_start = scope.start;
    let search_start = scope_start + 2;
    let reg_index = scope.reg_index;
    let label_references = facts.label_references();
    let labels = facts.direct_labels();
    // 声明前的 goto 不能跳进新建的 <close> 作用域；目标边界仍由真实 cleanup 布局决定。
    let Some(&(label_index, external_target)) = labels
        .in_range(search_start..scope.epoch_end)
        .iter()
        .find(|(_, label)| label_references.has_goto_before(scope_start, label.id))
    else {
        return Ok(None);
    };
    let scope_end = scope_boundary_for_external_label(
        facts,
        search_start,
        label_index,
        reg_index,
        scope.epoch_end,
    )?;
    let end = scope_end.end;

    let mut close_selections = scope_end.close_selections;
    for &(index, label) in labels.in_range(end..scope.epoch_end) {
        // 其它 cleanup 只取块内真实 goto 出口，避免误删物理寄存器后续复用的 sibling。
        // 首个目标的连续 cleanup 已由 scope_boundary_for_external_label 验证并收录。
        if index != label_index
            && (label.id == external_target.id
                || label_references.has_goto_in(scope_start..end, label.id))
        {
            close_selections.extend(covering_closes_after_label(
                facts,
                index,
                reg_index,
                scope.epoch_end,
            )?);
        }
    }
    Ok(Some(ScopeEnd {
        end,
        close_selections,
    }))
}

fn scope_boundary_for_external_label(
    facts: &ScopeFacts<'_>,
    search_start: usize,
    label_index: usize,
    reg_index: usize,
    epoch_end: usize,
) -> Result<ScopeEnd, ()> {
    if let Some(selection) = covering_closes_after_label(facts, label_index, reg_index, epoch_end)?
    {
        return Ok(ScopeEnd {
            end: label_index,
            close_selections: vec![selection],
        });
    }

    // 外部 goto 不能进入新建 local 的作用域；label 前的 cleanup 由词法 owner 消费，
    // 终点截止在最后一条 cleanup 之后，不能把外部目标包进 do block。
    let selection = CloseSelection::explicit(search_start..label_index, reg_index);
    let last = facts.direct_closes().last(&selection);
    Ok(ScopeEnd {
        end: last.map_or(label_index, |index| index + 1),
        close_selections: last.map(|_| selection).into_iter().collect(),
    })
}

fn covering_closes_after_label(
    facts: &ScopeFacts<'_>,
    label_index: usize,
    reg_index: usize,
    epoch_end: usize,
) -> Result<Option<CloseSelection>, ()> {
    let start = label_index + 1;
    let end = facts
        .direct_labels()
        .in_range(start..epoch_end)
        .first()
        .map_or(epoch_end, |(index, _)| *index);
    // 候选拒绝[SemanticBarrier:EvalOrder]：`goto L; ::L:: side(); Close r1`
    // 不能改成 goto 离开 `<close>` block；后者会把可观察的 __close 提前到 side() 之前。
    facts
        .direct_closes()
        .contiguous_explicit(start..end, reg_index)
}

fn retain_well_nested_interval_components(mut intervals: Vec<ScopeInterval>) -> Vec<ScopeInterval> {
    let mut retained = 0;
    let mut component_start = 0;
    let mut covered_end = 0;
    let mut nested_ends = Vec::new();
    let mut valid_component = true;
    for index in 0..intervals.len() {
        let start = intervals[index].start;
        let end = intervals[index].end;
        if start >= covered_end {
            component_start = retained;
            nested_ends.clear();
            valid_component = true;
        }
        // 被拒绝分量的后续区间仍可扩大连通范围，不能提前恢复接受。
        covered_end = covered_end.max(end);
        if !valid_component {
            continue;
        }
        while nested_ends.last().is_some_and(|&end| end <= start) {
            nested_ends.pop();
        }
        if nested_ends
            .last()
            .is_some_and(|&parent_end| end > parent_end)
        {
            // 候选拒绝[SemanticBarrier:Resource]：`TBC a; TBC b; Close(a); use(b); Close(b)`
            // 的交叉资源区间无法表示成嵌套 Lua block；强行合并会把 a 延寿到 use(b) 之后，
            // 强行嵌套则会在 a 之前关闭 b。屏障只覆盖这个重叠连通分量；后续不相交
            // 的资源区间仍可独立物化。
            retained = component_start;
            valid_component = false;
            continue;
        }
        nested_ends.push(end);
        // 只移动到已读位置；交叉时回退前缀长度，整个分量共同接受或拒绝。
        intervals.swap(retained, index);
        retained += 1;
    }
    intervals.truncate(retained);
    intervals
}

fn rebuild_slice(
    stmts: &mut std::vec::IntoIter<HirStmt>,
    range: std::ops::Range<usize>,
    intervals: &[ScopeInterval],
    cursor: &mut usize,
    cleanup_owners: &mut BTreeSet<InstrRef>,
    owned_close_indices: &BTreeSet<usize>,
    owned_origins: &BTreeSet<InstrRef>,
) -> Vec<HirStmt> {
    let mut rewritten = Vec::new();
    let mut index = range.start;

    while index < range.end {
        while *cursor < intervals.len() && intervals[*cursor].end <= index {
            *cursor += 1;
        }

        if *cursor < intervals.len() {
            let interval = &intervals[*cursor];
            if interval.start == index && interval.end <= range.end {
                *cursor += 1;
                let introduced_owner = cleanup_owners.insert(interval.origin);
                let inner = rebuild_slice(
                    stmts,
                    interval.start..interval.end,
                    intervals,
                    cursor,
                    cleanup_owners,
                    owned_close_indices,
                    owned_origins,
                );
                if introduced_owner {
                    cleanup_owners.remove(&interval.origin);
                }
                if interval.use_function_scope {
                    rewritten.extend(inner);
                } else {
                    rewritten.push(HirStmt::Block(Box::new(HirBlock { stmts: inner })));
                }
                index = interval.end;
                continue;
            }
        }

        let mut stmt = stmts
            .next()
            .expect("validated scope intervals partition the statement slice");
        let retained = if owned_close_indices.contains(&index)
            && let HirStmt::Close(close) = &mut stmt
        {
            retain_unowned_close(close, stmts.as_mut_slice().first_mut(), owned_origins)
        } else {
            strip_matching_close_from_stmt(
                &mut stmt,
                stmts.as_mut_slice().first_mut(),
                cleanup_owners,
            )
        };
        if retained {
            rewritten.push(stmt);
        }
        index += 1;
    }

    rewritten
}

/// 同一 Close 可以分步交给嵌套词法 owner；提交 scope 时一并退休其 origins。
/// 例如 inner 先结束、随后 outer 退出的组合 Close，只剩 outer 待处理；保留已消费的
/// inner 身份会使后续事务永远无法完成。Return 身份仅在整条 cleanup 被消费时退休。
fn retain_unowned_close(
    close: &mut HirClose,
    next: Option<&mut HirStmt>,
    owners: &BTreeSet<InstrRef>,
) -> bool {
    if close.origins.is_empty()
        || (!matches!(close.kind, crate::transformer::CloseKind::Explicit)
            && !paired_frame_cleanup(close, next.as_deref()))
    {
        return true;
    }
    close.origins.retain(|origin| !owners.contains(origin));
    !close.origins.is_empty() || !consume_cleanup_return_identity(close, next)
}

fn strip_matching_close_from_stmt(
    stmt: &mut HirStmt,
    next: Option<&mut HirStmt>,
    cleanup_owners: &BTreeSet<InstrRef>,
) -> bool {
    if cleanup_owners.is_empty() {
        return true;
    }
    if let HirStmt::Close(close) = stmt {
        return retain_unowned_close(close, next, cleanup_owners);
    }

    for_each_nested_block_mut(stmt, &mut |block| {
        let mut retained = 0;
        for index in 0..block.stmts.len() {
            let (prefix, suffix) = block.stmts.split_at_mut(index + 1);
            if strip_matching_close_from_stmt(
                &mut prefix[index],
                suffix.first_mut(),
                cleanup_owners,
            ) {
                prefix.swap(retained, index);
                retained += 1;
            }
        }
        block.stmts.truncate(retained);
    });
    true
}

struct BindingActivityCollector {
    positions: PositionIndex<ScopeBinding>,
    owner: usize,
}

impl HirVisitor<'_> for BindingActivityCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let locals: &[LocalId] = match stmt {
            HirStmt::LocalRootRelease(_) => &[],
            HirStmt::LocalDecl(decl) => &decl.bindings,
            HirStmt::NumericFor(for_stmt) => std::slice::from_ref(&for_stmt.binding),
            HirStmt::GenericFor(for_stmt) => &for_stmt.bindings,
            HirStmt::Assign(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::If(_)
            | HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::Block(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => &[],
        };
        for &local in locals {
            self.positions
                .record(ScopeBinding::Local(local), self.owner);
        }
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        if let Some(binding) = binding_from_expr(expr) {
            self.positions.record(binding, self.owner);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        let binding = match lvalue {
            HirLValue::Temp(temp) => ScopeBinding::Temp(*temp),
            HirLValue::Local(local) => ScopeBinding::Local(*local),
            HirLValue::Param(_)
            | HirLValue::Upvalue(_)
            | HirLValue::Global(_)
            | HirLValue::TableAccess(_) => return,
        };
        self.positions.record(binding, self.owner);
    }
}
