//! 这个文件负责把 `<close>` 相关的显式 cleanup 重新物化成词法块。
//!
//! Lua 5.4 在 low-IR 里会保留 `tbc rX` / `close from rX` 这类 VM 级语义。结构层能在
//! 一部分 case 里直接把它们吸收进 `while/if/do`，但像 `goto` 反复重入同一块时，
//! HIR 仍可能留下“声明已经恢复、cleanup 还没变回词法边界”的中间形状。这里不去 AST
//! 末端兜底，而是在 HIR 里基于 `<close>` 绑定和对应寄存器槽位，把它们重新收成
//! `HirStmt::Block`，让后面的 AST lowering 自然落成 `do ... end`。一个 `close from rA`
//! 会覆盖所有不小于 A 的 TBC 槽位，区间 owner 会消费词法范围内实际覆盖自己的 cleanup，
//! 避免 fixed-point 每轮重复包块。
//! 重建沿已证明的嵌套区间传递 cleanup owner 集合，一次过滤已有子树；例如外层 r2、
//! 内层 r3 的作用域会共同消费内部的 Close(2)/Close(3)，无需包块后再逐层扫描。
//! 这份集合只描述当前正在物化的词法 owner，不替代 Structure 的 label TBC active-set。
//! 同一 block 的候选共享按需构建的位置事实；cleanup 只扫描语句，binding 活动还包括
//! 声明、循环绑定和 capture 表达式。例如嵌套块内的 Close(r2) 发布在该块的外层语句位置。
//! 直属 label 序列由边界保护、外部跳转与 active-set 连续性查询共用；活跃 origin
//! 仍来自 Structure 发布的 label payload，不从 cleanup 的物理顺序反推。
//! 直属 cleanup 单独发布覆盖阈值，范围查询不逐候选重扫无关语句或高槽 close；
//! 它与嵌套 cleanup 的精确槽位摘要承担不同职责。

use std::{
    cell::OnceCell,
    collections::{BTreeMap, BTreeSet},
};

use crate::graph::{LabelReferenceIndex, PositionIndex};

use crate::hir::common::{
    HirBlock, HirDebugScope, HirExpr, HirLValue, HirLabelId, HirProto, HirStmt, LocalId, TempId,
};
use crate::transformer::InstrRef;

use super::label_refs::label_references_by_stmt;
use super::walk::{HirRewritePass, for_each_nested_block_mut, rewrite_proto};
use crate::hir::visit::{HirVisitor, visit_proto, visit_stmt_structure, visit_stmts};

mod closes;
mod labels;
use closes::DirectCloseIndex;
use labels::DirectLabelIndex;

#[derive(Debug, Clone, PartialEq, Eq)]
struct ScopeInterval {
    start: usize,
    end: usize,
    reg_index: usize,
    covering_close_indices: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ScopeEnd {
    end: usize,
    covering_close_indices: Vec<usize>,
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
    closes: OnceCell<PositionIndex<usize>>,
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
                        // Close(0) 的终结意义由当前 epoch 末尾或 Return 后继决定；
                        // 子树位置摘要只发布非零槽位的精确 cleanup。
                        if let HirStmt::Close(close) = stmt
                            && close.from_reg != 0
                        {
                            positions.record(close.from_reg, index);
                        }
                    });
                }
                positions
            })
            .last_in(&scope.reg_index, scope.start + 2..scope.epoch_end)
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

pub(super) fn materialize_tbc_close_scopes_in_proto(proto: &mut HirProto) -> bool {
    let mut pass = CloseScopePass {
        local_debug_scopes: proto.local_debug_scopes.clone(),
        temp_debug_scopes: proto.temp_debug_scopes.clone(),
        debug_scopes: proto.debug_scopes.clone(),
    };
    rewrite_proto(proto, &mut pass)
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

#[cfg(test)]
fn collect_pending_tbc_boundary_labels_in_block(
    block: &HirBlock,
    labels: &mut BTreeSet<HirLabelId>,
) {
    crate::hir::visit::visit_block(block, &mut PendingTbcBoundaryCollector { labels });
}

struct PendingTbcBoundaryCollector<'a> {
    labels: &'a mut BTreeSet<HirLabelId>,
}

impl HirVisitor for PendingTbcBoundaryCollector<'_> {
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
        let has_pending_close = facts
            .direct_closes()
            .scope_closes(search_start..scope.epoch_end, scope.reg_index)
            .next()
            .is_some();
        if !has_pending_close && facts.last_close(scope).is_none() {
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

struct CloseScopePass {
    local_debug_scopes: Vec<Option<usize>>,
    temp_debug_scopes: Vec<Option<usize>>,
    debug_scopes: Vec<Option<HirDebugScope>>,
}

impl HirRewritePass for CloseScopePass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        materialize_block(
            block,
            &self.local_debug_scopes,
            &self.temp_debug_scopes,
            &self.debug_scopes,
        )
    }
}

fn materialize_block(
    block: &mut HirBlock,
    local_debug_scopes: &[Option<usize>],
    temp_debug_scopes: &[Option<usize>],
    debug_scopes: &[Option<HirDebugScope>],
) -> bool {
    let intervals = collect_scope_intervals(
        &block.stmts,
        local_debug_scopes,
        temp_debug_scopes,
        debug_scopes,
    );
    if intervals.is_empty() {
        return remove_terminal_close_zero(&mut block.stmts);
    }

    let owned_close_indices = intervals
        .iter()
        .flat_map(|interval| interval.covering_close_indices.iter().copied())
        .collect();
    let len = block.stmts.len();
    // 区间已在原始序列上证明；提交只移动节点，递归消费仍按原始下标前进。
    // 无需为父块再次复制已经处理完的子树。
    block.stmts = rebuild_slice(
        &mut std::mem::take(&mut block.stmts).into_iter(),
        0,
        len,
        &intervals,
        &mut 0,
        &mut BTreeSet::new(),
        &owned_close_indices,
    );
    remove_terminal_close_zero(&mut block.stmts);
    true
}

fn remove_terminal_close_zero(stmts: &mut Vec<HirStmt>) -> bool {
    let len = stmts.len();
    let mut retained = 0;
    for index in 0..len {
        let remove = matches!(&stmts[index], HirStmt::Close(close) if close.from_reg == 0)
            && terminal_close_zero_end(stmts, index).is_some();
        if !remove {
            stmts.swap(retained, index);
            retained += 1;
        }
    }
    // 只移动到已读取的位置，判定仍看到原始后继；不在同轮回溯删除连续 Close(0)。
    stmts.truncate(retained);
    retained != len
}

fn collect_scope_intervals(
    stmts: &[HirStmt],
    local_debug_scopes: &[Option<usize>],
    temp_debug_scopes: &[Option<usize>],
    debug_scopes: &[Option<HirDebugScope>],
) -> Vec<ScopeInterval> {
    let facts = ScopeFacts::new(stmts);
    let intervals = facts
        .candidates
        .iter()
        .copied()
        .filter_map(|scope_start| {
            let scope_end = find_scope_end(
                &facts,
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
                start: scope_start.start,
                end: scope_end.end,
                reg_index: scope_start.reg_index,
                covering_close_indices: scope_end.covering_close_indices,
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
        if let Some(binding) = binding_from_expr(&tbc.value)
            .filter(|binding| stmt_defines_tbc_binding(&stmts[start], *binding))
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

fn stmt_defines_tbc_binding(stmt: &HirStmt, binding: ScopeBinding) -> bool {
    match (stmt, binding) {
        (HirStmt::LocalDecl(local_decl), ScopeBinding::Local(local)) => {
            local_decl.bindings.as_slice() == [local]
        }
        (HirStmt::Assign(assign), ScopeBinding::Temp(temp)) => {
            assign.values.exact_result_len() == Some(assign.targets.len())
                && matches!(assign.targets.last(), Some(HirLValue::Temp(last)) if *last == temp)
                && assign
                    .targets
                    .iter()
                    .all(|target| matches!(target, HirLValue::Temp(_)))
        }
        _ => false,
    }
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
    let last_close = facts.last_close(scope);
    let mut last_activity = last_close.map(|index| index + 1);
    let mut covering_close_indices = Vec::new();
    for index in facts
        .direct_closes()
        .scope_closes(start_index..epoch_end, reg_index)
    {
        covering_close_indices.push(index);
        if matches!(epoch_stmts[index], HirStmt::Close(ref close) if close.from_reg == 0) {
            let terminal_return_has_values = matches!(
                epoch_stmts.get(index + 1),
                Some(HirStmt::Return(return_stmt)) if !return_stmt.values.is_empty()
            );
            if !debug_scope_ends_before_return || terminal_return_has_values {
                last_activity = last_activity.max(terminal_close_zero_end(epoch_stmts, index));
            }
        }
    }
    if last_close.is_none() && covering_close_indices.is_empty() {
        return None;
    }
    last_activity = last_activity.max(facts.last_binding_activity(scope).map(|index| index + 1));
    if let Some(&close_idx) = covering_close_indices.last() {
        // composite close 同时终结多个嵌套 TBC scope；所有 interval 会在重建前一次收集，
        // 因此最内层可以消费这条 VM cleanup，外层仍由自己的词法 block 结束来表达。
        let end = label_scope_end.map_or(close_idx + 1, |label_end| label_end.max(close_idx + 1));
        let end = last_activity.map_or(end, |la| la.max(end));
        return Some(ScopeEnd {
            end,
            covering_close_indices,
        });
    }

    // 分支内 cleanup 与 active label 分别提供区间下界；二者同时存在时必须
    // 覆盖较远边界，不能因先发现 cleanup 而丢弃前层已证明的 scope 延续。
    last_activity.max(label_scope_end).map(|end| ScopeEnd {
        end,
        covering_close_indices,
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

fn terminal_close_zero_end(stmts: &[HirStmt], index: usize) -> Option<usize> {
    if index + 1 == stmts.len() {
        Some(stmts.len())
    } else if matches!(stmts.get(index + 1), Some(HirStmt::Return(_))) {
        Some(index + 2)
    } else {
        None
    }
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

    let mut covering_close_indices = scope_end.covering_close_indices;
    for &(index, label) in labels.in_range(end..scope.epoch_end) {
        // 其它 cleanup 只取块内真实 goto 出口，避免误删物理寄存器后续复用的 sibling。
        if label.id == external_target.id
            || label_references.has_goto_in(scope_start..end, label.id)
        {
            covering_close_indices.extend(covering_closes_after_label(
                facts,
                index,
                reg_index,
                scope.epoch_end,
            )?);
        }
    }
    covering_close_indices.sort_unstable();
    covering_close_indices.dedup();
    Ok(Some(ScopeEnd {
        end,
        covering_close_indices,
    }))
}

fn scope_boundary_for_external_label(
    facts: &ScopeFacts<'_>,
    search_start: usize,
    label_index: usize,
    reg_index: usize,
    epoch_end: usize,
) -> Result<ScopeEnd, ()> {
    let closes_after = covering_closes_after_label(facts, label_index, reg_index, epoch_end)?;
    if !closes_after.is_empty() {
        return Ok(ScopeEnd {
            end: label_index,
            covering_close_indices: closes_after,
        });
    }

    // 外部 goto 不能进入新建 local 的作用域；label 前的 cleanup 由词法 owner 消费，
    // 终点截止在最后一条 cleanup 之后，不能把外部目标包进 do block。
    let covering_close_indices: Vec<_> = facts
        .direct_closes()
        .nonzero_closes(search_start..label_index, reg_index)
        .collect();
    Ok(ScopeEnd {
        end: covering_close_indices
            .last()
            .map_or(label_index, |index| index + 1),
        covering_close_indices,
    })
}

fn covering_closes_after_label(
    facts: &ScopeFacts<'_>,
    label_index: usize,
    reg_index: usize,
    epoch_end: usize,
) -> Result<Vec<usize>, ()> {
    let start = label_index + 1;
    let end = facts
        .direct_labels()
        .in_range(start..epoch_end)
        .first()
        .map_or(epoch_end, |(index, _)| *index);
    let mut closes = Vec::new();
    for index in facts.direct_closes().nonzero_closes(start..end, reg_index) {
        if index != start + closes.len() {
            // 候选拒绝[SemanticBarrier:EvalOrder]：`goto L; ::L:: side(); Close r1`
            // 不能改成 goto 离开 `<close>` block；后者会把可观察的 __close 提前到 side()
            // 之前。regress334 的 side-effect/close 日志固定该顺序合同。
            return Err(());
        }
        closes.push(index);
    }
    Ok(closes)
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
    start: usize,
    end: usize,
    intervals: &[ScopeInterval],
    cursor: &mut usize,
    cleanup_owners: &mut BTreeSet<usize>,
    owned_close_indices: &BTreeSet<usize>,
) -> Vec<HirStmt> {
    let mut rewritten = Vec::new();
    let mut index = start;

    while index < end {
        while *cursor < intervals.len() && intervals[*cursor].end <= index {
            *cursor += 1;
        }

        if *cursor < intervals.len() {
            let interval = &intervals[*cursor];
            if interval.start == index && interval.end <= end {
                *cursor += 1;
                let introduced_owner = cleanup_owners.insert(interval.reg_index);
                let inner = rebuild_slice(
                    stmts,
                    interval.start,
                    interval.end,
                    intervals,
                    cursor,
                    cleanup_owners,
                    owned_close_indices,
                );
                if introduced_owner {
                    cleanup_owners.remove(&interval.reg_index);
                }
                rewritten.push(HirStmt::Block(Box::new(HirBlock { stmts: inner })));
                index = interval.end;
                continue;
            }
        }

        let mut stmt = stmts
            .next()
            .expect("validated scope intervals partition the statement slice");
        let close_owned_by_scope = owned_close_indices.contains(&index);
        if !close_owned_by_scope && strip_matching_close_from_stmt(&mut stmt, cleanup_owners) {
            rewritten.push(stmt);
        }
        index += 1;
    }

    rewritten
}

fn strip_matching_close_from_stmt(stmt: &mut HirStmt, cleanup_owners: &BTreeSet<usize>) -> bool {
    if cleanup_owners.is_empty() {
        return true;
    }
    if let HirStmt::Close(close) = stmt {
        return close.from_reg == 0 || !cleanup_owners.contains(&close.from_reg);
    }

    for_each_nested_block_mut(stmt, &mut |block| {
        block
            .stmts
            .retain_mut(|stmt| strip_matching_close_from_stmt(stmt, cleanup_owners));
    });
    true
}

struct BindingActivityCollector {
    positions: PositionIndex<ScopeBinding>,
    owner: usize,
}

impl HirVisitor for BindingActivityCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let locals: &[LocalId] = match stmt {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{HirAssign, HirClose, HirLabel, HirToBeClosed, HirValuePack};

    fn temp_definition(temp: TempId) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(temp)],
            values: HirValuePack::fixed(vec![HirExpr::Nil]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }))
    }

    fn tbc(temp: TempId, origin: InstrRef, reg_index: usize) -> HirStmt {
        HirStmt::ToBeClosed(Box::new(HirToBeClosed {
            origin,
            reg_index,
            value: HirExpr::TempRef(temp),
        }))
    }

    fn label(id: usize, barriers: Vec<InstrRef>) -> HirStmt {
        HirStmt::Label(Box::new(HirLabel {
            id: HirLabelId(id),
            tbc_barriers: barriers,
        }))
    }

    #[test]
    fn pending_boundaries_are_direct_and_epoch_local() {
        let first_origin = InstrRef(10);
        let second_origin = InstrRef(20);
        let block = HirBlock {
            stmts: vec![
                temp_definition(TempId(0)),
                tbc(TempId(0), first_origin, 2),
                label(1, vec![first_origin]),
                label(2, Vec::new()),
                HirStmt::Block(Box::new(HirBlock {
                    stmts: vec![label(3, vec![first_origin])],
                })),
                HirStmt::Close(Box::new(HirClose { from_reg: 2 })),
                temp_definition(TempId(1)),
                tbc(TempId(1), second_origin, 2),
                label(4, vec![second_origin]),
            ],
        };

        let mut boundaries = BTreeSet::new();
        collect_pending_tbc_boundary_labels_in_block(&block, &mut boundaries);

        assert_eq!(boundaries, BTreeSet::from([HirLabelId(1), HirLabelId(2)]));
    }

    #[test]
    fn crossing_resource_component_does_not_reject_disjoint_scope() {
        let interval = |start, end, reg_index| ScopeInterval {
            start,
            end,
            reg_index,
            covering_close_indices: Vec::new(),
        };
        let disjoint = interval(8, 11, 4);

        assert_eq!(
            retain_well_nested_interval_components(vec![
                interval(0, 5, 2),
                interval(2, 7, 3),
                disjoint.clone(),
            ]),
            vec![disjoint]
        );
    }
}
