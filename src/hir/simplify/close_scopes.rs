//! 这个文件负责把 `<close>` 相关的显式 cleanup 重新物化成词法块。
//!
//! Lua 5.4 在 low-IR 里会保留 `tbc rX` / `close from rX` 这类 VM 级语义。结构层能在
//! 一部分 case 里直接把它们吸收进 `while/if/do`，但像 `goto` 反复重入同一块时，
//! HIR 仍可能留下“声明已经恢复、cleanup 还没变回词法边界”的中间形状。这里不去 AST
//! 末端兜底，而是在 HIR 里基于 `<close>` 绑定和对应寄存器槽位，把它们重新收成
//! `HirStmt::Block`，让后面的 AST lowering 自然落成 `do ... end`。一个 `close from rA`
//! 会覆盖所有不小于 A 的 TBC 槽位，区间 owner 会消费词法范围内实际覆盖自己的 cleanup，
//! 避免 fixed-point 每轮重复包块。

use std::collections::BTreeSet;

use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirLabelId, HirProto, HirStmt, LocalId, TempId,
};

use super::label_refs::count_label_references;
use super::visit::{HirVisitor, visit_stmts};
use super::walk::{HirRewritePass, for_each_nested_block_mut, rewrite_proto};

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScopeBinding {
    Local(LocalId),
    Temp(TempId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScopeStart {
    start: usize,
    reg_index: usize,
    binding: ScopeBinding,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct ScopeActivity {
    mentions_binding: bool,
    closes_scope: bool,
}

impl ScopeActivity {
    fn any(self) -> bool {
        self.mentions_binding || self.closes_scope
    }
}

pub(super) fn materialize_tbc_close_scopes_in_proto(proto: &mut HirProto) -> bool {
    rewrite_proto(proto, &mut CloseScopePass)
}

struct CloseScopePass;

impl HirRewritePass for CloseScopePass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        materialize_block(block)
    }
}

fn materialize_block(block: &mut HirBlock) -> bool {
    let Some(rewritten) = rewrite_stmt_slice(&block.stmts) else {
        return false;
    };
    block.stmts = rewritten;
    true
}

fn rewrite_stmt_slice(stmts: &[HirStmt]) -> Option<Vec<HirStmt>> {
    let intervals = collect_scope_intervals(stmts);
    if intervals.is_empty() {
        if !stmts
            .iter()
            .any(|stmt| matches!(stmt, HirStmt::Close(close) if close.from_reg == 0))
        {
            return None;
        }
        return Some(
            stmts
                .iter()
                .filter(|stmt| !matches!(stmt, HirStmt::Close(close) if close.from_reg == 0))
                .cloned()
                .collect(),
        );
    }

    let mut cursor = 0;
    let owned_close_indices = intervals
        .iter()
        .flat_map(|interval| interval.covering_close_indices.iter().copied())
        .collect();
    Some(rebuild_slice(
        stmts,
        0,
        stmts.len(),
        &intervals,
        &mut cursor,
        None,
        &owned_close_indices,
    ))
}

fn collect_scope_intervals(stmts: &[HirStmt]) -> Vec<ScopeInterval> {
    let mut intervals: Vec<_> = (0..stmts.len())
        .filter_map(|index| {
            let scope_start = scope_start(stmts, index)?;
            let scope_end = find_scope_end(
                stmts,
                scope_start.start,
                scope_start.start + 2,
                scope_start.binding,
                scope_start.reg_index,
            )?;
            (scope_start.start < scope_end.end).then_some(ScopeInterval {
                start: scope_start.start,
                end: scope_end.end,
                reg_index: scope_start.reg_index,
                covering_close_indices: scope_end.covering_close_indices,
            })
        })
        .collect();

    intervals.sort_by_key(|interval| (interval.start, interval.end));

    if well_nested_scope_intervals(&intervals) {
        intervals
    } else {
        Vec::new()
    }
}

fn scope_start(stmts: &[HirStmt], index: usize) -> Option<ScopeStart> {
    match (stmts.get(index), stmts.get(index + 1)) {
        (
            Some(HirStmt::LocalDecl(_) | HirStmt::Assign(_)),
            Some(HirStmt::ToBeClosed(to_be_closed)),
        ) => binding_from_expr(&to_be_closed.value).map(|binding| ScopeStart {
            start: index,
            reg_index: to_be_closed.reg_index,
            binding,
        }),
        _ => None,
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
    stmts: &[HirStmt],
    scope_start: usize,
    start_index: usize,
    binding: ScopeBinding,
    reg_index: usize,
) -> Option<ScopeEnd> {
    if let Some(scope_end) =
        externally_entered_scope_end(stmts, scope_start, start_index, reg_index)
    {
        return Some(scope_end);
    }

    let mut saw_close = false;
    let mut last_activity = None;
    // 一个寄存器可能在 scope 内有多次 `close from rX`（如 goto 反复进入的
    // iteration early-exit），真正的词法 scope 结束应是能覆盖到当前寄存器的
    // 最“靠后”的一次 close 事件（可能是精确匹配，也可能是更外层 scope 的
    // 组合 close）。早期的 close 只是 scope 内部的 iteration 边界，把它们
    // 当成 scope 末端会把后续仍在同一 scope 内的表达式错误地挤出块外。
    let mut last_scope_close = None;
    let mut covering_close_indices = Vec::new();

    for (index, stmt) in stmts.iter().enumerate().skip(start_index) {
        if let HirStmt::Close(close) = stmt
            && close.from_reg != 0
            && close.from_reg <= reg_index
        {
            last_scope_close = Some(index);
            covering_close_indices.push(index);
            saw_close = true;
        }

        let activity = scope_activity_in_stmt(stmt, binding, reg_index);
        if activity.any() {
            last_activity = Some(index + 1);
        }
        saw_close |= activity.closes_scope;
    }

    if let Some(close_idx) = last_scope_close {
        // composite close 同时终结多个嵌套 TBC scope；所有 interval 会在重建前一次收集，
        // 因此最内层可以消费这条 VM cleanup，外层仍由自己的词法 block 结束来表达。
        let end = close_idx + 1;
        let end = last_activity.map_or(end, |la| la.max(end));
        // 同一 TBC scope 内可能有多个 goto/分支 cleanup，只消费最终词法区间实际覆盖的
        // close；区间之外的 cleanup 继续由对应 sibling/outer interval 接管。
        covering_close_indices.retain(|index| *index < end);
        return Some(ScopeEnd {
            end,
            covering_close_indices,
        });
    }

    if saw_close {
        last_activity.map(|end| ScopeEnd {
            end,
            covering_close_indices,
        })
    } else {
        None
    }
}

fn externally_entered_scope_end(
    stmts: &[HirStmt],
    scope_start: usize,
    search_start: usize,
    reg_index: usize,
) -> Option<ScopeEnd> {
    // 声明前已经存在的 goto 不能跳进 `<close>` local 的词法块；若目标 block
    // 以匹配的 VM Close 开始，该 label 就是作用域硬边界。其他可消费 Close 只取
    // 块内真实 goto 出口，避免同一物理寄存器后续复用时误删 sibling cleanup。
    let external_targets = goto_targets(&stmts[..scope_start]);
    let (end, external_target) =
        stmts
            .iter()
            .enumerate()
            .skip(search_start)
            .find_map(|(index, stmt)| {
                let HirStmt::Label(label) = stmt else {
                    return None;
                };
                external_targets
                    .contains(&label.id)
                    .then(|| {
                        scope_boundary_for_external_label(stmts, search_start, index, reg_index)
                    })
                    .flatten()
                    .map(|boundary| (boundary, label.id))
            })?;

    let mut exit_targets = goto_targets(&stmts[scope_start..end]);
    exit_targets.insert(external_target);
    let covering_close_indices = stmts
        .iter()
        .enumerate()
        .skip(end)
        .filter_map(|(index, stmt)| match stmt {
            HirStmt::Label(label) if exit_targets.contains(&label.id) => Some(index),
            _ => None,
        })
        .flat_map(|index| covering_closes_after_label(stmts, index, reg_index))
        .collect();
    Some(ScopeEnd {
        end,
        covering_close_indices,
    })
}

fn scope_boundary_for_external_label(
    stmts: &[HirStmt],
    search_start: usize,
    label_index: usize,
    reg_index: usize,
) -> Option<usize> {
    if !covering_closes_after_label(stmts, label_index, reg_index).is_empty() {
        return Some(label_index);
    }

    let cleanup_label = (search_start..label_index)
        .rev()
        .find(|index| matches!(stmts[*index], HirStmt::Label(_)))?;
    let cleanup = &stmts[cleanup_label + 1..label_index];
    (!cleanup.is_empty()
        && cleanup.iter().all(|stmt| {
            matches!(stmt, HirStmt::Close(close) if close.from_reg != 0 && close.from_reg <= reg_index)
        }))
    .then_some(cleanup_label)
}

fn covering_closes_after_label(
    stmts: &[HirStmt],
    label_index: usize,
    reg_index: usize,
) -> Vec<usize> {
    stmts
        .iter()
        .enumerate()
        .skip(label_index + 1)
        .take_while(|(_, stmt)| !matches!(stmt, HirStmt::Label(_)))
        .filter_map(|(index, stmt)| match stmt {
            HirStmt::Close(close) if close.from_reg != 0 && close.from_reg <= reg_index => {
                Some(index)
            }
            _ => None,
        })
        .collect()
}

fn goto_targets(stmts: &[HirStmt]) -> BTreeSet<HirLabelId> {
    count_label_references(stmts).into_keys().collect()
}

fn well_nested_scope_intervals(intervals: &[ScopeInterval]) -> bool {
    let mut stack = Vec::<&ScopeInterval>::new();

    for interval in intervals {
        while let Some(top) = stack.last() {
            if interval.start >= top.end {
                stack.pop();
            } else {
                break;
            }
        }

        if let Some(parent) = stack.last()
            && interval.end > parent.end
        {
            return false;
        }

        stack.push(interval);
    }

    true
}

fn rebuild_slice(
    stmts: &[HirStmt],
    start: usize,
    end: usize,
    intervals: &[ScopeInterval],
    cursor: &mut usize,
    active_scope: Option<&ScopeInterval>,
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
                let inner = rebuild_slice(
                    stmts,
                    interval.start,
                    interval.end,
                    intervals,
                    cursor,
                    Some(interval),
                    owned_close_indices,
                );
                let mut block_stmt = HirStmt::Block(Box::new(HirBlock { stmts: inner }));
                strip_matching_close_from_stmt(
                    &mut block_stmt,
                    active_scope.map(|scope| scope.reg_index),
                );
                rewritten.push(block_stmt);
                index = interval.end;
                continue;
            }
        }

        let mut cloned = stmts[index].clone();
        let close_owned_by_scope = owned_close_indices.contains(&index);
        if !close_owned_by_scope
            && strip_matching_close_from_stmt(
                &mut cloned,
                active_scope.map(|scope| scope.reg_index),
            )
        {
            rewritten.push(cloned);
        }
        index += 1;
    }

    rewritten
}

fn strip_matching_close_from_stmt(stmt: &mut HirStmt, active_scope_reg: Option<usize>) -> bool {
    if let HirStmt::Close(close) = stmt {
        return close.from_reg != 0 && active_scope_reg != Some(close.from_reg);
    }

    for_each_nested_block_mut(stmt, &mut |block| {
        strip_matching_close_from_block(block, active_scope_reg);
    });
    true
}

fn strip_matching_close_from_block(block: &mut HirBlock, active_scope_reg: Option<usize>) {
    block
        .stmts
        .retain_mut(|stmt| strip_matching_close_from_stmt(stmt, active_scope_reg));
}

fn scope_activity_in_stmt(
    stmt: &HirStmt,
    binding: ScopeBinding,
    reg_index: usize,
) -> ScopeActivity {
    let mut collector = ScopeActivityCollector {
        binding,
        reg_index,
        activity: ScopeActivity::default(),
    };
    visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.activity
}

struct ScopeActivityCollector {
    binding: ScopeBinding,
    reg_index: usize,
    activity: ScopeActivity,
}

impl ScopeActivityCollector {
    fn binding_matches_local(&self, local: LocalId) -> bool {
        self.binding == ScopeBinding::Local(local)
    }

    fn binding_matches_temp(&self, temp: TempId) -> bool {
        self.binding == ScopeBinding::Temp(temp)
    }
}

impl HirVisitor for ScopeActivityCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl(local_decl) => {
                self.activity.mentions_binding |= local_decl
                    .bindings
                    .iter()
                    .copied()
                    .any(|local| self.binding_matches_local(local));
            }
            HirStmt::Close(close) => {
                self.activity.closes_scope |= close.from_reg == self.reg_index;
            }
            HirStmt::NumericFor(numeric_for) => {
                self.activity.mentions_binding |= self.binding_matches_local(numeric_for.binding);
            }
            HirStmt::GenericFor(generic_for) => {
                self.activity.mentions_binding |= generic_for
                    .bindings
                    .iter()
                    .copied()
                    .any(|local| self.binding_matches_local(local));
            }
            HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::If(_)
            | HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::Block(_)
            | HirStmt::Unstructured(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::LocalRef(local) => {
                self.activity.mentions_binding |= self.binding_matches_local(*local);
            }
            HirExpr::TempRef(temp) => {
                self.activity.mentions_binding |= self.binding_matches_temp(*temp);
            }
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
            | HirExpr::UpvalueRef(_)
            | HirExpr::GlobalRef(_)
            | HirExpr::VarArg
            | HirExpr::Unresolved(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Unary(_)
            | HirExpr::Binary(_)
            | HirExpr::LogicalAnd(_)
            | HirExpr::LogicalOr(_)
            | HirExpr::Decision(_)
            | HirExpr::Call(_)
            | HirExpr::TableConstructor(_)
            | HirExpr::Closure(_) => {}
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        match lvalue {
            HirLValue::Temp(temp) => {
                self.activity.mentions_binding |= self.binding_matches_temp(*temp);
            }
            HirLValue::Local(local) => {
                self.activity.mentions_binding |= self.binding_matches_local(*local);
            }
            HirLValue::Param(_)
            | HirLValue::Upvalue(_)
            | HirLValue::Global(_)
            | HirLValue::TableAccess(_) => {}
        }
    }
}
