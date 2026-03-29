//! 这个文件负责把 `<close>` 相关的显式 cleanup 重新物化成词法块。
//!
//! Lua 5.4 在 low-IR 里会保留 `tbc rX` / `close from rX` 这类 VM 级语义。结构层能在
//! 一部分 case 里直接把它们吸收进 `while/if/do`，但像 `goto` 反复重入同一块时，
//! HIR 仍可能留下“声明已经恢复、cleanup 还没变回词法边界”的中间形状。这里不去 AST
//! 末端兜底，而是在 HIR 里基于 `<close>` 绑定和对应寄存器槽位，把它们重新收成
//! `HirStmt::Block`，让后面的 AST lowering 自然落成 `do ... end`。

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirProto, HirStmt, LocalId, TempId};

use super::visit::{HirVisitor, visit_stmts};
use super::walk::{HirRewritePass, for_each_nested_block_mut, rewrite_proto};

#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScopeInterval {
    start: usize,
    end: usize,
    reg_index: usize,
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
    let rewritten = rewrite_stmt_slice(&block.stmts);
    if rewritten != block.stmts {
        block.stmts = rewritten;
        return true;
    }
    false
}

fn rewrite_stmt_slice(stmts: &[HirStmt]) -> Vec<HirStmt> {
    let intervals = collect_scope_intervals(stmts);
    if intervals.is_empty() {
        return stmts
            .iter()
            .filter(|stmt| !matches!(stmt, HirStmt::Close(close) if close.from_reg == 0))
            .cloned()
            .collect();
    }

    let mut cursor = 0;
    rebuild_slice(stmts, 0, stmts.len(), &intervals, &mut cursor, None)
}

fn collect_scope_intervals(stmts: &[HirStmt]) -> Vec<ScopeInterval> {
    let mut intervals = Vec::new();
    for index in 0..stmts.len() {
        let Some(scope_start) = scope_start(stmts, index) else {
            continue;
        };
        let Some(end) = find_scope_end(
            stmts,
            scope_start.start + 2,
            scope_start.binding,
            scope_start.reg_index,
        ) else {
            continue;
        };
        if scope_start.start < end {
            intervals.push(ScopeInterval {
                start: scope_start.start,
                end,
                reg_index: scope_start.reg_index,
            });
        }
    }

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
    start_index: usize,
    binding: ScopeBinding,
    reg_index: usize,
) -> Option<usize> {
    let mut saw_close = false;
    let mut last_activity = None;

    for (index, stmt) in stmts.iter().enumerate().skip(start_index) {
        let activity = scope_activity_in_stmt(stmt, binding, reg_index);
        if activity.any() {
            last_activity = Some(index + 1);
        }
        saw_close |= activity.closes_scope;
    }

    if saw_close { last_activity } else { None }
}

fn well_nested_scope_intervals(intervals: &[ScopeInterval]) -> bool {
    let mut stack = Vec::<ScopeInterval>::new();

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

        stack.push(*interval);
    }

    true
}

fn rebuild_slice(
    stmts: &[HirStmt],
    start: usize,
    end: usize,
    intervals: &[ScopeInterval],
    cursor: &mut usize,
    active_scope_reg: Option<usize>,
) -> Vec<HirStmt> {
    let mut rewritten = Vec::new();
    let mut index = start;

    while index < end {
        while *cursor < intervals.len() && intervals[*cursor].end <= index {
            *cursor += 1;
        }

        if *cursor < intervals.len() {
            let interval = intervals[*cursor];
            if interval.start == index && interval.end <= end {
                *cursor += 1;
                let inner = rebuild_slice(
                    stmts,
                    interval.start,
                    interval.end,
                    intervals,
                    cursor,
                    Some(interval.reg_index),
                );
                let mut block_stmt = HirStmt::Block(Box::new(HirBlock { stmts: inner }));
                strip_matching_close_from_stmt(&mut block_stmt, active_scope_reg);
                rewritten.push(block_stmt);
                index = interval.end;
                continue;
            }
        }

        let mut cloned = stmts[index].clone();
        if strip_matching_close_from_stmt(&mut cloned, active_scope_reg) {
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
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {}
        }
    }
}
