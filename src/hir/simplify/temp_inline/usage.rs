//! 这个子模块负责 temp-inline pass 的候选识别和使用计数摘要。
//!
//! 它依赖 HIR 当前 stmt 序列，只回答“这一句是不是 `temp = expr` 候选”以及下一句对 temp
//! 的使用次数，不会在这里改写任何节点。
//! 例如：`t0 = a.b` 若下一句只用一次 `t0`，这里会把它标成可继续审查的内联候选。

use super::*;

pub(super) fn inline_candidate(stmt: &HirStmt) -> Option<(TempId, &HirExpr)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(temp)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };

    Some((*temp, value))
}

pub(super) struct NextStmtState {
    pub temp_uses: TempUseSummary,
}

pub(super) enum TempUseSummary {
    Empty,
    One(TempId, usize),
    Many(Vec<(TempId, usize)>),
}

impl TempUseSummary {
    pub(super) fn count(&self, temp: TempId) -> usize {
        match self {
            Self::Empty => 0,
            Self::One(other, count) => usize::from(*other == temp) * *count,
            Self::Many(entries) => entries
                .iter()
                .find_map(|(other, count)| (*other == temp).then_some(*count))
                .unwrap_or(0),
        }
    }

    pub(super) fn add_to_totals(&self, totals: &mut [usize]) {
        self.for_each(|temp, count| totals[temp.index()] += count);
    }

    pub(super) fn remove_from_totals(&self, totals: &mut [usize]) {
        self.for_each(|temp, count| {
            debug_assert!(totals[temp.index()] >= count);
            totals[temp.index()] -= count;
        });
    }

    fn for_each(&self, mut visitor: impl FnMut(TempId, usize)) {
        match self {
            Self::Empty => {}
            Self::One(temp, count) => visitor(*temp, *count),
            Self::Many(entries) => {
                for &(temp, count) in entries {
                    visitor(temp, count);
                }
            }
        }
    }
}

pub(super) struct TempUseScratch {
    temp_debug_hints: Vec<bool>,
    counts: Vec<usize>,
    touched: Vec<TempId>,
}

impl TempUseScratch {
    pub(super) fn new(proto: &HirProto, temp_count: usize) -> Self {
        let mut temp_debug_hints = vec![false; temp_count];
        for (index, hint) in proto.temp_debug_locals.iter().enumerate().take(temp_count) {
            temp_debug_hints[index] = hint.is_some();
        }
        Self {
            temp_debug_hints,
            counts: vec![0; temp_count],
            touched: Vec::new(),
        }
    }

    pub(super) fn temp_count(&self) -> usize {
        self.counts.len()
    }

    pub(super) fn has_debug_local_hint(&self, temp: TempId) -> bool {
        self.temp_debug_hints
            .get(temp.index())
            .copied()
            .unwrap_or(false)
    }

    fn note_temp(&mut self, temp: TempId) {
        let slot = &mut self.counts[temp.index()];
        if *slot == 0 {
            self.touched.push(temp);
        }
        *slot += 1;
    }

    fn finish_summary(&mut self) -> TempUseSummary {
        match self.touched.len() {
            0 => TempUseSummary::Empty,
            1 => {
                let temp = self
                    .touched
                    .pop()
                    .expect("single touched temp branch must contain exactly one item");
                let count = std::mem::take(&mut self.counts[temp.index()]);
                TempUseSummary::One(temp, count)
            }
            _ => {
                let mut entries = Vec::with_capacity(self.touched.len());
                for temp in self.touched.drain(..) {
                    let count = std::mem::take(&mut self.counts[temp.index()]);
                    entries.push((temp, count));
                }
                TempUseSummary::Many(entries)
            }
        }
    }
}

pub(super) fn collect_stmt_temp_uses(
    stmt: &HirStmt,
    scratch: &mut TempUseScratch,
) -> TempUseSummary {
    collect_stmt_temp_uses_into(stmt, scratch);
    scratch.finish_summary()
}

fn collect_stmt_temp_uses_into(stmt: &HirStmt, scratch: &mut TempUseScratch) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_expr_temp_uses(value, scratch);
            }
        }
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_temp_uses(target, scratch);
            }
            for value in &assign.values {
                collect_expr_temp_uses(value, scratch);
            }
        }
        HirStmt::TableSetList(set_list) => {
            collect_expr_temp_uses(&set_list.base, scratch);
            for value in &set_list.values {
                collect_expr_temp_uses(value, scratch);
            }
            if let Some(expr) = &set_list.trailing_multivalue {
                collect_expr_temp_uses(expr, scratch);
            }
        }
        HirStmt::ErrNil(err_nil) => {
            collect_expr_temp_uses(&err_nil.value, scratch);
        }
        HirStmt::ToBeClosed(to_be_closed) => {
            collect_expr_temp_uses(&to_be_closed.value, scratch);
        }
        HirStmt::CallStmt(call_stmt) => collect_call_temp_uses(&call_stmt.call, scratch),
        HirStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_temp_uses(value, scratch);
            }
        }
        HirStmt::If(if_stmt) => {
            collect_expr_temp_uses(&if_stmt.cond, scratch);
            collect_block_temp_uses(&if_stmt.then_block, scratch);
            if let Some(else_block) = &if_stmt.else_block {
                collect_block_temp_uses(else_block, scratch);
            }
        }
        HirStmt::While(while_stmt) => {
            collect_expr_temp_uses(&while_stmt.cond, scratch);
            collect_block_temp_uses(&while_stmt.body, scratch);
        }
        HirStmt::Repeat(repeat_stmt) => {
            collect_block_temp_uses(&repeat_stmt.body, scratch);
            collect_expr_temp_uses(&repeat_stmt.cond, scratch);
        }
        HirStmt::NumericFor(numeric_for) => {
            collect_expr_temp_uses(&numeric_for.start, scratch);
            collect_expr_temp_uses(&numeric_for.limit, scratch);
            collect_expr_temp_uses(&numeric_for.step, scratch);
            collect_block_temp_uses(&numeric_for.body, scratch);
        }
        HirStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_expr_temp_uses(expr, scratch);
            }
            collect_block_temp_uses(&generic_for.body, scratch);
        }
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
        HirStmt::Block(block) => collect_block_temp_uses(block, scratch),
        HirStmt::Unstructured(unstructured) => collect_block_temp_uses(&unstructured.body, scratch),
    }
}

fn collect_block_temp_uses(block: &HirBlock, scratch: &mut TempUseScratch) {
    for stmt in &block.stmts {
        collect_stmt_temp_uses_into(stmt, scratch);
    }
}

fn collect_call_temp_uses(call: &HirCallExpr, scratch: &mut TempUseScratch) {
    collect_expr_temp_uses(&call.callee, scratch);
    for arg in &call.args {
        collect_expr_temp_uses(arg, scratch);
    }
}

fn collect_lvalue_temp_uses(lvalue: &HirLValue, scratch: &mut TempUseScratch) {
    match lvalue {
        HirLValue::Temp(_) | HirLValue::Local(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => {
        }
        HirLValue::TableAccess(access) => {
            collect_expr_temp_uses(&access.base, scratch);
            collect_expr_temp_uses(&access.key, scratch);
        }
    }
}

fn collect_expr_temp_uses(expr: &HirExpr, scratch: &mut TempUseScratch) {
    match expr {
        HirExpr::TempRef(temp) => scratch.note_temp(*temp),
        HirExpr::TableAccess(access) => {
            collect_expr_temp_uses(&access.base, scratch);
            collect_expr_temp_uses(&access.key, scratch);
        }
        HirExpr::Unary(unary) => collect_expr_temp_uses(&unary.expr, scratch),
        HirExpr::Binary(binary) => {
            collect_expr_temp_uses(&binary.lhs, scratch);
            collect_expr_temp_uses(&binary.rhs, scratch);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_expr_temp_uses(&logical.lhs, scratch);
            collect_expr_temp_uses(&logical.rhs, scratch);
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                collect_expr_temp_uses(&node.test, scratch);
                collect_decision_target_temp_uses(&node.truthy, scratch);
                collect_decision_target_temp_uses(&node.falsy, scratch);
            }
        }
        HirExpr::Call(call) => collect_call_temp_uses(call, scratch),
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(expr) => collect_expr_temp_uses(expr, scratch),
                    HirTableField::Record(field) => {
                        collect_table_key_temp_uses(&field.key, scratch);
                        collect_expr_temp_uses(&field.value, scratch);
                    }
                }
            }
            if let Some(expr) = &table.trailing_multivalue {
                collect_expr_temp_uses(expr, scratch);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                collect_expr_temp_uses(&capture.value, scratch);
            }
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
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
}

fn collect_decision_target_temp_uses(
    target: &crate::hir::common::HirDecisionTarget,
    scratch: &mut TempUseScratch,
) {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => collect_expr_temp_uses(expr, scratch),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => {}
    }
}

fn collect_table_key_temp_uses(
    key: &crate::hir::common::HirTableKey,
    scratch: &mut TempUseScratch,
) {
    match key {
        crate::hir::common::HirTableKey::Name(_) => {}
        crate::hir::common::HirTableKey::Expr(expr) => collect_expr_temp_uses(expr, scratch),
    }
}

pub(super) fn max_temp_index_in_block(block: &HirBlock) -> Option<usize> {
    block.stmts.iter().filter_map(max_temp_index_in_stmt).max()
}

fn max_temp_index_in_stmt(stmt: &HirStmt) -> Option<usize> {
    match stmt {
        HirStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .filter_map(max_temp_index_in_expr)
            .max(),
        HirStmt::Assign(assign) => assign
            .targets
            .iter()
            .filter_map(max_temp_index_in_lvalue)
            .chain(assign.values.iter().filter_map(max_temp_index_in_expr))
            .max(),
        HirStmt::TableSetList(set_list) => std::iter::once(max_temp_index_in_expr(&set_list.base))
            .chain(set_list.values.iter().map(max_temp_index_in_expr))
            .chain(
                set_list
                    .trailing_multivalue
                    .iter()
                    .map(max_temp_index_in_expr),
            )
            .flatten()
            .max(),
        HirStmt::ErrNil(err_nil) => max_temp_index_in_expr(&err_nil.value),
        HirStmt::ToBeClosed(to_be_closed) => max_temp_index_in_expr(&to_be_closed.value),
        HirStmt::CallStmt(call_stmt) => max_temp_index_in_call(&call_stmt.call),
        HirStmt::Return(ret) => ret.values.iter().filter_map(max_temp_index_in_expr).max(),
        HirStmt::If(if_stmt) => std::iter::once(max_temp_index_in_expr(&if_stmt.cond))
            .chain(std::iter::once(max_temp_index_in_block(
                &if_stmt.then_block,
            )))
            .chain(if_stmt.else_block.iter().map(max_temp_index_in_block))
            .flatten()
            .max(),
        HirStmt::While(while_stmt) => std::iter::once(max_temp_index_in_expr(&while_stmt.cond))
            .chain(std::iter::once(max_temp_index_in_block(&while_stmt.body)))
            .flatten()
            .max(),
        HirStmt::Repeat(repeat_stmt) => std::iter::once(max_temp_index_in_block(&repeat_stmt.body))
            .chain(std::iter::once(max_temp_index_in_expr(&repeat_stmt.cond)))
            .flatten()
            .max(),
        HirStmt::NumericFor(numeric_for) => {
            std::iter::once(max_temp_index_in_expr(&numeric_for.start))
                .chain(std::iter::once(max_temp_index_in_expr(&numeric_for.limit)))
                .chain(std::iter::once(max_temp_index_in_expr(&numeric_for.step)))
                .chain(std::iter::once(max_temp_index_in_block(&numeric_for.body)))
                .flatten()
                .max()
        }
        HirStmt::GenericFor(generic_for) => generic_for
            .iterator
            .iter()
            .filter_map(max_temp_index_in_expr)
            .chain(std::iter::once(max_temp_index_in_block(&generic_for.body)).flatten())
            .max(),
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => None,
        HirStmt::Block(block) => max_temp_index_in_block(block),
        HirStmt::Unstructured(unstructured) => max_temp_index_in_block(&unstructured.body),
    }
}

fn max_temp_index_in_call(call: &HirCallExpr) -> Option<usize> {
    std::iter::once(max_temp_index_in_expr(&call.callee))
        .chain(call.args.iter().map(max_temp_index_in_expr))
        .flatten()
        .max()
}

fn max_temp_index_in_lvalue(lvalue: &HirLValue) -> Option<usize> {
    match lvalue {
        HirLValue::Temp(temp) => Some(temp.index()),
        HirLValue::TableAccess(access) => std::iter::once(max_temp_index_in_expr(&access.base))
            .chain(std::iter::once(max_temp_index_in_expr(&access.key)))
            .flatten()
            .max(),
        HirLValue::Local(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => None,
    }
}

fn max_temp_index_in_expr(expr: &HirExpr) -> Option<usize> {
    match expr {
        HirExpr::TempRef(temp) => Some(temp.index()),
        HirExpr::TableAccess(access) => std::iter::once(max_temp_index_in_expr(&access.base))
            .chain(std::iter::once(max_temp_index_in_expr(&access.key)))
            .flatten()
            .max(),
        HirExpr::Unary(unary) => max_temp_index_in_expr(&unary.expr),
        HirExpr::Binary(binary) => std::iter::once(max_temp_index_in_expr(&binary.lhs))
            .chain(std::iter::once(max_temp_index_in_expr(&binary.rhs)))
            .flatten()
            .max(),
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            std::iter::once(max_temp_index_in_expr(&logical.lhs))
                .chain(std::iter::once(max_temp_index_in_expr(&logical.rhs)))
                .flatten()
                .max()
        }
        HirExpr::Decision(decision) => decision
            .nodes
            .iter()
            .flat_map(|node| {
                [
                    max_temp_index_in_expr(&node.test),
                    max_temp_index_in_decision_target(&node.truthy),
                    max_temp_index_in_decision_target(&node.falsy),
                ]
            })
            .flatten()
            .max(),
        HirExpr::Call(call) => max_temp_index_in_call(call),
        HirExpr::TableConstructor(table) => table
            .fields
            .iter()
            .flat_map(|field| match field {
                HirTableField::Array(expr) => [max_temp_index_in_expr(expr), None],
                HirTableField::Record(field) => [
                    max_temp_index_in_table_key(&field.key),
                    max_temp_index_in_expr(&field.value),
                ],
            })
            .chain(table.trailing_multivalue.iter().map(max_temp_index_in_expr))
            .flatten()
            .max(),
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .filter_map(|capture| max_temp_index_in_expr(&capture.value))
            .max(),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => None,
    }
}

fn max_temp_index_in_decision_target(
    target: &crate::hir::common::HirDecisionTarget,
) -> Option<usize> {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => max_temp_index_in_expr(expr),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => None,
    }
}

fn max_temp_index_in_table_key(key: &crate::hir::common::HirTableKey) -> Option<usize> {
    match key {
        crate::hir::common::HirTableKey::Name(_) => None,
        crate::hir::common::HirTableKey::Expr(expr) => max_temp_index_in_expr(expr),
    }
}
