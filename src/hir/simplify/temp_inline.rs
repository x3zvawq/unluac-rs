//! 这个文件实现 HIR 的第一批 temp inlining。
//!
//! 我们故意把规则收得很保守：只折叠“单目标 temp 赋值，并且被紧邻下一条简单语句
//! 使用一次”的情况。这样可以先清掉大量机械性的寄存器搬运，又不会把求值顺序、
//! 控制流边界或 debug 语义悄悄改坏。

use crate::hir::common::{
    HirBlock, HirCallExpr, HirExpr, HirLValue, HirProto, HirStmt, HirTableField, TempId,
};

/// 对单个 proto 递归执行局部 temp 折叠。
pub(super) fn inline_temps_in_proto(proto: &mut HirProto) -> bool {
    let proto_temp_count = proto
        .temps
        .iter()
        .map(|temp| temp.index())
        .max()
        .map_or(0, |max_index| max_index + 1);
    let body_temp_count = max_temp_index_in_block(&proto.body).map_or(0, |max_index| max_index + 1);
    let temp_count = proto_temp_count.max(body_temp_count);
    let mut scratch = TempUseScratch::new(temp_count);
    inline_temps_in_block(&mut proto.body, &mut scratch)
}

fn inline_temps_in_block(block: &mut HirBlock, scratch: &mut TempUseScratch) -> bool {
    let mut changed = false;

    for stmt in &mut block.stmts {
        changed |= inline_temps_in_nested_blocks(stmt, scratch);
    }

    // 逆向扫描只需要维护“后缀里每个 temp 当前被用了多少次”以及最近一个保留下来的
    // 语句。这样可以在不反复重扫整个后缀的前提下，保留“只内联到最近简单语句”的约束。
    let mut suffix_use_totals = vec![0; scratch.temp_count()];
    let mut kept_rev = Vec::with_capacity(block.stmts.len());
    let mut next_stmt_state: Option<NextStmtState> = None;

    for stmt in std::mem::take(&mut block.stmts).into_iter().rev() {
        if let Some((temp, value)) = inline_candidate(&stmt)
            && suffix_use_totals.get(temp.index()).copied().unwrap_or(0) == 1
            && let Some(state) = &mut next_stmt_state
            && state.is_simple
            && state.temp_uses.count(temp) == 1
        {
            state.temp_uses.remove_from_totals(&mut suffix_use_totals);
            let next_stmt = kept_rev
                .last_mut()
                .expect("next stmt metadata must track the last kept stmt");
            replace_temp_in_simple_stmt(next_stmt, temp, value);
            state.temp_uses = collect_stmt_temp_uses(next_stmt, scratch);
            state.temp_uses.add_to_totals(&mut suffix_use_totals);
            changed = true;
            continue;
        }

        let stmt_uses = collect_stmt_temp_uses(&stmt, scratch);
        stmt_uses.add_to_totals(&mut suffix_use_totals);
        next_stmt_state = Some(NextStmtState {
            is_simple: is_simple_stmt(&stmt),
            temp_uses: stmt_uses,
        });
        kept_rev.push(stmt);
    }

    kept_rev.reverse();
    block.stmts = kept_rev;

    changed
}

fn inline_temps_in_nested_blocks(stmt: &mut HirStmt, scratch: &mut TempUseScratch) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            let mut changed = inline_temps_in_block(&mut if_stmt.then_block, scratch);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= inline_temps_in_block(else_block, scratch);
            }
            changed
        }
        HirStmt::While(while_stmt) => inline_temps_in_block(&mut while_stmt.body, scratch),
        HirStmt::Repeat(repeat_stmt) => inline_temps_in_block(&mut repeat_stmt.body, scratch),
        HirStmt::NumericFor(numeric_for) => inline_temps_in_block(&mut numeric_for.body, scratch),
        HirStmt::GenericFor(generic_for) => inline_temps_in_block(&mut generic_for.body, scratch),
        HirStmt::Block(block) => inline_temps_in_block(block, scratch),
        HirStmt::Unstructured(unstructured) => {
            inline_temps_in_block(&mut unstructured.body, scratch)
        }
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

fn inline_candidate(stmt: &HirStmt) -> Option<(TempId, &HirExpr)> {
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

fn is_simple_stmt(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_) => true,
        HirStmt::If(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::Block(_)
        | HirStmt::Unstructured(_) => false,
    }
}

struct NextStmtState {
    is_simple: bool,
    temp_uses: TempUseSummary,
}

enum TempUseSummary {
    Empty,
    One(TempId, usize),
    Many(Vec<(TempId, usize)>),
}

impl TempUseSummary {
    fn count(&self, temp: TempId) -> usize {
        match self {
            Self::Empty => 0,
            Self::One(other, count) => usize::from(*other == temp) * *count,
            Self::Many(entries) => entries
                .iter()
                .find_map(|(other, count)| (*other == temp).then_some(*count))
                .unwrap_or(0),
        }
    }

    fn add_to_totals(&self, totals: &mut [usize]) {
        self.for_each(|temp, count| totals[temp.index()] += count);
    }

    fn remove_from_totals(&self, totals: &mut [usize]) {
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

struct TempUseScratch {
    counts: Vec<usize>,
    touched: Vec<TempId>,
}

impl TempUseScratch {
    fn new(temp_count: usize) -> Self {
        Self {
            counts: vec![0; temp_count],
            touched: Vec::new(),
        }
    }

    fn temp_count(&self) -> usize {
        self.counts.len()
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

fn collect_stmt_temp_uses(stmt: &HirStmt, scratch: &mut TempUseScratch) -> TempUseSummary {
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

fn max_temp_index_in_block(block: &HirBlock) -> Option<usize> {
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

fn replace_temp_in_simple_stmt(stmt: &mut HirStmt, temp: TempId, replacement: &HirExpr) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            for value in &mut local_decl.values {
                replace_temp_in_expr(value, temp, replacement);
            }
        }
        HirStmt::Assign(assign) => {
            for target in &mut assign.targets {
                replace_temp_in_lvalue(target, temp, replacement);
            }
            for value in &mut assign.values {
                replace_temp_in_expr(value, temp, replacement);
            }
        }
        HirStmt::TableSetList(set_list) => {
            replace_temp_in_expr(&mut set_list.base, temp, replacement);
            for value in &mut set_list.values {
                replace_temp_in_expr(value, temp, replacement);
            }
            if let Some(expr) = &mut set_list.trailing_multivalue {
                replace_temp_in_expr(expr, temp, replacement);
            }
        }
        HirStmt::ErrNil(err_nil) => {
            replace_temp_in_expr(&mut err_nil.value, temp, replacement);
        }
        HirStmt::CallStmt(call_stmt) => {
            replace_temp_in_call_expr(&mut call_stmt.call, temp, replacement)
        }
        HirStmt::Return(ret) => {
            for value in &mut ret.values {
                replace_temp_in_expr(value, temp, replacement);
            }
        }
        HirStmt::If(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::Block(_)
        | HirStmt::Unstructured(_) => {}
    }
}

fn replace_temp_in_call_expr(call: &mut HirCallExpr, temp: TempId, replacement: &HirExpr) {
    replace_temp_in_expr(&mut call.callee, temp, replacement);
    for arg in &mut call.args {
        replace_temp_in_expr(arg, temp, replacement);
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

fn replace_temp_in_lvalue(lvalue: &mut HirLValue, temp: TempId, replacement: &HirExpr) {
    if let HirLValue::TableAccess(access) = lvalue {
        replace_temp_in_expr(&mut access.base, temp, replacement);
        replace_temp_in_expr(&mut access.key, temp, replacement);
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
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
}

fn replace_temp_in_expr(expr: &mut HirExpr, temp: TempId, replacement: &HirExpr) {
    match expr {
        HirExpr::TempRef(other) if *other == temp => {
            *expr = replacement.clone();
        }
        HirExpr::TableAccess(access) => {
            replace_temp_in_expr(&mut access.base, temp, replacement);
            replace_temp_in_expr(&mut access.key, temp, replacement);
        }
        HirExpr::Unary(unary) => replace_temp_in_expr(&mut unary.expr, temp, replacement),
        HirExpr::Binary(binary) => {
            replace_temp_in_expr(&mut binary.lhs, temp, replacement);
            replace_temp_in_expr(&mut binary.rhs, temp, replacement);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            replace_temp_in_expr(&mut logical.lhs, temp, replacement);
            replace_temp_in_expr(&mut logical.rhs, temp, replacement);
        }
        HirExpr::Decision(decision) => {
            for node in &mut decision.nodes {
                replace_temp_in_expr(&mut node.test, temp, replacement);
                replace_temp_in_decision_target(&mut node.truthy, temp, replacement);
                replace_temp_in_decision_target(&mut node.falsy, temp, replacement);
            }
        }
        HirExpr::Call(call) => replace_temp_in_call_expr(call, temp, replacement),
        HirExpr::TableConstructor(table) => {
            for field in &mut table.fields {
                match field {
                    HirTableField::Array(expr) => replace_temp_in_expr(expr, temp, replacement),
                    HirTableField::Record(field) => {
                        replace_temp_in_table_key(&mut field.key, temp, replacement);
                        replace_temp_in_expr(&mut field.value, temp, replacement);
                    }
                }
            }
            if let Some(expr) = &mut table.trailing_multivalue {
                replace_temp_in_expr(expr, temp, replacement);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &mut closure.captures {
                replace_temp_in_expr(&mut capture.value, temp, replacement);
            }
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
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

fn replace_temp_in_decision_target(
    target: &mut crate::hir::common::HirDecisionTarget,
    temp: TempId,
    replacement: &HirExpr,
) {
    if let crate::hir::common::HirDecisionTarget::Expr(expr) = target {
        replace_temp_in_expr(expr, temp, replacement);
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

fn replace_temp_in_table_key(
    key: &mut crate::hir::common::HirTableKey,
    temp: TempId,
    replacement: &HirExpr,
) {
    if let crate::hir::common::HirTableKey::Expr(expr) = key {
        replace_temp_in_expr(expr, temp, replacement);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{
        HirAssign, HirCallStmt, HirGlobalRef, HirModule, HirProtoRef, HirReturn,
    };

    #[test]
    fn removes_immediate_temp_forwarding_chain() {
        let mut proto = dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::Integer(41)],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(1))],
                    values: vec![HirExpr::TempRef(TempId(0))],
                })),
                HirStmt::CallStmt(Box::new(HirCallStmt {
                    call: HirCallExpr {
                        callee: HirExpr::GlobalRef(HirGlobalRef {
                            name: "print".to_owned(),
                        }),
                        args: vec![HirExpr::TempRef(TempId(1))],
                        multiret: false,
                        method: false,
                    },
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(TempId(0))],
                })),
            ],
        });

        assert!(inline_temps_in_proto(&mut proto));
        assert_eq!(proto.body.stmts.len(), 3);
        assert!(matches!(
            &proto.body.stmts[1],
            HirStmt::CallStmt(call_stmt)
                if matches!(call_stmt.call.args.as_slice(), [HirExpr::TempRef(TempId(0))])
        ));
    }

    #[test]
    fn does_not_inline_across_control_barrier() {
        let mut proto = dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::Integer(1)],
                })),
                HirStmt::Label(Box::new(crate::hir::common::HirLabel {
                    id: crate::hir::common::HirLabelId(0),
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(TempId(0))],
                })),
            ],
        });

        assert!(!inline_temps_in_proto(&mut proto));
        assert_eq!(proto.body.stmts.len(), 3);
    }

    #[test]
    fn collapses_terminal_forwarding_chain_in_single_proto_pass() {
        let mut proto = dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::Integer(7)],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(1))],
                    values: vec![HirExpr::TempRef(TempId(0))],
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(TempId(1))],
                })),
            ],
        });

        assert!(inline_temps_in_proto(&mut proto));
        assert!(matches!(
            proto.body.stmts.as_slice(),
            [HirStmt::Return(ret)] if matches!(ret.values.as_slice(), [HirExpr::Integer(7)])
        ));
    }

    fn dummy_proto(body: HirBlock) -> HirProto {
        HirProto {
            id: HirProtoRef(0),
            source: None,
            line_range: crate::parser::ProtoLineRange {
                defined_start: 0,
                defined_end: 0,
            },
            signature: crate::parser::ProtoSignature {
                num_params: 0,
                is_vararg: false,
                has_vararg_param_reg: false,
                named_vararg_table: false,
            },
            params: Vec::new(),
            locals: Vec::new(),
            upvalues: Vec::new(),
            temps: vec![TempId(0), TempId(1)],
            body,
            children: Vec::new(),
        }
    }

    #[test]
    fn simplify_module_runs_until_fixed_point() {
        let mut module = HirModule {
            entry: HirProtoRef(0),
            protos: vec![dummy_proto(HirBlock {
                stmts: vec![
                    HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(0))],
                        values: vec![HirExpr::Integer(7)],
                    })),
                    HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(1))],
                        values: vec![HirExpr::TempRef(TempId(0))],
                    })),
                    HirStmt::Return(Box::new(HirReturn {
                        values: vec![HirExpr::TempRef(TempId(1))],
                    })),
                ],
            })],
        };

        super::super::simplify_hir(&mut module);

        assert!(matches!(
            &module.protos[0].body.stmts.as_slice(),
            [HirStmt::Return(ret)] if matches!(ret.values.as_slice(), [HirExpr::Integer(7)])
        ));
    }
}
