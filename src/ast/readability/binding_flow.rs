//! 这个文件集中承载 AST readability 里的局部 binding 流分析工具。
//!
//! 这些 pass 经常需要回答同一类问题：
//! - 某个 binding 在一段语句里还会不会再被读取？
//! - 某个语句实际提到了哪些 binding（包括赋值目标这种 mention，而不只是读取）？
//! - 某个语句/块会不会提前引用一组待下沉的 hoisted local？
//! - 某个 binding 在当前函数体里一共被用了几次？
//!
//! 这里故意把“当前函数体”作为边界，不继续钻进嵌套函数体。
//! 原因是 AST 的 `LocalId` / `SyntheticLocalId` 都是按函数局部编号的，跨闭包继续统计
//! 很容易把不同函数里碰巧同号的 binding 错算成同一个变量。
//! 但 `FunctionExpr.captured_bindings` 是闭包创建时对当前词法 binding 的显式引用，
//! 必须按当前语句的一次使用统计，否则后续 pass 可能误删仍被闭包持有的局部。

use std::collections::{BTreeMap, BTreeSet};

use super::super::common::{
    AstBindingRef, AstBlock, AstCallExpr, AstCallKind, AstExpr, AstLValue, AstLocalBinding,
    AstMethodCallExpr, AstNameRef, AstStmt, AstTableField, AstTableKey,
};
use super::binding_ref::binding_from_name_ref;

pub(super) use super::binding_ref::name_matches_binding;

#[derive(Clone, Copy)]
enum BindingUseScope {
    CurrentFunctionOnly,
    IncludingNestedFunctions,
}

#[derive(Debug, Default, Clone)]
pub(super) struct BindingUseIndex {
    stmt_len: usize,
    stmt_counts: Vec<BTreeMap<AstBindingRef, usize>>,
    suffix_counts: BTreeMap<AstBindingRef, BindingUseSuffixCounts>,
}

#[derive(Debug, Clone)]
struct BindingUseSuffixCounts {
    stmt_indices: Vec<usize>,
    suffix_totals: Vec<usize>,
}

#[derive(Debug, Default)]
pub(super) struct BindingRefSet {
    ids: BTreeSet<AstBindingRef>,
}

impl BindingRefSet {
    pub(super) fn from_bindings(bindings: &[AstLocalBinding]) -> Self {
        Self {
            ids: bindings.iter().map(|binding| binding.id).collect(),
        }
    }
}

trait BindingLookup {
    fn contains_binding(&self, binding: AstBindingRef) -> bool;
}

impl BindingLookup for BindingRefSet {
    fn contains_binding(&self, binding: AstBindingRef) -> bool {
        self.ids.contains(&binding)
    }
}

impl BindingUseIndex {
    pub(super) fn for_stmts(stmts: &[AstStmt]) -> Self {
        Self::for_stmts_with_scope(stmts, BindingUseScope::CurrentFunctionOnly)
    }

    pub(super) fn for_stmts_deep(stmts: &[AstStmt]) -> Self {
        Self::for_stmts_with_scope(stmts, BindingUseScope::IncludingNestedFunctions)
    }

    fn for_stmts_with_scope(stmts: &[AstStmt], scope: BindingUseScope) -> Self {
        let mut stmt_counts = Vec::with_capacity(stmts.len());
        let mut occurrences = BTreeMap::<AstBindingRef, Vec<(usize, usize)>>::new();

        for (stmt_index, stmt) in stmts.iter().enumerate() {
            let mut counts = BTreeMap::new();
            collect_binding_uses_in_stmt_with_scope(stmt, scope, &mut counts);
            for (&binding, &count) in &counts {
                occurrences
                    .entry(binding)
                    .or_default()
                    .push((stmt_index, count));
            }
            stmt_counts.push(counts);
        }

        let suffix_counts = occurrences
            .into_iter()
            .map(|(binding, entries)| {
                let mut stmt_indices = Vec::with_capacity(entries.len());
                let mut suffix_totals = Vec::with_capacity(entries.len());
                let mut running_total = 0usize;

                for (stmt_index, count) in entries.iter().rev() {
                    running_total += *count;
                    stmt_indices.push(*stmt_index);
                    suffix_totals.push(running_total);
                }

                stmt_indices.reverse();
                suffix_totals.reverse();

                (
                    binding,
                    BindingUseSuffixCounts {
                        stmt_indices,
                        suffix_totals,
                    },
                )
            })
            .collect();

        Self {
            stmt_len: stmts.len(),
            stmt_counts,
            suffix_counts,
        }
    }

    pub(super) fn count_uses_in_suffix(&self, start: usize, binding: AstBindingRef) -> usize {
        if start >= self.stmt_len {
            return 0;
        }

        let Some(counts) = self.suffix_counts.get(&binding) else {
            return 0;
        };
        let first_suffix_stmt = counts
            .stmt_indices
            .partition_point(|stmt_index| *stmt_index < start);
        counts
            .suffix_totals
            .get(first_suffix_stmt)
            .copied()
            .unwrap_or(0)
    }

    pub(super) fn count_uses_in_range(
        &self,
        start: usize,
        end: usize,
        binding: AstBindingRef,
    ) -> usize {
        if start >= end {
            return 0;
        }
        self.count_uses_in_suffix(start, binding) - self.count_uses_in_suffix(end, binding)
    }

    pub(super) fn count_uses_in_stmt_index(
        &self,
        stmt_index: usize,
        binding: AstBindingRef,
    ) -> usize {
        self.stmt_counts
            .get(stmt_index)
            .and_then(|counts| counts.get(&binding))
            .copied()
            .unwrap_or(0)
    }
}

pub(super) fn count_binding_uses_in_block_deep(block: &AstBlock, binding: AstBindingRef) -> usize {
    count_binding_uses_in_block_with_scope(
        block,
        binding,
        BindingUseScope::IncludingNestedFunctions,
    )
}

pub(super) fn binding_mentions_in_stmt(stmt: &AstStmt) -> BTreeSet<AstBindingRef> {
    let mut mentions = BTreeSet::new();
    collect_binding_mentions_in_stmt(stmt, &mut mentions);
    mentions
}

pub(super) fn count_binding_uses_in_stmt(stmt: &AstStmt, binding: AstBindingRef) -> usize {
    count_binding_uses_in_stmt_with_scope(stmt, binding, BindingUseScope::CurrentFunctionOnly)
}

fn count_binding_uses_in_stmts_with_scope(
    stmts: &[AstStmt],
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    stmts
        .iter()
        .map(|stmt| count_binding_uses_in_stmt_with_scope(stmt, binding, scope))
        .sum()
}

fn count_binding_uses_in_block_with_scope(
    block: &AstBlock,
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    count_binding_uses_in_stmts_with_scope(&block.stmts, binding, scope)
}

fn count_binding_uses_in_stmt_with_scope(
    stmt: &AstStmt,
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .map(|value| count_binding_uses_in_expr_with_scope(value, binding, scope))
            .sum(),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .map(|value| count_binding_uses_in_expr_with_scope(value, binding, scope))
            .sum(),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .map(|target| count_binding_uses_in_lvalue_with_scope(target, binding, scope))
                .sum::<usize>()
                + assign
                    .values
                    .iter()
                    .map(|value| count_binding_uses_in_expr_with_scope(value, binding, scope))
                    .sum::<usize>()
        }
        AstStmt::CallStmt(call_stmt) => {
            count_binding_uses_in_call_with_scope(&call_stmt.call, binding, scope)
        }
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .map(|value| count_binding_uses_in_expr_with_scope(value, binding, scope))
            .sum(),
        AstStmt::If(if_stmt) => {
            count_binding_uses_in_expr_with_scope(&if_stmt.cond, binding, scope)
                + count_binding_uses_in_block_with_scope(&if_stmt.then_block, binding, scope)
                + if_stmt
                    .else_block
                    .as_ref()
                    .map(|else_block| {
                        count_binding_uses_in_block_with_scope(else_block, binding, scope)
                    })
                    .unwrap_or(0)
        }
        AstStmt::While(while_stmt) => {
            count_binding_uses_in_expr_with_scope(&while_stmt.cond, binding, scope)
                + count_binding_uses_in_block_with_scope(&while_stmt.body, binding, scope)
        }
        AstStmt::Repeat(repeat_stmt) => {
            count_binding_uses_in_block_with_scope(&repeat_stmt.body, binding, scope)
                + count_binding_uses_in_expr_with_scope(&repeat_stmt.cond, binding, scope)
        }
        AstStmt::NumericFor(numeric_for) => {
            count_binding_uses_in_expr_with_scope(&numeric_for.start, binding, scope)
                + count_binding_uses_in_expr_with_scope(&numeric_for.limit, binding, scope)
                + count_binding_uses_in_expr_with_scope(&numeric_for.step, binding, scope)
                + count_binding_uses_in_block_with_scope(&numeric_for.body, binding, scope)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .map(|expr| count_binding_uses_in_expr_with_scope(expr, binding, scope))
                .sum::<usize>()
                + count_binding_uses_in_block_with_scope(&generic_for.body, binding, scope)
        }
        AstStmt::DoBlock(block) => count_binding_uses_in_block_with_scope(block, binding, scope),
        AstStmt::FunctionDecl(function_decl) => {
            count_function_capture_use(&function_decl.func, binding)
                + if matches!(scope, BindingUseScope::IncludingNestedFunctions) {
                    count_binding_uses_in_block_with_scope(&function_decl.func.body, binding, scope)
                } else {
                    0
                }
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            count_function_capture_use(&function_decl.func, binding)
                + if matches!(scope, BindingUseScope::IncludingNestedFunctions) {
                    count_binding_uses_in_block_with_scope(&function_decl.func.body, binding, scope)
                } else {
                    0
                }
        }
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => 0,
    }
}

fn collect_binding_uses_in_block_with_scope(
    block: &AstBlock,
    scope: BindingUseScope,
    counts: &mut BTreeMap<AstBindingRef, usize>,
) {
    for stmt in &block.stmts {
        collect_binding_uses_in_stmt_with_scope(stmt, scope, counts);
    }
}

fn collect_binding_uses_in_stmt_with_scope(
    stmt: &AstStmt,
    scope: BindingUseScope,
    counts: &mut BTreeMap<AstBindingRef, usize>,
) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_binding_uses_in_expr_with_scope(value, scope, counts);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_binding_uses_in_expr_with_scope(value, scope, counts);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_binding_uses_in_lvalue_with_scope(target, scope, counts);
            }
            for value in &assign.values {
                collect_binding_uses_in_expr_with_scope(value, scope, counts);
            }
        }
        AstStmt::CallStmt(call_stmt) => {
            collect_binding_uses_in_call_with_scope(&call_stmt.call, scope, counts);
        }
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_binding_uses_in_expr_with_scope(value, scope, counts);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_binding_uses_in_expr_with_scope(&if_stmt.cond, scope, counts);
            collect_binding_uses_in_block_with_scope(&if_stmt.then_block, scope, counts);
            if let Some(else_block) = &if_stmt.else_block {
                collect_binding_uses_in_block_with_scope(else_block, scope, counts);
            }
        }
        AstStmt::While(while_stmt) => {
            collect_binding_uses_in_expr_with_scope(&while_stmt.cond, scope, counts);
            collect_binding_uses_in_block_with_scope(&while_stmt.body, scope, counts);
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_binding_uses_in_block_with_scope(&repeat_stmt.body, scope, counts);
            collect_binding_uses_in_expr_with_scope(&repeat_stmt.cond, scope, counts);
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_binding_uses_in_expr_with_scope(&numeric_for.start, scope, counts);
            collect_binding_uses_in_expr_with_scope(&numeric_for.limit, scope, counts);
            collect_binding_uses_in_expr_with_scope(&numeric_for.step, scope, counts);
            collect_binding_uses_in_block_with_scope(&numeric_for.body, scope, counts);
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_binding_uses_in_expr_with_scope(expr, scope, counts);
            }
            collect_binding_uses_in_block_with_scope(&generic_for.body, scope, counts);
        }
        AstStmt::DoBlock(block) => collect_binding_uses_in_block_with_scope(block, scope, counts),
        AstStmt::FunctionDecl(function_decl) => {
            collect_function_capture_uses(&function_decl.func, counts);
            if matches!(scope, BindingUseScope::IncludingNestedFunctions) {
                collect_binding_uses_in_block_with_scope(&function_decl.func.body, scope, counts);
            }
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            collect_function_capture_uses(&function_decl.func, counts);
            if matches!(scope, BindingUseScope::IncludingNestedFunctions) {
                collect_binding_uses_in_block_with_scope(&function_decl.func.body, scope, counts);
            }
        }
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => {}
    }
}

fn collect_binding_mentions_in_block(block: &AstBlock, mentions: &mut BTreeSet<AstBindingRef>) {
    for stmt in &block.stmts {
        collect_binding_mentions_in_stmt(stmt, mentions);
    }
}

fn collect_binding_mentions_in_stmt(stmt: &AstStmt, mentions: &mut BTreeSet<AstBindingRef>) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            mentions.extend(local_decl.bindings.iter().map(|binding| binding.id));
            for value in &local_decl.values {
                collect_binding_mentions_in_expr(value, mentions);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_binding_mentions_in_expr(value, mentions);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_binding_mentions_in_lvalue(target, mentions);
            }
            for value in &assign.values {
                collect_binding_mentions_in_expr(value, mentions);
            }
        }
        AstStmt::CallStmt(call_stmt) => collect_binding_mentions_in_call(&call_stmt.call, mentions),
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_binding_mentions_in_expr(value, mentions);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_binding_mentions_in_expr(&if_stmt.cond, mentions);
            collect_binding_mentions_in_block(&if_stmt.then_block, mentions);
            if let Some(else_block) = &if_stmt.else_block {
                collect_binding_mentions_in_block(else_block, mentions);
            }
        }
        AstStmt::While(while_stmt) => {
            collect_binding_mentions_in_expr(&while_stmt.cond, mentions);
            collect_binding_mentions_in_block(&while_stmt.body, mentions);
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_binding_mentions_in_block(&repeat_stmt.body, mentions);
            collect_binding_mentions_in_expr(&repeat_stmt.cond, mentions);
        }
        AstStmt::NumericFor(numeric_for) => {
            mentions.insert(numeric_for.binding);
            collect_binding_mentions_in_expr(&numeric_for.start, mentions);
            collect_binding_mentions_in_expr(&numeric_for.limit, mentions);
            collect_binding_mentions_in_expr(&numeric_for.step, mentions);
            collect_binding_mentions_in_block(&numeric_for.body, mentions);
        }
        AstStmt::GenericFor(generic_for) => {
            mentions.extend(generic_for.bindings.iter().copied());
            for expr in &generic_for.iterator {
                collect_binding_mentions_in_expr(expr, mentions);
            }
            collect_binding_mentions_in_block(&generic_for.body, mentions);
        }
        AstStmt::DoBlock(block) => collect_binding_mentions_in_block(block, mentions),
        AstStmt::FunctionDecl(function_decl) => {
            collect_function_name_mentions(&function_decl.target, mentions);
            collect_function_capture_mentions(&function_decl.func, mentions);
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            mentions.insert(function_decl.name);
            collect_function_capture_mentions(&function_decl.func, mentions);
        }
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => {}
    }
}

fn collect_binding_mentions_in_call(call: &AstCallKind, mentions: &mut BTreeSet<AstBindingRef>) {
    match call {
        AstCallKind::Call(call) => {
            collect_binding_mentions_in_expr(&call.callee, mentions);
            for arg in &call.args {
                collect_binding_mentions_in_expr(arg, mentions);
            }
        }
        AstCallKind::MethodCall(call) => {
            collect_binding_mentions_in_expr(&call.receiver, mentions);
            for arg in &call.args {
                collect_binding_mentions_in_expr(arg, mentions);
            }
        }
    }
}

fn collect_binding_mentions_in_lvalue(target: &AstLValue, mentions: &mut BTreeSet<AstBindingRef>) {
    match target {
        AstLValue::Name(name) => {
            if let Some(binding) = binding_from_name_ref(name) {
                mentions.insert(binding);
            }
        }
        AstLValue::FieldAccess(access) => {
            collect_binding_mentions_in_expr(&access.base, mentions);
        }
        AstLValue::IndexAccess(access) => {
            collect_binding_mentions_in_expr(&access.base, mentions);
            collect_binding_mentions_in_expr(&access.index, mentions);
        }
    }
}

fn collect_binding_mentions_in_expr(expr: &AstExpr, mentions: &mut BTreeSet<AstBindingRef>) {
    match expr {
        AstExpr::Var(name) => {
            if let Some(binding) = binding_from_name_ref(name) {
                mentions.insert(binding);
            }
        }
        AstExpr::FieldAccess(access) => collect_binding_mentions_in_expr(&access.base, mentions),
        AstExpr::IndexAccess(access) => {
            collect_binding_mentions_in_expr(&access.base, mentions);
            collect_binding_mentions_in_expr(&access.index, mentions);
        }
        AstExpr::Unary(unary) => collect_binding_mentions_in_expr(&unary.expr, mentions),
        AstExpr::Binary(binary) => {
            collect_binding_mentions_in_expr(&binary.lhs, mentions);
            collect_binding_mentions_in_expr(&binary.rhs, mentions);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_binding_mentions_in_expr(&logical.lhs, mentions);
            collect_binding_mentions_in_expr(&logical.rhs, mentions);
        }
        AstExpr::Call(call) => {
            collect_binding_mentions_in_expr(&call.callee, mentions);
            for arg in &call.args {
                collect_binding_mentions_in_expr(arg, mentions);
            }
        }
        AstExpr::MethodCall(call) => {
            collect_binding_mentions_in_expr(&call.receiver, mentions);
            for arg in &call.args {
                collect_binding_mentions_in_expr(arg, mentions);
            }
        }
        AstExpr::SingleValue(expr) => collect_binding_mentions_in_expr(expr, mentions),
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    AstTableField::Array(value) => {
                        collect_binding_mentions_in_expr(value, mentions);
                    }
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &record.key {
                            collect_binding_mentions_in_expr(key, mentions);
                        }
                        collect_binding_mentions_in_expr(&record.value, mentions);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(function) => collect_function_capture_mentions(function, mentions),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg
        | AstExpr::Error(_) => {}
    }
}

fn collect_function_name_mentions(
    target: &super::super::common::AstFunctionName,
    mentions: &mut BTreeSet<AstBindingRef>,
) {
    let path = match target {
        super::super::common::AstFunctionName::Plain(path) => path,
        super::super::common::AstFunctionName::Method(path, _) => path,
    };
    if let Some(binding) = binding_from_name_ref(&path.root) {
        mentions.insert(binding);
    }
}

fn count_binding_uses_in_call_with_scope(
    call: &AstCallKind,
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    match call {
        AstCallKind::Call(call) => count_call_expr_uses_with_scope(call, binding, scope),
        AstCallKind::MethodCall(call) => {
            count_method_call_expr_uses_with_scope(call, binding, scope)
        }
    }
}

fn count_call_expr_uses_with_scope(
    call: &AstCallExpr,
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    count_binding_uses_in_expr_with_scope(&call.callee, binding, scope)
        + count_expr_list_uses_with_scope(&call.args, binding, scope)
}

fn count_method_call_expr_uses_with_scope(
    call: &AstMethodCallExpr,
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    count_binding_uses_in_expr_with_scope(&call.receiver, binding, scope)
        + count_expr_list_uses_with_scope(&call.args, binding, scope)
}

fn count_expr_list_uses_with_scope(
    exprs: &[AstExpr],
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    exprs
        .iter()
        .map(|expr| count_binding_uses_in_expr_with_scope(expr, binding, scope))
        .sum()
}

fn collect_binding_uses_in_call_with_scope(
    call: &AstCallKind,
    scope: BindingUseScope,
    counts: &mut BTreeMap<AstBindingRef, usize>,
) {
    match call {
        AstCallKind::Call(call) => {
            collect_binding_uses_in_expr_with_scope(&call.callee, scope, counts);
            for arg in &call.args {
                collect_binding_uses_in_expr_with_scope(arg, scope, counts);
            }
        }
        AstCallKind::MethodCall(call) => {
            collect_binding_uses_in_expr_with_scope(&call.receiver, scope, counts);
            for arg in &call.args {
                collect_binding_uses_in_expr_with_scope(arg, scope, counts);
            }
        }
    }
}

fn count_binding_uses_in_lvalue_with_scope(
    target: &AstLValue,
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    match target {
        AstLValue::Name(_) => 0,
        AstLValue::FieldAccess(access) => {
            count_binding_uses_in_expr_with_scope(&access.base, binding, scope)
        }
        AstLValue::IndexAccess(access) => {
            count_binding_uses_in_expr_with_scope(&access.base, binding, scope)
                + count_binding_uses_in_expr_with_scope(&access.index, binding, scope)
        }
    }
}

fn collect_binding_uses_in_lvalue_with_scope(
    target: &AstLValue,
    scope: BindingUseScope,
    counts: &mut BTreeMap<AstBindingRef, usize>,
) {
    match target {
        AstLValue::Name(_) => {}
        AstLValue::FieldAccess(access) => {
            collect_binding_uses_in_expr_with_scope(&access.base, scope, counts);
        }
        AstLValue::IndexAccess(access) => {
            collect_binding_uses_in_expr_with_scope(&access.base, scope, counts);
            collect_binding_uses_in_expr_with_scope(&access.index, scope, counts);
        }
    }
}

fn count_binding_uses_in_expr_with_scope(
    expr: &AstExpr,
    binding: AstBindingRef,
    scope: BindingUseScope,
) -> usize {
    match expr {
        AstExpr::Var(name) if name_matches_binding(name, binding) => 1,
        AstExpr::FieldAccess(access) => {
            count_binding_uses_in_expr_with_scope(&access.base, binding, scope)
        }
        AstExpr::IndexAccess(access) => {
            count_binding_uses_in_expr_with_scope(&access.base, binding, scope)
                + count_binding_uses_in_expr_with_scope(&access.index, binding, scope)
        }
        AstExpr::Unary(unary) => count_binding_uses_in_expr_with_scope(&unary.expr, binding, scope),
        AstExpr::Binary(binary) => {
            count_binding_uses_in_expr_with_scope(&binary.lhs, binding, scope)
                + count_binding_uses_in_expr_with_scope(&binary.rhs, binding, scope)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            count_binding_uses_in_expr_with_scope(&logical.lhs, binding, scope)
                + count_binding_uses_in_expr_with_scope(&logical.rhs, binding, scope)
        }
        AstExpr::Call(call) => count_call_expr_uses_with_scope(call, binding, scope),
        AstExpr::MethodCall(call) => count_method_call_expr_uses_with_scope(call, binding, scope),
        AstExpr::SingleValue(expr) => count_binding_uses_in_expr_with_scope(expr, binding, scope),
        AstExpr::TableConstructor(table) => table
            .fields
            .iter()
            .map(|field| match field {
                AstTableField::Array(value) => {
                    count_binding_uses_in_expr_with_scope(value, binding, scope)
                }
                AstTableField::Record(record) => {
                    let key_count = if let AstTableKey::Expr(key) = &record.key {
                        count_binding_uses_in_expr_with_scope(key, binding, scope)
                    } else {
                        0
                    };
                    key_count + count_binding_uses_in_expr_with_scope(&record.value, binding, scope)
                }
            })
            .sum(),
        AstExpr::FunctionExpr(function) => {
            count_function_capture_use(function, binding)
                + if matches!(scope, BindingUseScope::IncludingNestedFunctions) {
                    count_binding_uses_in_block_with_scope(&function.body, binding, scope)
                } else {
                    0
                }
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg
        | AstExpr::Error(_) => 0,
    }
}

fn collect_binding_uses_in_expr_with_scope(
    expr: &AstExpr,
    scope: BindingUseScope,
    counts: &mut BTreeMap<AstBindingRef, usize>,
) {
    match expr {
        AstExpr::Var(name) => {
            if let Some(binding) = binding_from_name_ref(name) {
                *counts.entry(binding).or_insert(0) += 1;
            }
        }
        AstExpr::FieldAccess(access) => {
            collect_binding_uses_in_expr_with_scope(&access.base, scope, counts);
        }
        AstExpr::IndexAccess(access) => {
            collect_binding_uses_in_expr_with_scope(&access.base, scope, counts);
            collect_binding_uses_in_expr_with_scope(&access.index, scope, counts);
        }
        AstExpr::Unary(unary) => {
            collect_binding_uses_in_expr_with_scope(&unary.expr, scope, counts);
        }
        AstExpr::Binary(binary) => {
            collect_binding_uses_in_expr_with_scope(&binary.lhs, scope, counts);
            collect_binding_uses_in_expr_with_scope(&binary.rhs, scope, counts);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_binding_uses_in_expr_with_scope(&logical.lhs, scope, counts);
            collect_binding_uses_in_expr_with_scope(&logical.rhs, scope, counts);
        }
        AstExpr::Call(call) => {
            collect_binding_uses_in_expr_with_scope(&call.callee, scope, counts);
            for arg in &call.args {
                collect_binding_uses_in_expr_with_scope(arg, scope, counts);
            }
        }
        AstExpr::MethodCall(call) => {
            collect_binding_uses_in_expr_with_scope(&call.receiver, scope, counts);
            for arg in &call.args {
                collect_binding_uses_in_expr_with_scope(arg, scope, counts);
            }
        }
        AstExpr::SingleValue(expr) => {
            collect_binding_uses_in_expr_with_scope(expr, scope, counts);
        }
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    AstTableField::Array(value) => {
                        collect_binding_uses_in_expr_with_scope(value, scope, counts);
                    }
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &record.key {
                            collect_binding_uses_in_expr_with_scope(key, scope, counts);
                        }
                        collect_binding_uses_in_expr_with_scope(&record.value, scope, counts);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(function) => {
            collect_function_capture_uses(function, counts);
            if matches!(scope, BindingUseScope::IncludingNestedFunctions) {
                collect_binding_uses_in_block_with_scope(&function.body, scope, counts);
            }
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg
        | AstExpr::Error(_) => {}
    }
}

fn count_function_capture_use(
    function: &super::super::common::AstFunctionExpr,
    binding: AstBindingRef,
) -> usize {
    usize::from(function.captured_bindings.contains(&binding))
}

fn collect_function_capture_uses(
    function: &super::super::common::AstFunctionExpr,
    counts: &mut BTreeMap<AstBindingRef, usize>,
) {
    for binding in &function.captured_bindings {
        *counts.entry(*binding).or_insert(0) += 1;
    }
}

fn collect_function_capture_mentions(
    function: &super::super::common::AstFunctionExpr,
    mentions: &mut BTreeSet<AstBindingRef>,
) {
    mentions.extend(function.captured_bindings.iter().copied());
}

pub(super) fn stmt_references_any_binding(stmt: &AstStmt, bindings: &[AstLocalBinding]) -> bool {
    let refs = BindingRefSet::from_bindings(bindings);
    stmt_references_binding_set(stmt, &refs)
}

pub(super) fn stmt_references_binding_set(stmt: &AstStmt, bindings: &BindingRefSet) -> bool {
    stmt_references_binding_lookup(stmt, bindings)
}

fn stmt_references_binding_lookup(stmt: &AstStmt, bindings: &dyn BindingLookup) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            local_decl
                .bindings
                .iter()
                .any(|binding| bindings.contains_binding(binding.id))
                || local_decl
                    .values
                    .iter()
                    .any(|value| expr_references_binding_lookup(value, bindings))
        }
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .any(|value| expr_references_binding_lookup(value, bindings)),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| lvalue_references_binding_lookup(target, bindings))
                || assign
                    .values
                    .iter()
                    .any(|value| expr_references_binding_lookup(value, bindings))
        }
        AstStmt::CallStmt(call_stmt) => call_references_binding_lookup(&call_stmt.call, bindings),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .any(|value| expr_references_binding_lookup(value, bindings)),
        AstStmt::If(if_stmt) => {
            expr_references_binding_lookup(&if_stmt.cond, bindings)
                || block_references_binding_lookup(&if_stmt.then_block, bindings)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block_references_binding_lookup(block, bindings))
        }
        AstStmt::While(while_stmt) => {
            expr_references_binding_lookup(&while_stmt.cond, bindings)
                || block_references_binding_lookup(&while_stmt.body, bindings)
        }
        AstStmt::Repeat(repeat_stmt) => {
            block_references_binding_lookup(&repeat_stmt.body, bindings)
                || expr_references_binding_lookup(&repeat_stmt.cond, bindings)
        }
        AstStmt::NumericFor(numeric_for) => {
            bindings.contains_binding(numeric_for.binding)
                || expr_references_binding_lookup(&numeric_for.start, bindings)
                || expr_references_binding_lookup(&numeric_for.limit, bindings)
                || expr_references_binding_lookup(&numeric_for.step, bindings)
                || block_references_binding_lookup(&numeric_for.body, bindings)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .bindings
                .iter()
                .any(|binding| bindings.contains_binding(*binding))
                || generic_for
                    .iterator
                    .iter()
                    .any(|expr| expr_references_binding_lookup(expr, bindings))
                || block_references_binding_lookup(&generic_for.body, bindings)
        }
        AstStmt::DoBlock(block) => block_references_binding_lookup(block, bindings),
        AstStmt::FunctionDecl(function_decl) => {
            function_name_references_binding_lookup(&function_decl.target, bindings)
                || function_capture_references_binding_lookup(&function_decl.func, bindings)
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            bindings.contains_binding(function_decl.name)
                || function_capture_references_binding_lookup(&function_decl.func, bindings)
        }
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => false,
    }
}

pub(super) fn block_references_binding_set(block: &AstBlock, bindings: &BindingRefSet) -> bool {
    block_references_binding_lookup(block, bindings)
}

fn block_references_binding_lookup(block: &AstBlock, bindings: &dyn BindingLookup) -> bool {
    block
        .stmts
        .iter()
        .any(|stmt| stmt_references_binding_lookup(stmt, bindings))
}

pub(super) fn expr_references_any_binding(expr: &AstExpr, bindings: &[AstLocalBinding]) -> bool {
    let refs = BindingRefSet::from_bindings(bindings);
    expr_references_binding_set(expr, &refs)
}

pub(super) fn expr_references_binding_set(expr: &AstExpr, bindings: &BindingRefSet) -> bool {
    expr_references_binding_lookup(expr, bindings)
}

fn expr_references_binding_lookup(expr: &AstExpr, bindings: &dyn BindingLookup) -> bool {
    match expr {
        AstExpr::Var(name) => name_ref_matches_binding_lookup(name, bindings),
        AstExpr::FieldAccess(access) => expr_references_binding_lookup(&access.base, bindings),
        AstExpr::IndexAccess(access) => {
            expr_references_binding_lookup(&access.base, bindings)
                || expr_references_binding_lookup(&access.index, bindings)
        }
        AstExpr::Unary(unary) => expr_references_binding_lookup(&unary.expr, bindings),
        AstExpr::Binary(binary) => {
            expr_references_binding_lookup(&binary.lhs, bindings)
                || expr_references_binding_lookup(&binary.rhs, bindings)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_references_binding_lookup(&logical.lhs, bindings)
                || expr_references_binding_lookup(&logical.rhs, bindings)
        }
        AstExpr::Call(call) => {
            expr_references_binding_lookup(&call.callee, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding_lookup(arg, bindings))
        }
        AstExpr::MethodCall(call) => {
            expr_references_binding_lookup(&call.receiver, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding_lookup(arg, bindings))
        }
        AstExpr::SingleValue(expr) => expr_references_binding_lookup(expr, bindings),
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            AstTableField::Array(value) => expr_references_binding_lookup(value, bindings),
            AstTableField::Record(record) => {
                let key_references_binding = match &record.key {
                    AstTableKey::Name(_) => false,
                    AstTableKey::Expr(expr) => expr_references_binding_lookup(expr, bindings),
                };
                key_references_binding || expr_references_binding_lookup(&record.value, bindings)
            }
        }),
        AstExpr::FunctionExpr(function) => {
            function_capture_references_binding_lookup(function, bindings)
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg
        | AstExpr::Error(_) => false,
    }
}

fn call_references_binding_lookup(call: &AstCallKind, bindings: &dyn BindingLookup) -> bool {
    match call {
        AstCallKind::Call(call) => {
            expr_references_binding_lookup(&call.callee, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding_lookup(arg, bindings))
        }
        AstCallKind::MethodCall(call) => {
            expr_references_binding_lookup(&call.receiver, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding_lookup(arg, bindings))
        }
    }
}

fn function_name_references_binding_lookup(
    target: &super::super::common::AstFunctionName,
    bindings: &dyn BindingLookup,
) -> bool {
    let path = match target {
        super::super::common::AstFunctionName::Plain(path) => path,
        super::super::common::AstFunctionName::Method(path, _) => path,
    };
    name_ref_matches_binding_lookup(&path.root, bindings)
}

fn function_capture_references_binding_lookup(
    function: &super::super::common::AstFunctionExpr,
    bindings: &dyn BindingLookup,
) -> bool {
    function
        .captured_bindings
        .iter()
        .any(|binding| bindings.contains_binding(*binding))
}

fn lvalue_references_binding_lookup(target: &AstLValue, bindings: &dyn BindingLookup) -> bool {
    match target {
        AstLValue::Name(name) => name_ref_matches_binding_lookup(name, bindings),
        AstLValue::FieldAccess(access) => expr_references_binding_lookup(&access.base, bindings),
        AstLValue::IndexAccess(access) => {
            expr_references_binding_lookup(&access.base, bindings)
                || expr_references_binding_lookup(&access.index, bindings)
        }
    }
}

fn name_ref_matches_binding_lookup(name: &AstNameRef, bindings: &dyn BindingLookup) -> bool {
    binding_from_name_ref(name).is_some_and(|binding| bindings.contains_binding(binding))
}
