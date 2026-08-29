//! 这个文件集中承载 AST readability 里的局部 binding 流分析工具。
//!
//! 这些 pass 经常需要回答同一类问题：
//! - 某个 binding 在一段语句里还会不会再被读取？
//! - 某个语句实际提到了哪些 binding（包括赋值目标这种 mention，而不只是读取）？
//! - 某个语句/块会不会提前引用一组待下沉的 hoisted local？
//! - 某个 binding 在当前函数体里一共被用了几次？
//! - repeat body 之后的 until 条件会不会继续读取正文 local？
//!
//! 这里故意把“当前函数体”作为边界，不继续钻进嵌套函数体。
//! 原因是 AST 的 `LocalId` / `SyntheticLocalId` 都是按函数局部编号的，跨闭包继续统计
//! 很容易把不同函数里碰巧同号的 binding 错算成同一个变量。
//! 但 `FunctionExpr.captured_bindings` 是闭包创建时对当前词法 binding 的显式引用，
//! 必须按当前语句的一次使用统计，否则后续 pass 可能误删仍被闭包持有的局部。

mod refs;

use std::collections::{BTreeMap, BTreeSet};

use super::super::common::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstNameRef, AstStmt,
    AstTableField, AstTableKey,
};
use super::binding_ref::binding_from_name_ref;

pub(super) use refs::{
    BindingRefSet, block_references_binding_set, expr_references_any_binding,
    expr_references_binding_set, stmt_references_any_binding, stmt_references_binding_set,
};

pub(super) type MutableSnapshotNames = BTreeSet<AstNameRef>;

pub(super) fn mutable_snapshot_names_in_block(block: &AstBlock) -> MutableSnapshotNames {
    #[derive(Default)]
    struct CaptureCollector(MutableSnapshotNames);

    impl super::visit::AstVisitor for CaptureCollector {
        fn visit_function_expr(&mut self, function: &AstFunctionExpr) -> bool {
            self.0.extend(
                function
                    .captured_bindings
                    .iter()
                    .copied()
                    .map(AstBindingRef::to_name_ref),
            );
            self.0.extend(
                function
                    .captured_params
                    .iter()
                    .copied()
                    .map(AstNameRef::Param),
            );
            false
        }
    }

    let mut collector = CaptureCollector::default();
    super::visit::visit_block(block, &mut collector);
    collector.0
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

impl BindingUseIndex {
    pub(super) fn for_stmts(stmts: &[AstStmt]) -> Self {
        Self::for_stmts_with_trailing_expr(stmts, None)
    }

    pub(super) fn for_stmts_with_trailing_expr(
        stmts: &[AstStmt],
        trailing_expr: Option<&AstExpr>,
    ) -> Self {
        let stmt_len = stmts.len() + usize::from(trailing_expr.is_some());
        let mut stmt_counts = Vec::with_capacity(stmt_len);
        let mut occurrences = BTreeMap::<AstBindingRef, Vec<(usize, usize)>>::new();

        for (stmt_index, stmt) in stmts.iter().enumerate() {
            let mut counts = BTreeMap::new();
            collect_binding_uses_in_stmt(stmt, &mut counts);
            for (&binding, &count) in &counts {
                occurrences
                    .entry(binding)
                    .or_default()
                    .push((stmt_index, count));
            }
            stmt_counts.push(counts);
        }

        if let Some(expr) = trailing_expr {
            let stmt_index = stmts.len();
            let mut counts = BTreeMap::new();
            collect_binding_uses_in_expr(expr, &mut counts);
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
            stmt_len,
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

    /// 返回 suffix 中所有承载该 binding 读取的顶层语句索引。
    ///
    /// 同一语句内的多次读取只出现一个索引；trailing expression 仍以末尾虚拟语句表示。
    pub(super) fn use_stmt_indices_in_suffix(
        &self,
        start: usize,
        binding: AstBindingRef,
    ) -> &[usize] {
        let Some(counts) = self.suffix_counts.get(&binding) else {
            return &[];
        };
        let index = counts
            .stmt_indices
            .partition_point(|stmt_index| *stmt_index < start);
        &counts.stmt_indices[index..]
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

    pub(super) fn uses_in_stmt_index(
        &self,
        stmt_index: usize,
    ) -> impl Iterator<Item = (AstBindingRef, usize)> + '_ {
        self.stmt_counts
            .get(stmt_index)
            .into_iter()
            .flat_map(|counts| counts.iter().map(|(binding, count)| (*binding, *count)))
    }
}

pub(super) fn binding_mentions_in_stmt(stmt: &AstStmt) -> BTreeSet<AstBindingRef> {
    let mut mentions = BTreeSet::new();
    collect_binding_mentions_in_stmt(stmt, &mut mentions);
    mentions
}

pub(super) fn binding_mentions_in_block(block: &AstBlock) -> BTreeSet<AstBindingRef> {
    let mut mentions = BTreeSet::new();
    collect_binding_mentions_in_block(block, &mut mentions);
    mentions
}

pub(super) fn binding_mentions_in_expr(expr: &AstExpr) -> BTreeSet<AstBindingRef> {
    let mut mentions = BTreeSet::new();
    collect_binding_mentions_in_expr(expr, &mut mentions);
    mentions
}

fn collect_binding_uses_in_block(block: &AstBlock, counts: &mut BTreeMap<AstBindingRef, usize>) {
    for stmt in &block.stmts {
        collect_binding_uses_in_stmt(stmt, counts);
    }
}

fn collect_binding_uses_in_stmt(stmt: &AstStmt, counts: &mut BTreeMap<AstBindingRef, usize>) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_binding_uses_in_expr(value, counts);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_binding_uses_in_expr(value, counts);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_binding_uses_in_lvalue(target, counts);
            }
            for value in &assign.values {
                collect_binding_uses_in_expr(value, counts);
            }
        }
        AstStmt::CallStmt(call_stmt) => {
            collect_binding_uses_in_call(&call_stmt.call, counts);
        }
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_binding_uses_in_expr(value, counts);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_binding_uses_in_expr(&if_stmt.cond, counts);
            collect_binding_uses_in_block(&if_stmt.then_block, counts);
            if let Some(else_block) = &if_stmt.else_block {
                collect_binding_uses_in_block(else_block, counts);
            }
        }
        AstStmt::While(while_stmt) => {
            collect_binding_uses_in_expr(&while_stmt.cond, counts);
            collect_binding_uses_in_block(&while_stmt.body, counts);
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_binding_uses_in_block(&repeat_stmt.body, counts);
            collect_binding_uses_in_expr(&repeat_stmt.cond, counts);
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_binding_uses_in_expr(&numeric_for.start, counts);
            collect_binding_uses_in_expr(&numeric_for.limit, counts);
            collect_binding_uses_in_expr(&numeric_for.step, counts);
            collect_binding_uses_in_block(&numeric_for.body, counts);
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_binding_uses_in_expr(expr, counts);
            }
            collect_binding_uses_in_block(&generic_for.body, counts);
        }
        AstStmt::DoBlock(block) => collect_binding_uses_in_block(block, counts),
        AstStmt::FunctionDecl(function_decl) => {
            collect_function_capture_uses(&function_decl.func, counts);
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            collect_function_capture_uses(&function_decl.func, counts);
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
        | AstExpr::Vector(_)
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

fn collect_binding_uses_in_call(call: &AstCallKind, counts: &mut BTreeMap<AstBindingRef, usize>) {
    match call {
        AstCallKind::Call(call) => {
            collect_binding_uses_in_expr(&call.callee, counts);
            for arg in &call.args {
                collect_binding_uses_in_expr(arg, counts);
            }
        }
        AstCallKind::MethodCall(call) => {
            collect_binding_uses_in_expr(&call.receiver, counts);
            for arg in &call.args {
                collect_binding_uses_in_expr(arg, counts);
            }
        }
    }
}

fn collect_binding_uses_in_lvalue(target: &AstLValue, counts: &mut BTreeMap<AstBindingRef, usize>) {
    match target {
        AstLValue::Name(_) => {}
        AstLValue::FieldAccess(access) => {
            collect_binding_uses_in_expr(&access.base, counts);
        }
        AstLValue::IndexAccess(access) => {
            collect_binding_uses_in_expr(&access.base, counts);
            collect_binding_uses_in_expr(&access.index, counts);
        }
    }
}

fn collect_binding_uses_in_expr(expr: &AstExpr, counts: &mut BTreeMap<AstBindingRef, usize>) {
    match expr {
        AstExpr::Var(name) => {
            if let Some(binding) = binding_from_name_ref(name) {
                *counts.entry(binding).or_insert(0) += 1;
            }
        }
        AstExpr::FieldAccess(access) => {
            collect_binding_uses_in_expr(&access.base, counts);
        }
        AstExpr::IndexAccess(access) => {
            collect_binding_uses_in_expr(&access.base, counts);
            collect_binding_uses_in_expr(&access.index, counts);
        }
        AstExpr::Unary(unary) => {
            collect_binding_uses_in_expr(&unary.expr, counts);
        }
        AstExpr::Binary(binary) => {
            collect_binding_uses_in_expr(&binary.lhs, counts);
            collect_binding_uses_in_expr(&binary.rhs, counts);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_binding_uses_in_expr(&logical.lhs, counts);
            collect_binding_uses_in_expr(&logical.rhs, counts);
        }
        AstExpr::Call(call) => {
            collect_binding_uses_in_expr(&call.callee, counts);
            for arg in &call.args {
                collect_binding_uses_in_expr(arg, counts);
            }
        }
        AstExpr::MethodCall(call) => {
            collect_binding_uses_in_expr(&call.receiver, counts);
            for arg in &call.args {
                collect_binding_uses_in_expr(arg, counts);
            }
        }
        AstExpr::SingleValue(expr) => {
            collect_binding_uses_in_expr(expr, counts);
        }
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    AstTableField::Array(value) => {
                        collect_binding_uses_in_expr(value, counts);
                    }
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &record.key {
                            collect_binding_uses_in_expr(key, counts);
                        }
                        collect_binding_uses_in_expr(&record.value, counts);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(function) => {
            collect_function_capture_uses(function, counts);
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg
        | AstExpr::Error(_) => {}
    }
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
