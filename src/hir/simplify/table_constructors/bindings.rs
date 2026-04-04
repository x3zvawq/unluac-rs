//! 这个子模块负责 table-constructor pass 里的 binding 识别与字段键翻译。
//!
//! 它依赖 HIR 已经分好的 lvalue/expr 形状，只回答“这个读写是不是同一个构造器绑定”，
//! 不会在这里扫描 region 或重建字段序列。
//! 例如：`t.x = v` 会在这里把键翻成 `Name(\"x\")` 并识别 `t` 的绑定身份。

use std::collections::BTreeMap;

use crate::hir::common::{
    HirCallExpr, HirDecisionTarget, HirExpr, HirLValue, HirStmt, HirTableField, HirTableKey,
};

use super::{BindingId, TableBinding};
use crate::hir::simplify::visit::{HirVisitor, visit_block, visit_stmts};

pub(super) fn binding_from_lvalue(lvalue: &HirLValue) -> Option<TableBinding> {
    match lvalue {
        HirLValue::Temp(temp) => Some(TableBinding::Temp(*temp)),
        HirLValue::Local(local) => Some(TableBinding::Local(*local)),
        HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => None,
    }
}

pub(super) fn binding_from_expr(expr: &HirExpr) -> Option<TableBinding> {
    match expr {
        HirExpr::TempRef(temp) => Some(TableBinding::Temp(*temp)),
        HirExpr::LocalRef(local) => Some(TableBinding::Local(*local)),
        _ => None,
    }
}

pub(super) fn matches_binding_ref(expr: &HirExpr, binding: TableBinding) -> bool {
    binding_from_expr(expr) == Some(binding)
}

pub(super) fn table_key_from_expr(expr: &HirExpr) -> HirTableKey {
    if let HirExpr::String(name) = expr
        && is_identifier_name(name)
    {
        return HirTableKey::Name(name.clone());
    }
    HirTableKey::Expr(expr.clone())
}

pub(super) fn collect_materialized_binding_counts(
    block: &crate::hir::common::HirBlock,
) -> BTreeMap<TableBinding, usize> {
    let mut collector = MaterializedBindingCollector::default();
    visit_block(block, &mut collector);
    collector.counts
}

#[derive(Debug, Clone, Default)]
pub(super) struct BindingIndex {
    ids: BTreeMap<TableBinding, BindingId>,
    bindings: Vec<TableBinding>,
}

impl BindingIndex {
    pub(super) fn intern(&mut self, binding: TableBinding) -> BindingId {
        if let Some(id) = self.ids.get(&binding).copied() {
            return id;
        }
        let id = self.bindings.len();
        self.ids.insert(binding, id);
        self.bindings.push(binding);
        id
    }

    pub(super) fn id_of(&self, binding: TableBinding) -> Option<BindingId> {
        self.ids.get(&binding).copied()
    }

    pub(super) fn len(&self) -> usize {
        self.bindings.len()
    }

    pub(super) fn materialized_counts(&self, counts: &BTreeMap<TableBinding, usize>) -> Vec<u32> {
        self.bindings
            .iter()
            .map(|binding| counts.get(binding).copied().unwrap_or_default() as u32)
            .collect()
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct StmtBindingSummary {
    ids: Vec<BindingId>,
}

impl StmtBindingSummary {
    pub(super) fn iter(&self) -> impl Iterator<Item = BindingId> + '_ {
        self.ids.iter().copied()
    }
}

pub(super) fn collect_stmt_binding_summary(
    stmt: &HirStmt,
    binding_index: &mut BindingIndex,
) -> StmtBindingSummary {
    intern_stmt_bindings(stmt, binding_index);
    collect_stmt_slice_binding_summary(std::slice::from_ref(stmt), binding_index)
}

pub(super) fn intern_stmt_bindings(stmt: &HirStmt, binding_index: &mut BindingIndex) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                binding_index.intern(TableBinding::Local(*binding));
            }
        }
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                if let Some(binding) = binding_from_lvalue(target) {
                    binding_index.intern(binding);
                }
            }
        }
        HirStmt::NumericFor(numeric_for) => {
            binding_index.intern(TableBinding::Local(numeric_for.binding));
        }
        HirStmt::GenericFor(generic_for) => {
            for binding in &generic_for.bindings {
                binding_index.intern(TableBinding::Local(*binding));
            }
        }
        HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::If(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::Block(_)
        | HirStmt::Unstructured(_) => {}
    }
}

pub(super) fn collect_stmt_slice_binding_summary(
    stmts: &[HirStmt],
    binding_index: &mut BindingIndex,
) -> StmtBindingSummary {
    let mut collector = BindingUseCollector {
        binding_index,
        ids: Vec::new(),
    };
    visit_stmts(stmts, &mut collector);
    collector.ids.sort_unstable();
    collector.ids.dedup();
    StmtBindingSummary { ids: collector.ids }
}

#[derive(Debug, Clone, Default)]
pub(super) struct BindingUseSummary {
    counts: Vec<u32>,
}

impl BindingUseSummary {
    pub(super) fn with_binding_count(binding_count: usize) -> Self {
        Self {
            counts: vec![0; binding_count],
        }
    }

    pub(super) fn contains(&self, binding_id: BindingId) -> bool {
        self.counts.get(binding_id).copied().unwrap_or_default() > 0
    }

    pub(super) fn add_stmt_bindings(&mut self, bindings: &StmtBindingSummary) {
        for binding_id in bindings.iter() {
            self.counts[binding_id] += 1;
        }
    }

    pub(super) fn remove_stmt_bindings(&mut self, bindings: &StmtBindingSummary) {
        for binding_id in bindings.iter() {
            self.counts[binding_id] -= 1;
        }
    }
}

pub(super) fn expr_uses_binding(expr: &HirExpr, binding: TableBinding) -> bool {
    if matches_binding_ref(expr, binding) {
        return true;
    }

    match expr {
        HirExpr::TableAccess(access) => {
            expr_uses_binding(&access.base, binding) || expr_uses_binding(&access.key, binding)
        }
        HirExpr::Unary(unary) => expr_uses_binding(&unary.expr, binding),
        HirExpr::Binary(binary) => {
            expr_uses_binding(&binary.lhs, binding) || expr_uses_binding(&binary.rhs, binding)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_uses_binding(&logical.lhs, binding) || expr_uses_binding(&logical.rhs, binding)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_uses_binding(&node.test, binding)
                || decision_target_uses_binding(&node.truthy, binding)
                || decision_target_uses_binding(&node.falsy, binding)
        }),
        HirExpr::Call(call) => call_expr_uses_binding(call, binding),
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                HirTableField::Array(expr) => expr_uses_binding(expr, binding),
                HirTableField::Record(field) => {
                    table_key_uses_binding(&field.key, binding)
                        || expr_uses_binding(&field.value, binding)
                }
            }) || table
                .trailing_multivalue
                .as_ref()
                .is_some_and(|expr| expr_uses_binding(expr, binding))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_uses_binding(&capture.value, binding)),
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
        | HirExpr::Unresolved(_) => false,
        HirExpr::TempRef(_) | HirExpr::LocalRef(_) => false,
    }
}

pub(super) fn lvalue_uses_binding(lvalue: &HirLValue, binding: TableBinding) -> bool {
    match lvalue {
        HirLValue::Temp(temp) => TableBinding::Temp(*temp) == binding,
        HirLValue::Local(local) => TableBinding::Local(*local) == binding,
        HirLValue::Upvalue(_) => false,
        HirLValue::Global(_) => false,
        HirLValue::TableAccess(access) => {
            expr_uses_binding(&access.base, binding) || expr_uses_binding(&access.key, binding)
        }
    }
}

pub(super) fn stmt_slice_mentions_binding(stmts: &[HirStmt], binding: TableBinding) -> bool {
    stmts
        .iter()
        .any(|stmt| stmt_mentions_binding(stmt, binding))
}

fn stmt_mentions_binding(stmt: &HirStmt, binding: TableBinding) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|value| expr_uses_binding(value, binding)),
        HirStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| lvalue_uses_binding(target, binding))
                || assign
                    .values
                    .iter()
                    .any(|value| expr_uses_binding(value, binding))
        }
        HirStmt::TableSetList(set_list) => {
            expr_uses_binding(&set_list.base, binding)
                || set_list
                    .values
                    .iter()
                    .any(|value| expr_uses_binding(value, binding))
                || set_list
                    .trailing_multivalue
                    .as_ref()
                    .is_some_and(|value| expr_uses_binding(value, binding))
        }
        HirStmt::ErrNil(err_nil) => expr_uses_binding(&err_nil.value, binding),
        HirStmt::ToBeClosed(to_be_closed) => expr_uses_binding(&to_be_closed.value, binding),
        HirStmt::Close(_) => false,
        HirStmt::CallStmt(call_stmt) => call_expr_uses_binding(&call_stmt.call, binding),
        HirStmt::Return(ret) => ret
            .values
            .iter()
            .any(|value| expr_uses_binding(value, binding)),
        HirStmt::If(if_stmt) => {
            expr_uses_binding(&if_stmt.cond, binding)
                || stmt_slice_mentions_binding(&if_stmt.then_block.stmts, binding)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| stmt_slice_mentions_binding(&block.stmts, binding))
        }
        HirStmt::While(while_stmt) => {
            expr_uses_binding(&while_stmt.cond, binding)
                || stmt_slice_mentions_binding(&while_stmt.body.stmts, binding)
        }
        HirStmt::Repeat(repeat_stmt) => {
            stmt_slice_mentions_binding(&repeat_stmt.body.stmts, binding)
                || expr_uses_binding(&repeat_stmt.cond, binding)
        }
        HirStmt::NumericFor(numeric_for) => {
            TableBinding::Local(numeric_for.binding) == binding
                || expr_uses_binding(&numeric_for.start, binding)
                || expr_uses_binding(&numeric_for.limit, binding)
                || expr_uses_binding(&numeric_for.step, binding)
                || stmt_slice_mentions_binding(&numeric_for.body.stmts, binding)
        }
        HirStmt::GenericFor(generic_for) => {
            generic_for
                .bindings
                .iter()
                .any(|local| TableBinding::Local(*local) == binding)
                || generic_for
                    .iterator
                    .iter()
                    .any(|expr| expr_uses_binding(expr, binding))
                || stmt_slice_mentions_binding(&generic_for.body.stmts, binding)
        }
        HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_) => false,
        HirStmt::Block(block) => stmt_slice_mentions_binding(&block.stmts, binding),
        HirStmt::Unstructured(unstructured) => {
            stmt_slice_mentions_binding(&unstructured.body.stmts, binding)
        }
    }
}

fn is_identifier_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

struct BindingUseCollector<'a> {
    binding_index: &'a mut BindingIndex,
    ids: Vec<BindingId>,
}

impl HirVisitor for BindingUseCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let Some(binding) = binding_from_expr(expr) {
            self.ids.push(self.binding_index.intern(binding));
        }
    }
}

#[derive(Default)]
struct MaterializedBindingCollector {
    counts: BTreeMap<TableBinding, usize>,
}

impl HirVisitor for MaterializedBindingCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl(local_decl) => {
                for binding in &local_decl.bindings {
                    *self
                        .counts
                        .entry(TableBinding::Local(*binding))
                        .or_default() += 1;
                }
            }
            HirStmt::Assign(assign) => {
                for target in &assign.targets {
                    if let Some(binding) = binding_from_lvalue(target) {
                        *self.counts.entry(binding).or_default() += 1;
                    }
                }
            }
            HirStmt::NumericFor(numeric_for) => {
                *self
                    .counts
                    .entry(TableBinding::Local(numeric_for.binding))
                    .or_default() += 1;
            }
            HirStmt::GenericFor(generic_for) => {
                for binding in &generic_for.bindings {
                    *self
                        .counts
                        .entry(TableBinding::Local(*binding))
                        .or_default() += 1;
                }
            }
            HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
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
}

fn call_expr_uses_binding(call: &HirCallExpr, binding: TableBinding) -> bool {
    expr_uses_binding(&call.callee, binding)
        || call.args.iter().any(|arg| expr_uses_binding(arg, binding))
}

fn decision_target_uses_binding(target: &HirDecisionTarget, binding: TableBinding) -> bool {
    match target {
        HirDecisionTarget::Expr(expr) => expr_uses_binding(expr, binding),
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
    }
}

fn table_key_uses_binding(key: &HirTableKey, binding: TableBinding) -> bool {
    match key {
        HirTableKey::Name(_) => false,
        HirTableKey::Expr(expr) => expr_uses_binding(expr, binding),
    }
}
