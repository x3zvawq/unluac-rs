//! 这个文件承载 HIR 内部给 simplify 使用的 promotion facts。
//!
//! `locals` pass 只看 HIR 语法本身时，能判断“哪些 temp 正在沿别名链流动”，却不知道
//! “这个 temp 最早来自哪个寄存器槽位”。一旦某个 local 已经被 closure capture，后续
//! 同槽位的新 def 就不该再长成新的 local，而应继续写回原绑定。
//!
//! 这里专门把那份“temp -> home slot”事实从 analyze 阶段带给 simplify：
//! - 它依赖 Dataflow 已经给出的 fixed def/reg 身份
//! - 它不会重新做结构恢复，也不会把事实暴露成公开 HIR API
//! - 例子：`t0(slot 0)` 被闭包 capture 之后，后续 `t7(slot 0)` 会被 locals 认成同一
//!   个源码 local 的写回，而不是新的 `local l3 = ...`

use crate::cfg::DataflowFacts;
use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirStmt, HirTableField, HirTableKey, TempId,
};
use std::collections::BTreeSet;

/// 单个 proto 的 temp promotion 辅助事实。
#[derive(Debug, Clone, Default)]
pub(super) struct ProtoPromotionFacts {
    temp_home_slots: Vec<Option<usize>>,
}

impl ProtoPromotionFacts {
    /// 从 Dataflow 里提取当前 proto 所需的 temp -> home slot 对照表。
    pub(super) fn from_dataflow(dataflow: &DataflowFacts) -> Self {
        let total_temps =
            dataflow.defs.len() + dataflow.open_defs.len() + dataflow.phi_candidates.len();
        let mut temp_home_slots = vec![None; total_temps];

        for def in &dataflow.defs {
            temp_home_slots[def.id.index()] = Some(def.reg.index());
        }

        Self { temp_home_slots }
    }

    /// 返回某个 temp 对应的原始寄存器槽位。
    pub(super) fn home_slot(&self, temp: TempId) -> Option<usize> {
        self.temp_home_slots.get(temp.index()).copied().flatten()
    }

    /// 把当前语句里所有 closure capture 观察到的 home slot 收集进集合。
    pub(super) fn collect_captured_home_slots_in_stmt(
        &self,
        stmt: &HirStmt,
        slots: &mut BTreeSet<usize>,
    ) {
        match stmt {
            HirStmt::LocalDecl(local_decl) => {
                for value in &local_decl.values {
                    self.collect_captured_home_slots_in_expr(value, slots);
                }
            }
            HirStmt::Assign(assign) => {
                for target in &assign.targets {
                    if let HirLValue::TableAccess(access) = target {
                        self.collect_captured_home_slots_in_expr(&access.base, slots);
                        self.collect_captured_home_slots_in_expr(&access.key, slots);
                    }
                }
                for value in &assign.values {
                    self.collect_captured_home_slots_in_expr(value, slots);
                }
            }
            HirStmt::TableSetList(set_list) => {
                self.collect_captured_home_slots_in_expr(&set_list.base, slots);
                for value in &set_list.values {
                    self.collect_captured_home_slots_in_expr(value, slots);
                }
                if let Some(trailing) = &set_list.trailing_multivalue {
                    self.collect_captured_home_slots_in_expr(trailing, slots);
                }
            }
            HirStmt::ErrNil(err_nil) => {
                self.collect_captured_home_slots_in_expr(&err_nil.value, slots);
            }
            HirStmt::ToBeClosed(to_be_closed) => {
                self.collect_captured_home_slots_in_expr(&to_be_closed.value, slots);
            }
            HirStmt::CallStmt(call_stmt) => {
                self.collect_captured_home_slots_in_expr(&call_stmt.call.callee, slots);
                for arg in &call_stmt.call.args {
                    self.collect_captured_home_slots_in_expr(arg, slots);
                }
            }
            HirStmt::Return(ret) => {
                for value in &ret.values {
                    self.collect_captured_home_slots_in_expr(value, slots);
                }
            }
            HirStmt::If(if_stmt) => {
                self.collect_captured_home_slots_in_expr(&if_stmt.cond, slots);
                self.collect_captured_home_slots_in_block(&if_stmt.then_block, slots);
                if let Some(else_block) = &if_stmt.else_block {
                    self.collect_captured_home_slots_in_block(else_block, slots);
                }
            }
            HirStmt::While(while_stmt) => {
                self.collect_captured_home_slots_in_expr(&while_stmt.cond, slots);
                self.collect_captured_home_slots_in_block(&while_stmt.body, slots);
            }
            HirStmt::Repeat(repeat_stmt) => {
                self.collect_captured_home_slots_in_block(&repeat_stmt.body, slots);
                self.collect_captured_home_slots_in_expr(&repeat_stmt.cond, slots);
            }
            HirStmt::NumericFor(numeric_for) => {
                self.collect_captured_home_slots_in_expr(&numeric_for.start, slots);
                self.collect_captured_home_slots_in_expr(&numeric_for.limit, slots);
                self.collect_captured_home_slots_in_expr(&numeric_for.step, slots);
                self.collect_captured_home_slots_in_block(&numeric_for.body, slots);
            }
            HirStmt::GenericFor(generic_for) => {
                for iterator in &generic_for.iterator {
                    self.collect_captured_home_slots_in_expr(iterator, slots);
                }
                self.collect_captured_home_slots_in_block(&generic_for.body, slots);
            }
            HirStmt::Block(block) => self.collect_captured_home_slots_in_block(block, slots),
            HirStmt::Unstructured(unstructured) => {
                self.collect_captured_home_slots_in_block(&unstructured.body, slots);
            }
            HirStmt::Break
            | HirStmt::Close(_)
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }

    /// 只收集在进入嵌套 block 之前就会执行到的 capture。
    pub(super) fn collect_prefix_captured_home_slots_in_stmt(
        &self,
        stmt: &HirStmt,
        slots: &mut BTreeSet<usize>,
    ) {
        match stmt {
            HirStmt::If(if_stmt) => self.collect_captured_home_slots_in_expr(&if_stmt.cond, slots),
            HirStmt::While(while_stmt) => {
                self.collect_captured_home_slots_in_expr(&while_stmt.cond, slots);
            }
            HirStmt::NumericFor(numeric_for) => {
                self.collect_captured_home_slots_in_expr(&numeric_for.start, slots);
                self.collect_captured_home_slots_in_expr(&numeric_for.limit, slots);
                self.collect_captured_home_slots_in_expr(&numeric_for.step, slots);
            }
            HirStmt::GenericFor(generic_for) => {
                for iterator in &generic_for.iterator {
                    self.collect_captured_home_slots_in_expr(iterator, slots);
                }
            }
            HirStmt::LocalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::Repeat(_)
            | HirStmt::Block(_)
            | HirStmt::Unstructured(_)
            | HirStmt::Break
            | HirStmt::Close(_)
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }

    fn collect_captured_home_slots_in_block(&self, block: &HirBlock, slots: &mut BTreeSet<usize>) {
        for stmt in &block.stmts {
            self.collect_captured_home_slots_in_stmt(stmt, slots);
        }
    }

    fn collect_captured_home_slots_in_expr(&self, expr: &HirExpr, slots: &mut BTreeSet<usize>) {
        match expr {
            HirExpr::TableAccess(access) => {
                self.collect_captured_home_slots_in_expr(&access.base, slots);
                self.collect_captured_home_slots_in_expr(&access.key, slots);
            }
            HirExpr::Unary(unary) => self.collect_captured_home_slots_in_expr(&unary.expr, slots),
            HirExpr::Binary(binary) => {
                self.collect_captured_home_slots_in_expr(&binary.lhs, slots);
                self.collect_captured_home_slots_in_expr(&binary.rhs, slots);
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.collect_captured_home_slots_in_expr(&logical.lhs, slots);
                self.collect_captured_home_slots_in_expr(&logical.rhs, slots);
            }
            HirExpr::Decision(decision) => {
                for node in &decision.nodes {
                    self.collect_captured_home_slots_in_expr(&node.test, slots);
                    self.collect_captured_home_slots_in_decision_target(&node.truthy, slots);
                    self.collect_captured_home_slots_in_decision_target(&node.falsy, slots);
                }
            }
            HirExpr::Call(call) => {
                self.collect_captured_home_slots_in_expr(&call.callee, slots);
                for arg in &call.args {
                    self.collect_captured_home_slots_in_expr(arg, slots);
                }
            }
            HirExpr::TableConstructor(table) => {
                for field in &table.fields {
                    match field {
                        HirTableField::Array(value) => {
                            self.collect_captured_home_slots_in_expr(value, slots);
                        }
                        HirTableField::Record(field) => {
                            if let HirTableKey::Expr(key) = &field.key {
                                self.collect_captured_home_slots_in_expr(key, slots);
                            }
                            self.collect_captured_home_slots_in_expr(&field.value, slots);
                        }
                    }
                }
                if let Some(trailing) = &table.trailing_multivalue {
                    self.collect_captured_home_slots_in_expr(trailing, slots);
                }
            }
            HirExpr::Closure(closure) => {
                for capture in &closure.captures {
                    self.collect_temp_home_slots_in_expr(&capture.value, slots);
                    self.collect_captured_home_slots_in_expr(&capture.value, slots);
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
            | HirExpr::TempRef(_)
            | HirExpr::GlobalRef(_)
            | HirExpr::VarArg
            | HirExpr::Unresolved(_) => {}
        }
    }

    fn collect_captured_home_slots_in_decision_target(
        &self,
        target: &crate::hir::common::HirDecisionTarget,
        slots: &mut BTreeSet<usize>,
    ) {
        if let crate::hir::common::HirDecisionTarget::Expr(expr) = target {
            self.collect_captured_home_slots_in_expr(expr, slots);
        }
    }

    fn collect_temp_home_slots_in_expr(&self, expr: &HirExpr, slots: &mut BTreeSet<usize>) {
        match expr {
            HirExpr::TempRef(temp) => {
                if let Some(slot) = self.home_slot(*temp) {
                    slots.insert(slot);
                }
            }
            HirExpr::TableAccess(access) => {
                self.collect_temp_home_slots_in_expr(&access.base, slots);
                self.collect_temp_home_slots_in_expr(&access.key, slots);
            }
            HirExpr::Unary(unary) => self.collect_temp_home_slots_in_expr(&unary.expr, slots),
            HirExpr::Binary(binary) => {
                self.collect_temp_home_slots_in_expr(&binary.lhs, slots);
                self.collect_temp_home_slots_in_expr(&binary.rhs, slots);
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.collect_temp_home_slots_in_expr(&logical.lhs, slots);
                self.collect_temp_home_slots_in_expr(&logical.rhs, slots);
            }
            HirExpr::Decision(decision) => {
                for node in &decision.nodes {
                    self.collect_temp_home_slots_in_expr(&node.test, slots);
                    self.collect_temp_home_slots_in_decision_target(&node.truthy, slots);
                    self.collect_temp_home_slots_in_decision_target(&node.falsy, slots);
                }
            }
            HirExpr::Call(call) => {
                self.collect_temp_home_slots_in_expr(&call.callee, slots);
                for arg in &call.args {
                    self.collect_temp_home_slots_in_expr(arg, slots);
                }
            }
            HirExpr::TableConstructor(table) => {
                for field in &table.fields {
                    match field {
                        HirTableField::Array(value) => {
                            self.collect_temp_home_slots_in_expr(value, slots);
                        }
                        HirTableField::Record(field) => {
                            if let HirTableKey::Expr(key) = &field.key {
                                self.collect_temp_home_slots_in_expr(key, slots);
                            }
                            self.collect_temp_home_slots_in_expr(&field.value, slots);
                        }
                    }
                }
                if let Some(trailing) = &table.trailing_multivalue {
                    self.collect_temp_home_slots_in_expr(trailing, slots);
                }
            }
            HirExpr::Closure(closure) => {
                for capture in &closure.captures {
                    self.collect_temp_home_slots_in_expr(&capture.value, slots);
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

    fn collect_temp_home_slots_in_decision_target(
        &self,
        target: &crate::hir::common::HirDecisionTarget,
        slots: &mut BTreeSet<usize>,
    ) {
        if let crate::hir::common::HirDecisionTarget::Expr(expr) = target {
            self.collect_temp_home_slots_in_expr(expr, slots);
        }
    }

    #[cfg(test)]
    pub(super) fn for_test(temp_home_slots: Vec<Option<usize>>) -> Self {
        Self { temp_home_slots }
    }
}
