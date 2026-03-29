//! 这个文件负责把最终仍然泄漏到 AST 层的 temp 身份物化成保守 synthetic local。
//!
//! 理想情况下，前层应该尽量在 HIR/AST build 阶段就把源码绑定恢复干净；但如果某些
//! temp 直到 Readability 结束前仍然存在，这里会把它们显式落成 AST 自己的
//! synthetic local，避免 Generate 再去猜。它不会把 temp 强行美化成本地源码变量，
//! 只负责把“无法继续隐藏的 temp”稳定表达出来。
//!
//! 例子：
//! - `t0 = f(); return t0` 会物化成一个 synthetic local，再由后续 pass/Generate
//!   稳定输出，而不是把裸 `t0` 留到最终代码
//! - 命名 vararg、capture binding、函数名路径里残留的 temp 也会一起收成
//!   synthetic local 身份

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::TempId;

use super::super::common::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstModule,
    AstNameRef, AstStmt, AstSyntheticLocalId, AstTableField, AstTableKey,
};
use super::ReadabilityContext;
use super::visit::{self, AstVisitor};
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    walk::rewrite_module(module, &mut MaterializeTempsPass)
}

struct MaterializeTempsPass;

impl AstRewritePass for MaterializeTempsPass {
    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        let temps = collect_function_temps_in_block(block);
        if temps.is_empty() {
            return false;
        }

        let mapping = temps
            .into_iter()
            .map(|temp| (temp, AstSyntheticLocalId(temp)))
            .collect::<BTreeMap<_, _>>();
        rewrite_function_block(block, &mapping);
        true
    }
}

fn collect_function_temps_in_block(block: &AstBlock) -> BTreeSet<TempId> {
    let mut collector = FunctionTempCollector::default();
    visit::visit_block(block, &mut collector);
    collector.temps
}

#[derive(Default)]
struct FunctionTempCollector {
    temps: BTreeSet<TempId>,
}

impl AstVisitor for FunctionTempCollector {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::LocalDecl(local_decl) => {
                for binding in &local_decl.bindings {
                    if let AstBindingRef::Temp(temp) = binding.id {
                        self.temps.insert(temp);
                    }
                }
            }
            AstStmt::FunctionDecl(function_decl) => {
                collect_function_temps_in_function_name(&function_decl.target, &mut self.temps);
            }
            AstStmt::LocalFunctionDecl(local_function_decl) => {
                if let AstBindingRef::Temp(temp) = local_function_decl.name {
                    self.temps.insert(temp);
                }
            }
            AstStmt::NumericFor(numeric_for) => {
                if let AstBindingRef::Temp(temp) = numeric_for.binding {
                    self.temps.insert(temp);
                }
            }
            AstStmt::GenericFor(generic_for) => {
                for binding in &generic_for.bindings {
                    if let AstBindingRef::Temp(temp) = binding {
                        self.temps.insert(*temp);
                    }
                }
            }
            AstStmt::GlobalDecl(_)
            | AstStmt::Assign(_)
            | AstStmt::CallStmt(_)
            | AstStmt::Return(_)
            | AstStmt::If(_)
            | AstStmt::While(_)
            | AstStmt::Repeat(_)
            | AstStmt::DoBlock(_)
            | AstStmt::Break
            | AstStmt::Continue
            | AstStmt::Goto(_)
            | AstStmt::Label(_) => {}
        }
    }

    fn visit_lvalue(&mut self, target: &AstLValue) {
        if let AstLValue::Name(AstNameRef::Temp(temp)) = target {
            self.temps.insert(*temp);
        }
    }

    fn visit_expr(&mut self, expr: &AstExpr) {
        if let AstExpr::Var(AstNameRef::Temp(temp)) = expr {
            self.temps.insert(*temp);
        }
    }

    fn visit_function_expr(&mut self, function: &AstFunctionExpr) -> bool {
        if let Some(AstBindingRef::Temp(temp)) = function.named_vararg {
            self.temps.insert(temp);
        }
        for binding in &function.captured_bindings {
            if let AstBindingRef::Temp(temp) = binding {
                self.temps.insert(*temp);
            }
        }
        false
    }
}

fn collect_function_temps_in_function_name(
    target: &super::super::common::AstFunctionName,
    temps: &mut BTreeSet<TempId>,
) {
    let path = match target {
        super::super::common::AstFunctionName::Plain(path) => path,
        super::super::common::AstFunctionName::Method(path, _) => path,
    };
    if let AstNameRef::Temp(temp) = path.root {
        temps.insert(temp);
    }
}

fn rewrite_function_block(block: &mut AstBlock, mapping: &BTreeMap<TempId, AstSyntheticLocalId>) {
    for stmt in &mut block.stmts {
        rewrite_function_stmt(stmt, mapping);
    }
}

fn rewrite_function_stmt(stmt: &mut AstStmt, mapping: &BTreeMap<TempId, AstSyntheticLocalId>) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &mut local_decl.bindings {
                if let AstBindingRef::Temp(temp) = binding.id
                    && let Some(&synthetic) = mapping.get(&temp)
                {
                    binding.id = AstBindingRef::SyntheticLocal(synthetic);
                }
            }
            for value in &mut local_decl.values {
                rewrite_function_expr(value, mapping);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &mut global_decl.values {
                rewrite_function_expr(value, mapping);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &mut assign.targets {
                rewrite_function_lvalue(target, mapping);
            }
            for value in &mut assign.values {
                rewrite_function_expr(value, mapping);
            }
        }
        AstStmt::CallStmt(call_stmt) => rewrite_function_call(&mut call_stmt.call, mapping),
        AstStmt::Return(ret) => {
            for value in &mut ret.values {
                rewrite_function_expr(value, mapping);
            }
        }
        AstStmt::If(if_stmt) => {
            rewrite_function_expr(&mut if_stmt.cond, mapping);
            rewrite_function_block(&mut if_stmt.then_block, mapping);
            if let Some(else_block) = &mut if_stmt.else_block {
                rewrite_function_block(else_block, mapping);
            }
        }
        AstStmt::While(while_stmt) => {
            rewrite_function_expr(&mut while_stmt.cond, mapping);
            rewrite_function_block(&mut while_stmt.body, mapping);
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_function_block(&mut repeat_stmt.body, mapping);
            rewrite_function_expr(&mut repeat_stmt.cond, mapping);
        }
        AstStmt::NumericFor(numeric_for) => {
            rewrite_function_expr(&mut numeric_for.start, mapping);
            rewrite_function_expr(&mut numeric_for.limit, mapping);
            rewrite_function_expr(&mut numeric_for.step, mapping);
            rewrite_function_block(&mut numeric_for.body, mapping);
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &mut generic_for.iterator {
                rewrite_function_expr(expr, mapping);
            }
            rewrite_function_block(&mut generic_for.body, mapping);
        }
        AstStmt::DoBlock(block) => rewrite_function_block(block, mapping),
        AstStmt::FunctionDecl(function_decl) => {
            rewrite_function_name(&mut function_decl.target, mapping)
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            if let AstBindingRef::Temp(temp) = local_function_decl.name
                && let Some(&synthetic) = mapping.get(&temp)
            {
                local_function_decl.name = AstBindingRef::SyntheticLocal(synthetic);
            }
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
    }
}

fn rewrite_function_name(
    target: &mut super::super::common::AstFunctionName,
    mapping: &BTreeMap<TempId, AstSyntheticLocalId>,
) {
    let path = match target {
        super::super::common::AstFunctionName::Plain(path) => path,
        super::super::common::AstFunctionName::Method(path, _) => path,
    };
    rewrite_name_ref(&mut path.root, mapping);
}

fn rewrite_function_call(call: &mut AstCallKind, mapping: &BTreeMap<TempId, AstSyntheticLocalId>) {
    match call {
        AstCallKind::Call(call) => {
            rewrite_function_expr(&mut call.callee, mapping);
            for arg in &mut call.args {
                rewrite_function_expr(arg, mapping);
            }
        }
        AstCallKind::MethodCall(call) => {
            rewrite_function_expr(&mut call.receiver, mapping);
            for arg in &mut call.args {
                rewrite_function_expr(arg, mapping);
            }
        }
    }
}

fn rewrite_function_lvalue(
    target: &mut AstLValue,
    mapping: &BTreeMap<TempId, AstSyntheticLocalId>,
) {
    match target {
        AstLValue::Name(name) => rewrite_name_ref(name, mapping),
        AstLValue::FieldAccess(access) => rewrite_function_expr(&mut access.base, mapping),
        AstLValue::IndexAccess(access) => {
            rewrite_function_expr(&mut access.base, mapping);
            rewrite_function_expr(&mut access.index, mapping);
        }
    }
}

fn rewrite_function_expr(expr: &mut AstExpr, mapping: &BTreeMap<TempId, AstSyntheticLocalId>) {
    match expr {
        AstExpr::Var(name) => rewrite_name_ref(name, mapping),
        AstExpr::FieldAccess(access) => rewrite_function_expr(&mut access.base, mapping),
        AstExpr::IndexAccess(access) => {
            rewrite_function_expr(&mut access.base, mapping);
            rewrite_function_expr(&mut access.index, mapping);
        }
        AstExpr::Unary(unary) => rewrite_function_expr(&mut unary.expr, mapping),
        AstExpr::Binary(binary) => {
            rewrite_function_expr(&mut binary.lhs, mapping);
            rewrite_function_expr(&mut binary.rhs, mapping);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_function_expr(&mut logical.lhs, mapping);
            rewrite_function_expr(&mut logical.rhs, mapping);
        }
        AstExpr::Call(call) => {
            rewrite_function_expr(&mut call.callee, mapping);
            for arg in &mut call.args {
                rewrite_function_expr(arg, mapping);
            }
        }
        AstExpr::MethodCall(call) => {
            rewrite_function_expr(&mut call.receiver, mapping);
            for arg in &mut call.args {
                rewrite_function_expr(arg, mapping);
            }
        }
        AstExpr::SingleValue(expr) => rewrite_function_expr(expr, mapping),
        AstExpr::TableConstructor(table) => {
            for field in &mut table.fields {
                match field {
                    AstTableField::Array(value) => rewrite_function_expr(value, mapping),
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            rewrite_function_expr(key, mapping);
                        }
                        rewrite_function_expr(&mut record.value, mapping);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(function) => {
            rewrite_function_capture_bindings(function, mapping);
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg => {}
    }
}

fn rewrite_name_ref(name: &mut AstNameRef, mapping: &BTreeMap<TempId, AstSyntheticLocalId>) {
    if let AstNameRef::Temp(temp) = name
        && let Some(&synthetic) = mapping.get(temp)
    {
        *name = AstNameRef::SyntheticLocal(synthetic);
    }
}

fn rewrite_function_capture_bindings(
    function: &mut AstFunctionExpr,
    mapping: &BTreeMap<TempId, AstSyntheticLocalId>,
) {
    if function.captured_bindings.is_empty() {
        return;
    }
    function.captured_bindings = function
        .captured_bindings
        .iter()
        .map(|binding| match binding {
            AstBindingRef::Temp(temp) => mapping
                .get(temp)
                .copied()
                .map(AstBindingRef::SyntheticLocal)
                .unwrap_or(AstBindingRef::Temp(*temp)),
            _ => *binding,
        })
        .collect();
}

#[cfg(test)]
mod tests;
