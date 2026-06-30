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

use std::collections::BTreeSet;

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

        rewrite_function_block(block, &temps);
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
            | AstStmt::Label(_)
            | AstStmt::Error(_) => {}
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

fn rewrite_function_block(block: &mut AstBlock, temps: &BTreeSet<TempId>) {
    for stmt in &mut block.stmts {
        rewrite_function_stmt(stmt, temps);
    }
}

fn rewrite_function_stmt(stmt: &mut AstStmt, temps: &BTreeSet<TempId>) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &mut local_decl.bindings {
                if let AstBindingRef::Temp(temp) = binding.id
                    && temps.contains(&temp)
                {
                    binding.id = AstBindingRef::SyntheticLocal(AstSyntheticLocalId(temp));
                }
            }
            for value in &mut local_decl.values {
                rewrite_function_expr(value, temps);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &mut global_decl.values {
                rewrite_function_expr(value, temps);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &mut assign.targets {
                rewrite_function_lvalue(target, temps);
            }
            for value in &mut assign.values {
                rewrite_function_expr(value, temps);
            }
        }
        AstStmt::CallStmt(call_stmt) => rewrite_function_call(&mut call_stmt.call, temps),
        AstStmt::Return(ret) => {
            for value in &mut ret.values {
                rewrite_function_expr(value, temps);
            }
        }
        AstStmt::If(if_stmt) => {
            rewrite_function_expr(&mut if_stmt.cond, temps);
            rewrite_function_block(&mut if_stmt.then_block, temps);
            if let Some(else_block) = &mut if_stmt.else_block {
                rewrite_function_block(else_block, temps);
            }
        }
        AstStmt::While(while_stmt) => {
            rewrite_function_expr(&mut while_stmt.cond, temps);
            rewrite_function_block(&mut while_stmt.body, temps);
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_function_block(&mut repeat_stmt.body, temps);
            rewrite_function_expr(&mut repeat_stmt.cond, temps);
        }
        AstStmt::NumericFor(numeric_for) => {
            rewrite_function_expr(&mut numeric_for.start, temps);
            rewrite_function_expr(&mut numeric_for.limit, temps);
            rewrite_function_expr(&mut numeric_for.step, temps);
            rewrite_function_block(&mut numeric_for.body, temps);
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &mut generic_for.iterator {
                rewrite_function_expr(expr, temps);
            }
            rewrite_function_block(&mut generic_for.body, temps);
        }
        AstStmt::DoBlock(block) => rewrite_function_block(block, temps),
        AstStmt::FunctionDecl(function_decl) => {
            rewrite_function_name(&mut function_decl.target, temps)
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            if let AstBindingRef::Temp(temp) = local_function_decl.name
                && temps.contains(&temp)
            {
                local_function_decl.name = AstBindingRef::SyntheticLocal(AstSyntheticLocalId(temp));
            }
        }
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => {}
    }
}

fn rewrite_function_name(
    target: &mut super::super::common::AstFunctionName,
    temps: &BTreeSet<TempId>,
) {
    let path = match target {
        super::super::common::AstFunctionName::Plain(path) => path,
        super::super::common::AstFunctionName::Method(path, _) => path,
    };
    rewrite_name_ref(&mut path.root, temps);
}

fn rewrite_function_call(call: &mut AstCallKind, temps: &BTreeSet<TempId>) {
    match call {
        AstCallKind::Call(call) => {
            rewrite_function_expr(&mut call.callee, temps);
            for arg in &mut call.args {
                rewrite_function_expr(arg, temps);
            }
        }
        AstCallKind::MethodCall(call) => {
            rewrite_function_expr(&mut call.receiver, temps);
            for arg in &mut call.args {
                rewrite_function_expr(arg, temps);
            }
        }
    }
}

fn rewrite_function_lvalue(target: &mut AstLValue, temps: &BTreeSet<TempId>) {
    match target {
        AstLValue::Name(name) => rewrite_name_ref(name, temps),
        AstLValue::FieldAccess(access) => rewrite_function_expr(&mut access.base, temps),
        AstLValue::IndexAccess(access) => {
            rewrite_function_expr(&mut access.base, temps);
            rewrite_function_expr(&mut access.index, temps);
        }
    }
}

fn rewrite_function_expr(expr: &mut AstExpr, temps: &BTreeSet<TempId>) {
    match expr {
        AstExpr::Var(name) => rewrite_name_ref(name, temps),
        AstExpr::FieldAccess(access) => rewrite_function_expr(&mut access.base, temps),
        AstExpr::IndexAccess(access) => {
            rewrite_function_expr(&mut access.base, temps);
            rewrite_function_expr(&mut access.index, temps);
        }
        AstExpr::Unary(unary) => rewrite_function_expr(&mut unary.expr, temps),
        AstExpr::Binary(binary) => {
            rewrite_function_expr(&mut binary.lhs, temps);
            rewrite_function_expr(&mut binary.rhs, temps);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_function_expr(&mut logical.lhs, temps);
            rewrite_function_expr(&mut logical.rhs, temps);
        }
        AstExpr::Call(call) => {
            rewrite_function_expr(&mut call.callee, temps);
            for arg in &mut call.args {
                rewrite_function_expr(arg, temps);
            }
        }
        AstExpr::MethodCall(call) => {
            rewrite_function_expr(&mut call.receiver, temps);
            for arg in &mut call.args {
                rewrite_function_expr(arg, temps);
            }
        }
        AstExpr::SingleValue(expr) => rewrite_function_expr(expr, temps),
        AstExpr::TableConstructor(table) => {
            for field in &mut table.fields {
                match field {
                    AstTableField::Array(value) => rewrite_function_expr(value, temps),
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            rewrite_function_expr(key, temps);
                        }
                        rewrite_function_expr(&mut record.value, temps);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(function) => {
            rewrite_function_capture_bindings(function, temps);
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

fn rewrite_name_ref(name: &mut AstNameRef, temps: &BTreeSet<TempId>) {
    if let AstNameRef::Temp(temp) = name
        && temps.contains(temp)
    {
        *name = AstNameRef::SyntheticLocal(AstSyntheticLocalId(*temp));
    }
}

fn rewrite_function_capture_bindings(function: &mut AstFunctionExpr, temps: &BTreeSet<TempId>) {
    if function.captured_bindings.is_empty() {
        return;
    }
    function.captured_bindings = function
        .captured_bindings
        .iter()
        .map(|binding| match binding {
            AstBindingRef::Temp(temp) if temps.contains(temp) => {
                AstBindingRef::SyntheticLocal(AstSyntheticLocalId(*temp))
            }
            AstBindingRef::Temp(temp) => AstBindingRef::Temp(*temp),
            _ => *binding,
        })
        .collect();
}
