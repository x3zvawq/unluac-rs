//! 这个文件负责从最终 AST 收集 naming 需要的“成品结构事实”。
//!
//! Naming 发生在 Readability 之后，所以像“哪些 binding 还真实留在 AST 里”
//! “哪些 synthetic local 最终其实只是丢弃位”这类信息，不能再靠 HIR/Raw 的原始槽位推断。
//! 这里直接基于最终 AST 建一份轻量事实表，让命名阶段能按成品结构做决定。

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue,
    AstModule, AstNameRef, AstStmt, AstSyntheticLocalId, AstTableField, AstTableKey,
};
use crate::hir::{HirModule, HirProtoRef};

#[derive(Debug, Clone, Default)]
pub(super) struct AstNamingFacts {
    pub(super) functions: Vec<FunctionAstNamingFacts>,
}

#[derive(Debug, Clone, Default)]
pub(super) struct FunctionAstNamingFacts {
    pub(super) debug_like_binding_order: BTreeMap<AstBindingRef, usize>,
    pub(super) unused_synthetic_locals: BTreeSet<AstSyntheticLocalId>,
}

pub(super) fn collect_ast_naming_facts(module: &AstModule, hir: &HirModule) -> AstNamingFacts {
    let mut facts = AstNamingFacts {
        functions: vec![FunctionAstNamingFacts::default(); hir.protos.len()],
    };
    collect_function_facts(module.entry_function, &module.body, &mut facts);
    facts
}

#[derive(Debug, Default)]
struct FunctionAstCollector {
    binding_order: Vec<AstBindingRef>,
    seen_bindings: BTreeSet<AstBindingRef>,
    declared_synthetic_locals: BTreeSet<AstSyntheticLocalId>,
    mentioned_synthetic_locals: BTreeSet<AstSyntheticLocalId>,
}

impl FunctionAstCollector {
    fn note_binding(&mut self, binding: AstBindingRef) {
        if self.seen_bindings.insert(binding) {
            self.binding_order.push(binding);
        }
        if let AstBindingRef::SyntheticLocal(local) = binding {
            self.declared_synthetic_locals.insert(local);
        }
    }

    fn note_name_ref(&mut self, name: &AstNameRef) {
        match name {
            AstNameRef::Local(local) => self.note_binding(AstBindingRef::Local(*local)),
            AstNameRef::SyntheticLocal(local) => {
                self.note_binding(AstBindingRef::SyntheticLocal(*local));
                self.mentioned_synthetic_locals.insert(*local);
            }
            AstNameRef::Param(_)
            | AstNameRef::Temp(_)
            | AstNameRef::Upvalue(_)
            | AstNameRef::Global(_) => {}
        }
    }

    fn finish(self) -> FunctionAstNamingFacts {
        let debug_like_binding_order = self
            .binding_order
            .into_iter()
            .enumerate()
            .map(|(index, binding)| (binding, index))
            .collect();
        let unused_synthetic_locals = self
            .declared_synthetic_locals
            .difference(&self.mentioned_synthetic_locals)
            .copied()
            .collect();

        FunctionAstNamingFacts {
            debug_like_binding_order,
            unused_synthetic_locals,
        }
    }
}

fn collect_function_facts(function: HirProtoRef, body: &AstBlock, facts: &mut AstNamingFacts) {
    let mut collector = FunctionAstCollector::default();
    collect_block_facts(body, &mut collector, facts);
    facts.functions[function.index()] = collector.finish();
}

fn collect_block_facts(
    block: &AstBlock,
    collector: &mut FunctionAstCollector,
    facts: &mut AstNamingFacts,
) {
    for stmt in &block.stmts {
        collect_stmt_facts(stmt, collector, facts);
    }
}

fn collect_stmt_facts(
    stmt: &AstStmt,
    collector: &mut FunctionAstCollector,
    facts: &mut AstNamingFacts,
) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                collector.note_binding(binding.id);
            }
            for value in &local_decl.values {
                collect_expr_facts(value, collector, facts);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_expr_facts(value, collector, facts);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_facts(target, collector, facts);
            }
            for value in &assign.values {
                collect_expr_facts(value, collector, facts);
            }
        }
        AstStmt::CallStmt(call_stmt) => collect_call_facts(&call_stmt.call, collector, facts),
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_facts(value, collector, facts);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_expr_facts(&if_stmt.cond, collector, facts);
            collect_block_facts(&if_stmt.then_block, collector, facts);
            if let Some(else_block) = &if_stmt.else_block {
                collect_block_facts(else_block, collector, facts);
            }
        }
        AstStmt::While(while_stmt) => {
            collect_expr_facts(&while_stmt.cond, collector, facts);
            collect_block_facts(&while_stmt.body, collector, facts);
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_block_facts(&repeat_stmt.body, collector, facts);
            collect_expr_facts(&repeat_stmt.cond, collector, facts);
        }
        AstStmt::NumericFor(numeric_for) => {
            collector.note_binding(numeric_for.binding);
            collect_expr_facts(&numeric_for.start, collector, facts);
            collect_expr_facts(&numeric_for.limit, collector, facts);
            collect_expr_facts(&numeric_for.step, collector, facts);
            collect_block_facts(&numeric_for.body, collector, facts);
        }
        AstStmt::GenericFor(generic_for) => {
            for &binding in &generic_for.bindings {
                collector.note_binding(binding);
            }
            for expr in &generic_for.iterator {
                collect_expr_facts(expr, collector, facts);
            }
            collect_block_facts(&generic_for.body, collector, facts);
        }
        AstStmt::DoBlock(block) => collect_block_facts(block, collector, facts),
        AstStmt::FunctionDecl(function_decl) => {
            collect_function_name_facts(&function_decl.target, collector);
            collect_nested_function_facts(&function_decl.func, facts);
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            collector.note_binding(local_function_decl.name);
            collect_nested_function_facts(&local_function_decl.func, facts);
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
    }
}

fn collect_nested_function_facts(function_expr: &AstFunctionExpr, facts: &mut AstNamingFacts) {
    collect_function_facts(function_expr.function, &function_expr.body, facts);
}

fn collect_function_name_facts(target: &AstFunctionName, collector: &mut FunctionAstCollector) {
    let path = match target {
        AstFunctionName::Plain(path) => path,
        AstFunctionName::Method(path, _) => path,
    };
    collector.note_name_ref(&path.root);
}

fn collect_call_facts(
    call: &AstCallKind,
    collector: &mut FunctionAstCollector,
    facts: &mut AstNamingFacts,
) {
    match call {
        AstCallKind::Call(call) => {
            collect_expr_facts(&call.callee, collector, facts);
            for arg in &call.args {
                collect_expr_facts(arg, collector, facts);
            }
        }
        AstCallKind::MethodCall(call) => {
            collect_expr_facts(&call.receiver, collector, facts);
            for arg in &call.args {
                collect_expr_facts(arg, collector, facts);
            }
        }
    }
}

fn collect_lvalue_facts(
    target: &AstLValue,
    collector: &mut FunctionAstCollector,
    facts: &mut AstNamingFacts,
) {
    match target {
        AstLValue::Name(name) => collector.note_name_ref(name),
        AstLValue::FieldAccess(access) => collect_expr_facts(&access.base, collector, facts),
        AstLValue::IndexAccess(access) => {
            collect_expr_facts(&access.base, collector, facts);
            collect_expr_facts(&access.index, collector, facts);
        }
    }
}

fn collect_expr_facts(
    expr: &AstExpr,
    collector: &mut FunctionAstCollector,
    facts: &mut AstNamingFacts,
) {
    match expr {
        AstExpr::Var(name) => collector.note_name_ref(name),
        AstExpr::FieldAccess(access) => collect_expr_facts(&access.base, collector, facts),
        AstExpr::IndexAccess(access) => {
            collect_expr_facts(&access.base, collector, facts);
            collect_expr_facts(&access.index, collector, facts);
        }
        AstExpr::Unary(unary) => collect_expr_facts(&unary.expr, collector, facts),
        AstExpr::Binary(binary) => {
            collect_expr_facts(&binary.lhs, collector, facts);
            collect_expr_facts(&binary.rhs, collector, facts);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_expr_facts(&logical.lhs, collector, facts);
            collect_expr_facts(&logical.rhs, collector, facts);
        }
        AstExpr::Call(call) => {
            collect_expr_facts(&call.callee, collector, facts);
            for arg in &call.args {
                collect_expr_facts(arg, collector, facts);
            }
        }
        AstExpr::MethodCall(call) => {
            collect_expr_facts(&call.receiver, collector, facts);
            for arg in &call.args {
                collect_expr_facts(arg, collector, facts);
            }
        }
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    AstTableField::Array(value) => collect_expr_facts(value, collector, facts),
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &record.key {
                            collect_expr_facts(key, collector, facts);
                        }
                        collect_expr_facts(&record.value, collector, facts);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(function_expr) => collect_nested_function_facts(function_expr, facts),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::VarArg => {}
    }
}
