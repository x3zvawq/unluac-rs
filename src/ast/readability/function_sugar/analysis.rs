//! 这个子模块负责 `function_sugar` 的只读事实收集。
//!
//! 它依赖 AST 已经合法化后的函数声明/调用形状，只收集 method field 名称，不会在这里
//! 直接改写语句。普通 `Call` 上由 HIR 保留的 `method_name` 也属于同一份 provenance。
//! 例如：`function t:x() end` 会在这里把 `x` 记录成 method field 证据。

use std::collections::BTreeSet;

use crate::ast::common::{
    AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstGlobalBindingTarget,
    AstLValue, AstModule, AstNameRef, AstStmt,
};

use super::super::visit::{self, AstVisitor};

pub(super) fn collect_method_field_names(module: &AstModule) -> BTreeSet<String> {
    let mut visitor = MethodFieldCollector::default();
    visit::visit_module(module, &mut visitor);
    visitor.fields
}

pub(super) fn collect_method_field_names_in_block(block: &AstBlock, fields: &mut BTreeSet<String>) {
    let mut visitor = MethodFieldCollector {
        fields: std::mem::take(fields),
    };
    visit::visit_block(block, &mut visitor);
    *fields = visitor.fields;
}

pub(super) fn function_uses_global_name(function: &AstFunctionExpr, name: &str) -> bool {
    let mut visitor = GlobalNameFinder { name, found: false };
    visit::visit_block(&function.body, &mut visitor);
    visitor.found
}

struct GlobalNameFinder<'a> {
    name: &'a str,
    found: bool,
}

impl AstVisitor for GlobalNameFinder<'_> {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::GlobalDecl(decl) => {
                self.found |= decl.bindings.iter().any(|binding| {
                    matches!(&binding.target, AstGlobalBindingTarget::Name(global) if global.text == self.name)
                });
            }
            AstStmt::FunctionDecl(decl) => {
                let path = match &decl.target {
                    AstFunctionName::Plain(path) | AstFunctionName::Method(path, _) => path,
                };
                self.found |=
                    matches!(&path.root, AstNameRef::Global(global) if global.text == self.name);
            }
            _ => {}
        }
    }

    fn visit_expr(&mut self, expr: &AstExpr) {
        if matches!(expr, AstExpr::Var(AstNameRef::Global(global)) if global.text == self.name) {
            self.found = true;
        }
    }

    fn visit_lvalue(&mut self, lvalue: &AstLValue) {
        if matches!(lvalue, AstLValue::Name(AstNameRef::Global(global)) if global.text == self.name)
        {
            self.found = true;
        }
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}

#[derive(Default)]
struct MethodFieldCollector {
    fields: BTreeSet<String>,
}

impl AstVisitor for MethodFieldCollector {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        if let AstStmt::FunctionDecl(function_decl) = stmt
            && let AstFunctionName::Method(_, method) = &function_decl.target
        {
            self.fields.insert(method.clone());
        }
    }

    fn visit_call(&mut self, call: &AstCallKind) {
        match call {
            AstCallKind::MethodCall(call) => {
                self.fields.insert(call.method.clone());
            }
            AstCallKind::Call(call) => {
                if let Some(method) = &call.method_name {
                    self.fields.insert(method.clone());
                }
            }
        }
    }

    fn visit_expr(&mut self, expr: &AstExpr) {
        match expr {
            AstExpr::MethodCall(call) => {
                self.fields.insert(call.method.clone());
            }
            AstExpr::Call(call) => {
                if let Some(method) = &call.method_name {
                    self.fields.insert(method.clone());
                }
            }
            _ => {}
        }
    }
}
