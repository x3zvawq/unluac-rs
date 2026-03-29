//! 这个子模块负责 `function_sugar` 的只读事实收集。
//!
//! 它依赖 AST 已经合法化后的函数声明/调用形状，只收集 method field 名称，不会在这里
//! 直接改写语句。
//! 例如：`function t:x() end` 会在这里把 `x` 记录成 method field 证据。

use std::collections::BTreeSet;

use crate::ast::common::{AstBlock, AstCallKind, AstExpr, AstFunctionName, AstModule, AstStmt};

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
        if let AstCallKind::MethodCall(call) = call {
            self.fields.insert(call.method.clone());
        }
    }

    fn visit_expr(&mut self, expr: &AstExpr) {
        if let AstExpr::MethodCall(call) = expr {
            self.fields.insert(call.method.clone());
        }
    }
}
