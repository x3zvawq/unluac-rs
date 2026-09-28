//! 按已有调用提示选择函数声明风格。
//!
//! 消费 HIR 参数身份与最终 AST 可见性，保持隐式 self 的词法合法性。

use std::{collections::BTreeSet, ops::ControlFlow};

use crate::ast::readability::walk::{self, AstRewritePass};
use crate::ast::visit::{AstVisitor, NameAccess, visit_block};
use crate::ast::{AstCallKind, AstExpr, AstFunctionName, AstModule, AstNameRef, AstStmt};

pub(super) fn apply(module: &mut AstModule) -> bool {
    let mut hints = MethodNames::default();
    visit_block(&module.body, &mut hints);
    walk::rewrite_module(module, &mut hints)
}

#[derive(Default)]
struct MethodNames(BTreeSet<String>);

impl AstVisitor for MethodNames {
    fn visit_expr(&mut self, expr: &AstExpr) {
        let key = match expr {
            AstExpr::MethodCall(call) => Some(call.method.as_str()),
            AstExpr::Call(call) => call.method_key.as_ref().and_then(crate::LuaString::as_utf8),
            _ => None,
        };
        if let Some(key) = key {
            self.0.insert(key.to_owned());
        }
    }

    fn visit_call(&mut self, call: &AstCallKind) {
        let key = match call {
            AstCallKind::MethodCall(call) => Some(call.method.as_str()),
            AstCallKind::Call(call) => call.method_key.as_ref().and_then(crate::LuaString::as_utf8),
        };
        if let Some(key) = key {
            self.0.insert(key.to_owned());
        }
    }
}

impl AstRewritePass for MethodNames {
    fn rewrite_stmt(&mut self, stmt: &mut AstStmt) -> bool {
        let AstStmt::FunctionDecl(decl) = stmt else {
            return false;
        };
        let AstFunctionName::Plain(path) = &decl.target else {
            return false;
        };
        if !decl.func.allows_self_param
            || !path.fields.last().is_some_and(|key| self.0.contains(key))
        {
            return false;
        }
        let mut free_self = FreeSelf(false);
        visit_block(&decl.func.body, &mut free_self);
        if free_self.0 {
            // 候选拒绝[SemanticBarrier:BindingIdentity]：隐式参数会遮蔽后代访问的全局 self（regress_333）。
            return false;
        }
        let mut path = path.clone();
        let method = path.fields.pop().expect("method hint requires a field");
        decl.target = AstFunctionName::Method(path, method);
        true
    }
}

struct FreeSelf(bool);

impl AstVisitor for FreeSelf {
    fn visit_name(&mut self, name: &AstNameRef, _access: NameAccess) -> ControlFlow<()> {
        if matches!(name, AstNameRef::Global(global) if global.text == "self") {
            self.0 = true;
            ControlFlow::Break(())
        } else {
            ControlFlow::Continue(())
        }
    }
}
