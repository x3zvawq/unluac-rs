//! `installer_iife`：把“匿名安装器立即调用”从合法 AST 收回成可读性更稳定的局部名。
//!
//! 这个 pass 只处理形如 `(function(x) emit = ... end)(arg)` 的直接调用：
//! 它会把输入
//! ` (function(x) emit = x end)("ax") `
//! 收成
//! ` local l0 = function(x) emit = x end; l0("ax") `
//! 然后交给后面的 `function_sugar` 再决定是否继续变成 `local function l0(x) ... end`。
//!
//! 它依赖 AST build 已经把直接调用的 callee 落成合法 `FunctionExpr`，也依赖
//! `materialize-temps` 先把 AST 自己残留的 temp 物化掉，这样这里新增的名字只需要走
//! synthetic-local 命名空间，不会越权复用前层 temp。
//!
//! 它不负责：
//! - 判断 forwarded multiret / final-call-arg 这类语义约束，它们仍属于 AST build；
//! - 把这个局部函数进一步降成方法声明或 `local function`，那属于 `function_sugar`。

use crate::ast::common::{
    AstBindingRef, AstBlock, AstCallExpr, AstCallKind, AstCallStmt, AstExpr, AstFunctionExpr,
    AstFunctionName, AstLValue, AstLocalAttr, AstLocalBinding, AstLocalDecl, AstLocalOrigin,
    AstModule, AstNamePath, AstNameRef, AstStmt, AstSyntheticLocalId,
};
use crate::hir::TempId;

use super::ReadabilityContext;
use super::visit::{self, AstVisitor};
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    walk::rewrite_module(module, &mut InstallerIifePass)
}

struct InstallerIifePass;

impl AstRewritePass for InstallerIifePass {
    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        let mut next_synthetic_local = next_synthetic_local_index_in_block(block);
        let mut changed = false;
        let mut index = 0;
        while index < block.stmts.len() {
            let Some(rewritten) =
                rewrite_installer_iife_stmt(&block.stmts[index], &mut next_synthetic_local)
            else {
                index += 1;
                continue;
            };
            block.stmts.splice(index..=index, rewritten);
            changed = true;
            index += 2;
        }
        changed
    }
}

fn rewrite_installer_iife_stmt(
    stmt: &AstStmt,
    next_synthetic_local: &mut usize,
) -> Option<Vec<AstStmt>> {
    let AstStmt::CallStmt(call_stmt) = stmt else {
        return None;
    };
    let AstCallKind::Call(call) = &call_stmt.call else {
        return None;
    };
    let AstExpr::FunctionExpr(function) = &call.callee else {
        return None;
    };
    if !function_expr_looks_like_named_installer(function) {
        return None;
    }

    let binding_id = AstSyntheticLocalId(TempId(*next_synthetic_local));
    *next_synthetic_local += 1;

    Some(vec![
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: AstBindingRef::SyntheticLocal(binding_id),
                attr: AstLocalAttr::None,
                origin: AstLocalOrigin::Recovered,
            }],
            values: vec![AstExpr::FunctionExpr(function.clone())],
        })),
        AstStmt::CallStmt(Box::new(AstCallStmt {
            call: AstCallKind::Call(Box::new(AstCallExpr {
                callee: AstExpr::Var(AstNameRef::SyntheticLocal(binding_id)),
                args: call.args.clone(),
            })),
        })),
    ])
}

fn next_synthetic_local_index_in_block(block: &AstBlock) -> usize {
    let mut collector = SyntheticLocalCollector::default();
    visit::visit_block(block, &mut collector);
    collector.next
}

#[derive(Default)]
struct SyntheticLocalCollector {
    next: usize,
}

impl AstVisitor for SyntheticLocalCollector {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::LocalDecl(local_decl) => {
                for binding in &local_decl.bindings {
                    self.collect_binding_ref(binding.id);
                }
            }
            AstStmt::NumericFor(numeric_for) => {
                self.collect_binding_ref(numeric_for.binding);
            }
            AstStmt::GenericFor(generic_for) => {
                for binding in &generic_for.bindings {
                    self.collect_binding_ref(*binding);
                }
            }
            AstStmt::FunctionDecl(function_decl) => {
                self.collect_function_name(&function_decl.target);
            }
            AstStmt::LocalFunctionDecl(function_decl) => {
                self.collect_binding_ref(function_decl.name);
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
        if let AstLValue::Name(name) = target {
            self.collect_name_ref(name);
        }
    }

    fn visit_expr(&mut self, expr: &AstExpr) {
        if let AstExpr::Var(name) = expr {
            self.collect_name_ref(name);
        }
    }

    fn visit_function_expr(&mut self, function: &AstFunctionExpr) -> bool {
        if let Some(vararg) = function.named_vararg {
            self.collect_binding_ref(vararg);
        }
        for binding in &function.captured_bindings {
            self.collect_binding_ref(*binding);
        }
        true
    }
}

impl SyntheticLocalCollector {
    fn collect_function_name(&mut self, target: &AstFunctionName) {
        match target {
            AstFunctionName::Plain(path) => self.collect_name_ref(&path.root),
            AstFunctionName::Method(path, _) => self.collect_name_ref(&path.root),
        }
    }

    fn collect_name_ref(&mut self, name: &AstNameRef) {
        if let AstNameRef::SyntheticLocal(id) = name {
            self.next = self.next.max(id.index() + 1);
        }
    }

    fn collect_binding_ref(&mut self, binding: AstBindingRef) {
        if let AstBindingRef::SyntheticLocal(id) = binding {
            self.next = self.next.max(id.index() + 1);
        }
    }
}

fn function_expr_looks_like_named_installer(function: &AstFunctionExpr) -> bool {
    let [stmt] = function.body.stmts.as_slice() else {
        return false;
    };

    match stmt {
        AstStmt::Assign(assign) if assign.targets.len() == 1 && assign.values.len() == 1 => {
            match (&assign.targets[0], &assign.values[0]) {
                (AstLValue::Name(AstNameRef::Global(name)), AstExpr::Var(AstNameRef::Param(_)))
                    if looks_like_installer_name(&name.text) =>
                {
                    true
                }
                (AstLValue::FieldAccess(access), AstExpr::Var(AstNameRef::Param(_)))
                    if looks_like_installer_field(&access.field) =>
                {
                    true
                }
                _ => false,
            }
        }
        AstStmt::FunctionDecl(function_decl) => {
            function_name_looks_like_installer(&function_decl.target)
        }
        AstStmt::LocalFunctionDecl(_) => false,
        _ => false,
    }
}

fn function_name_looks_like_installer(target: &AstFunctionName) -> bool {
    match target {
        AstFunctionName::Plain(path) => name_path_looks_like_installer(path),
        AstFunctionName::Method(path, method) => {
            name_path_looks_like_installer(path) || looks_like_installer_field(method)
        }
    }
}

fn name_path_looks_like_installer(path: &AstNamePath) -> bool {
    path.fields
        .last()
        .is_some_and(|field| looks_like_installer_field(field))
        || matches!(
            &path.root,
            AstNameRef::Global(name) if looks_like_installer_name(&name.text)
        )
}

fn looks_like_installer_name(name: &str) -> bool {
    looks_like_installer_field(name)
}

fn looks_like_installer_field(field: &str) -> bool {
    matches!(field, "installer" | "install" | "setup" | "mount" | "apply")
}
