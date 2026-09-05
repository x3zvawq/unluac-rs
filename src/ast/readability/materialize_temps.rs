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
//! - 物化只改变可读性状态，`HirTemp(temp)` 显式保留 HIR 身份；repeat/capture 消费方
//!   直接查询该来源，不能把 AST 自建的同号 local 当作原 temp

use super::super::common::{
    AstBindingRef, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue, AstModule, AstNameRef,
    AstStmt, AstSyntheticLocalId,
};
use super::ReadabilityContext;
use super::walk::{self, AstRewritePass};

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    walk::rewrite_module(module, &mut MaterializeTempsPass)
}

struct MaterializeTempsPass;

impl AstRewritePass for MaterializeTempsPass {
    fn rewrite_stmt(&mut self, stmt: &mut AstStmt) -> bool {
        match stmt {
            AstStmt::LocalDecl(local_decl) => {
                let mut changed = false;
                for binding in &mut local_decl.bindings {
                    changed |= rewrite_binding_ref(&mut binding.id);
                }
                changed
            }
            AstStmt::FunctionDecl(function_decl) => {
                let mut changed = rewrite_function_name(&mut function_decl.target);
                changed |= rewrite_function_metadata(&mut function_decl.func);
                changed
            }
            AstStmt::LocalFunctionDecl(local_function_decl) => {
                let mut changed = rewrite_binding_ref(&mut local_function_decl.name);
                changed |= rewrite_function_metadata(&mut local_function_decl.func);
                changed
            }
            AstStmt::NumericFor(numeric_for) => rewrite_binding_ref(&mut numeric_for.binding),
            AstStmt::GenericFor(generic_for) => {
                let mut changed = false;
                for binding in &mut generic_for.bindings {
                    changed |= rewrite_binding_ref(binding);
                }
                changed
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
            | AstStmt::Error(_) => false,
        }
    }

    fn rewrite_lvalue(&mut self, target: &mut AstLValue) -> bool {
        if let AstLValue::Name(name) = target {
            rewrite_name_ref(name)
        } else {
            false
        }
    }

    fn rewrite_expr(&mut self, expr: &mut AstExpr) -> bool {
        match expr {
            AstExpr::Var(name) => rewrite_name_ref(name),
            AstExpr::FunctionExpr(function) => rewrite_function_metadata(function),
            AstExpr::Nil
            | AstExpr::Boolean(_)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_)
            | AstExpr::Int64(_)
            | AstExpr::UInt64(_)
            | AstExpr::Vector(_)
            | AstExpr::Complex { .. }
            | AstExpr::FieldAccess(_)
            | AstExpr::IndexAccess(_)
            | AstExpr::Unary(_)
            | AstExpr::Binary(_)
            | AstExpr::LogicalAnd(_)
            | AstExpr::LogicalOr(_)
            | AstExpr::Call(_)
            | AstExpr::MethodCall(_)
            | AstExpr::SingleValue(_)
            | AstExpr::VarArg
            | AstExpr::TableConstructor(_)
            | AstExpr::Error(_) => false,
        }
    }
}

fn rewrite_binding_ref(binding: &mut AstBindingRef) -> bool {
    let AstBindingRef::Temp(temp) = *binding else {
        return false;
    };
    *binding = AstBindingRef::SyntheticLocal(AstSyntheticLocalId::HirTemp(temp));
    true
}

fn rewrite_function_name(target: &mut AstFunctionName) -> bool {
    let path = match target {
        AstFunctionName::Plain(path) | AstFunctionName::Method(path, _) => path,
    };
    rewrite_name_ref(&mut path.root)
}

fn rewrite_name_ref(name: &mut AstNameRef) -> bool {
    let AstNameRef::Temp(temp) = name else {
        return false;
    };
    let temp = *temp;
    *name = AstNameRef::SyntheticLocal(AstSyntheticLocalId::HirTemp(temp));
    true
}

fn rewrite_function_metadata(function: &mut AstFunctionExpr) -> bool {
    let mut changed = false;
    if let Some(named_vararg) = &mut function.named_vararg {
        changed |= rewrite_binding_ref(named_vararg);
    }

    if function
        .captured_bindings
        .iter()
        .any(|binding| matches!(binding, AstBindingRef::Temp(_)))
    {
        function.captured_bindings = std::mem::take(&mut function.captured_bindings)
            .into_iter()
            .map(|binding| match binding {
                AstBindingRef::Temp(temp) => {
                    AstBindingRef::SyntheticLocal(AstSyntheticLocalId::HirTemp(temp))
                }
                binding => binding,
            })
            .collect();
        changed = true;
    }

    if function
        .capture_write_names
        .iter()
        .any(|name| matches!(name, AstNameRef::Temp(_)))
    {
        function.capture_write_names = std::mem::take(&mut function.capture_write_names)
            .into_iter()
            .map(|mut name| {
                rewrite_name_ref(&mut name);
                name
            })
            .collect();
        changed = true;
    }

    for name in function.capture_names_by_upvalue.values_mut() {
        changed |= rewrite_name_ref(name);
    }

    changed
}
