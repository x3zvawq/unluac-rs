//! 在最终源码树上核对必须消失的 Luau 调用。
//!
//! HIR 已证明原展开帧及参数替换；这里不重建寄存器身份。固定函数体在仓库 pinned
//! Luau 的默认编译选项下 cost=25、stack=4，基础阈值25经收益调整后为28。只接受直接单结果
//! initializer，并用活动声明数约束 caller regTop；模块外围限定为不引起其它 O2
//! 改写的语法。例 `local result=build(input)` 只有所有 occurrence 及原函数声明
//! 同时通过时才可发射 optimize pragma，不能将该要求当作可关闭的展示注释。

use crate::ast::*;
use crate::hir::HirRequiredLuauInlining;
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn validate(module: &AstModule, requirements: &[HirRequiredLuauInlining]) -> bool {
    let mut callees = BTreeMap::new();
    let mut results = BTreeMap::new();
    let fields = requirements
        .iter()
        .map(|requirement| (requirement.callee, &requirement.field))
        .collect::<BTreeMap<_, _>>();
    for requirement in requirements {
        if requirement.owner != module.entry_function
            || callees
                .insert(requirement.callee, requirement.child)
                .is_some()
        {
            return false;
        }
        for result in &requirement.results {
            if results.insert(*result, requirement.callee).is_some() {
                return false;
            }
        }
    }
    let mut declared = BTreeSet::new();
    let mut seen_results = BTreeSet::new();
    let mut active = 0usize;
    for stmt in &module.body.stmts {
        match stmt {
            AstStmt::LocalFunctionDecl(decl) => {
                let AstBindingRef::Local(local) = decl.name else {
                    return false;
                };
                if callees.get(&local) != Some(&decl.func.function)
                    || !declared.insert(local)
                    || !callee_body(&decl.func, fields[&local])
                {
                    return false;
                }
                active += 1;
            }
            AstStmt::LocalDecl(decl) => {
                // 整组 local 的 target 已预留；只允许一对一的 fixed-one 调用。
                active += decl.bindings.len();
                for (index, value) in decl.values.iter().enumerate() {
                    if let AstExpr::Call(call) = value {
                        let Some(binding) = decl.bindings.get(index) else {
                            return false;
                        };
                        let AstBindingRef::Local(result) = binding.id else {
                            return false;
                        };
                        let Some(callee) = results.get(&result) else {
                            return false;
                        };
                        if decl.bindings.len() != 1
                            || decl.values.len() != 1
                            || active > 128
                            || !seen_results.insert(result)
                            || !declared.contains(callee)
                            || call.callee != AstExpr::Var(AstNameRef::Local(*callee))
                            || call.args.len() != 1
                            || !plain_expr(&call.args[0], &callees)
                        {
                            return false;
                        }
                    } else if !plain_expr(value, &callees) {
                        return false;
                    }
                }
            }
            AstStmt::CallStmt(stmt) => {
                let AstCallKind::Call(call) = &stmt.call else {
                    return false;
                };
                if !matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name))
                    if name.text == "assert" || name.text == "print")
                    || !call.args.iter().all(|arg| plain_expr(arg, &callees))
                {
                    return false;
                }
            }
            AstStmt::Return(ret) if ret.values.is_empty() => {}
            _ => return false,
        }
    }
    seen_results.len() == results.len() && declared.len() == callees.len()
}

fn callee_body(func: &AstFunctionExpr, expected_field: &crate::LuaString) -> bool {
    if func.params.len() != 1
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let [AstStmt::Return(ret)] = func.body.stmts.as_slice() else {
        return false;
    };
    let [AstExpr::TableConstructor(table)] = ret.values.as_slice() else {
        return false;
    };
    let [AstTableField::Array(AstExpr::Call(call))] = table.fields.as_slice() else {
        return false;
    };
    if !matches!(&call.callee, AstExpr::FieldAccess(field)
        if field.field == "unpack" && matches!(&field.base,
            AstExpr::Var(AstNameRef::Global(name)) if name.text == "table"))
    {
        return false;
    }
    let [AstExpr::LogicalOr(logical)] = call.args.as_slice() else {
        return false;
    };
    matches!((&logical.lhs, &logical.rhs),
        (AstExpr::FieldAccess(field), AstExpr::TableConstructor(empty))
        if field.base == AstExpr::Var(AstNameRef::Param(func.params[0]))
            && Some(field.field.as_str()) == expected_field.as_utf8()
            && empty.fields.is_empty())
}

/// 不含其它函数解析、builtin 折叠、math 常量、vararg 或算术交换候选的外围表达式。
/// 遍历拒绝所有 global 值读取，因此也覆盖整个模块的 getfenv/setfenv 禁内联条件。
fn plain_expr(
    expr: &AstExpr,
    callees: &BTreeMap<crate::hir::LocalId, crate::hir::HirProtoRef>,
) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_) => true,
        AstExpr::Var(AstNameRef::Local(local)) => !callees.contains_key(local),
        AstExpr::FieldAccess(field) => plain_expr(&field.base, callees),
        AstExpr::IndexAccess(index) => {
            plain_expr(&index.base, callees) && plain_expr(&index.index, callees)
        }
        AstExpr::Unary(unary) => {
            matches!(unary.op, AstUnaryOpKind::Length | AstUnaryOpKind::Not)
                && plain_expr(&unary.expr, callees)
        }
        AstExpr::Binary(binary) => {
            matches!(
                binary.op,
                AstBinaryOpKind::Eq
                    | AstBinaryOpKind::Lt
                    | AstBinaryOpKind::Le
                    | AstBinaryOpKind::Gt
                    | AstBinaryOpKind::Ge
            ) && plain_expr(&binary.lhs, callees)
                && plain_expr(&binary.rhs, callees)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            plain_expr(&logical.lhs, callees) && plain_expr(&logical.rhs, callees)
        }
        AstExpr::TableConstructor(table) => table.fields.iter().all(|field| match field {
            AstTableField::Array(value) => plain_expr(value, callees),
            AstTableField::Record(record) => {
                (match &record.key {
                    AstTableKey::Name(_) => true,
                    AstTableKey::Expr(key) => plain_expr(key, callees),
                }) && plain_expr(&record.value, callees)
            }
        }),
        _ => false,
    }
}
