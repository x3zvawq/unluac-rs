//! 让纯短路表达式更像源码。
//!
//! 这里不负责“反内联”。它只处理一类可证明纯净的表达式子集，然后借用 HIR 侧的等价
//! 综合工具把 `and/or/not` 重新收成更自然的 guarded 结构。

use super::super::common::{
    AstBinaryExpr, AstBinaryOpKind, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue,
    AstLogicalExpr, AstModule, AstStmt, AstTableField, AstTableKey, AstUnaryExpr, AstUnaryOpKind,
};
use super::ReadabilityContext;
use crate::hir::{
    HirBinaryExpr, HirBinaryOpKind, HirExpr, HirLogicalExpr, HirUnaryExpr, HirUnaryOpKind,
    synthesize_readable_pure_logical_expr,
};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    rewrite_block(&mut module.body)
}

fn rewrite_block(block: &mut AstBlock) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= rewrite_stmt(stmt);
    }
    changed
}

fn rewrite_stmt(stmt: &mut AstStmt) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            let mut changed = rewrite_expr(&mut if_stmt.cond);
            changed |= rewrite_block(&mut if_stmt.then_block);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block);
            }
            changed
        }
        AstStmt::While(while_stmt) => {
            rewrite_expr(&mut while_stmt.cond) | rewrite_block(&mut while_stmt.body)
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_block(&mut repeat_stmt.body) | rewrite_expr(&mut repeat_stmt.cond)
        }
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = rewrite_expr(&mut numeric_for.start);
            changed |= rewrite_expr(&mut numeric_for.limit);
            changed |= rewrite_expr(&mut numeric_for.step);
            changed |= rewrite_block(&mut numeric_for.body);
            changed
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for expr in &mut generic_for.iterator {
                changed |= rewrite_expr(expr);
            }
            changed |= rewrite_block(&mut generic_for.body);
            changed
        }
        AstStmt::DoBlock(block) => rewrite_block(block),
        AstStmt::FunctionDecl(function_decl) => rewrite_function(&mut function_decl.func),
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            rewrite_function(&mut local_function_decl.func)
        }
        AstStmt::LocalDecl(local_decl) => {
            let mut changed = false;
            for value in &mut local_decl.values {
                changed |= rewrite_expr(value);
            }
            changed
        }
        AstStmt::GlobalDecl(global_decl) => {
            let mut changed = false;
            for value in &mut global_decl.values {
                changed |= rewrite_expr(value);
            }
            changed
        }
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target in &mut assign.targets {
                changed |= rewrite_lvalue(target);
            }
            for value in &mut assign.values {
                changed |= rewrite_expr(value);
            }
            changed
        }
        AstStmt::CallStmt(call_stmt) => rewrite_call(&mut call_stmt.call),
        AstStmt::Return(ret) => {
            let mut changed = false;
            for value in &mut ret.values {
                changed |= rewrite_expr(value);
            }
            changed
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

fn rewrite_function(function: &mut AstFunctionExpr) -> bool {
    rewrite_block(&mut function.body)
}

fn rewrite_call(call: &mut AstCallKind) -> bool {
    match call {
        AstCallKind::Call(call) => {
            let mut changed = rewrite_expr(&mut call.callee);
            for arg in &mut call.args {
                changed |= rewrite_expr(arg);
            }
            changed
        }
        AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_expr(&mut call.receiver);
            for arg in &mut call.args {
                changed |= rewrite_expr(arg);
            }
            changed
        }
    }
}

fn rewrite_lvalue(target: &mut AstLValue) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => rewrite_expr(&mut access.base),
        AstLValue::IndexAccess(access) => {
            rewrite_expr(&mut access.base) | rewrite_expr(&mut access.index)
        }
    }
}

fn rewrite_expr(expr: &mut AstExpr) -> bool {
    let mut changed = match expr {
        AstExpr::FieldAccess(access) => rewrite_expr(&mut access.base),
        AstExpr::IndexAccess(access) => {
            rewrite_expr(&mut access.base) | rewrite_expr(&mut access.index)
        }
        AstExpr::Unary(unary) => rewrite_expr(&mut unary.expr),
        AstExpr::Binary(binary) => rewrite_expr(&mut binary.lhs) | rewrite_expr(&mut binary.rhs),
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_expr(&mut logical.lhs) | rewrite_expr(&mut logical.rhs)
        }
        AstExpr::Call(call) => {
            let mut changed = rewrite_expr(&mut call.callee);
            for arg in &mut call.args {
                changed |= rewrite_expr(arg);
            }
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = rewrite_expr(&mut call.receiver);
            for arg in &mut call.args {
                changed |= rewrite_expr(arg);
            }
            changed
        }
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                match field {
                    AstTableField::Array(value) => changed |= rewrite_expr(value),
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            changed |= rewrite_expr(key);
                        }
                        changed |= rewrite_expr(&mut record.value);
                    }
                }
            }
            changed
        }
        AstExpr::FunctionExpr(function) => rewrite_function(function),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    };

    if let Some(hir_expr) = hir_from_ast_expr(expr)
        && let Some(pretty_hir) = synthesize_readable_pure_logical_expr(&hir_expr)
        && pretty_hir != hir_expr
        && let Some(pretty_ast) = ast_from_hir_expr(&pretty_hir)
    {
        *expr = pretty_ast;
        changed = true;
    }

    changed
}

fn hir_from_ast_expr(expr: &AstExpr) -> Option<HirExpr> {
    match expr {
        AstExpr::Nil => Some(HirExpr::Nil),
        AstExpr::Boolean(value) => Some(HirExpr::Boolean(*value)),
        AstExpr::Integer(value) => Some(HirExpr::Integer(*value)),
        AstExpr::Number(value) => Some(HirExpr::Number(*value)),
        AstExpr::String(value) => Some(HirExpr::String(value.clone())),
        AstExpr::Var(name) => match name {
            super::super::common::AstNameRef::Param(param) => Some(HirExpr::ParamRef(*param)),
            super::super::common::AstNameRef::Local(local) => Some(HirExpr::LocalRef(*local)),
            super::super::common::AstNameRef::Temp(temp) => Some(HirExpr::TempRef(*temp)),
            super::super::common::AstNameRef::Upvalue(upvalue) => {
                Some(HirExpr::UpvalueRef(*upvalue))
            }
            super::super::common::AstNameRef::Global(_) => None,
        },
        AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => {
            Some(HirExpr::Unary(Box::new(HirUnaryExpr {
                op: HirUnaryOpKind::Not,
                expr: hir_from_ast_expr(&unary.expr)?,
            })))
        }
        AstExpr::Binary(binary) if binary.op == AstBinaryOpKind::Eq => {
            Some(HirExpr::Binary(Box::new(HirBinaryExpr {
                op: HirBinaryOpKind::Eq,
                lhs: hir_from_ast_expr(&binary.lhs)?,
                rhs: hir_from_ast_expr(&binary.rhs)?,
            })))
        }
        AstExpr::LogicalAnd(logical) => Some(HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
            lhs: hir_from_ast_expr(&logical.lhs)?,
            rhs: hir_from_ast_expr(&logical.rhs)?,
        }))),
        AstExpr::LogicalOr(logical) => Some(HirExpr::LogicalOr(Box::new(HirLogicalExpr {
            lhs: hir_from_ast_expr(&logical.lhs)?,
            rhs: hir_from_ast_expr(&logical.rhs)?,
        }))),
        AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Unary(_)
        | AstExpr::Binary(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_) => None,
    }
}

fn ast_from_hir_expr(expr: &HirExpr) -> Option<AstExpr> {
    match expr {
        HirExpr::Nil => Some(AstExpr::Nil),
        HirExpr::Boolean(value) => Some(AstExpr::Boolean(*value)),
        HirExpr::Integer(value) => Some(AstExpr::Integer(*value)),
        HirExpr::Number(value) => Some(AstExpr::Number(*value)),
        HirExpr::String(value) => Some(AstExpr::String(value.clone())),
        HirExpr::ParamRef(param) => Some(AstExpr::Var(super::super::common::AstNameRef::Param(
            *param,
        ))),
        HirExpr::LocalRef(local) => Some(AstExpr::Var(super::super::common::AstNameRef::Local(
            *local,
        ))),
        HirExpr::TempRef(temp) => Some(AstExpr::Var(super::super::common::AstNameRef::Temp(*temp))),
        HirExpr::UpvalueRef(upvalue) => Some(AstExpr::Var(
            super::super::common::AstNameRef::Upvalue(*upvalue),
        )),
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            Some(AstExpr::Unary(Box::new(AstUnaryExpr {
                op: AstUnaryOpKind::Not,
                expr: ast_from_hir_expr(&unary.expr)?,
            })))
        }
        HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq => {
            Some(AstExpr::Binary(Box::new(AstBinaryExpr {
                op: AstBinaryOpKind::Eq,
                lhs: ast_from_hir_expr(&binary.lhs)?,
                rhs: ast_from_hir_expr(&binary.rhs)?,
            })))
        }
        HirExpr::LogicalAnd(logical) => Some(AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
            lhs: ast_from_hir_expr(&logical.lhs)?,
            rhs: ast_from_hir_expr(&logical.rhs)?,
        }))),
        HirExpr::LogicalOr(logical) => Some(AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: ast_from_hir_expr(&logical.lhs)?,
            rhs: ast_from_hir_expr(&logical.rhs)?,
        }))),
        HirExpr::Decision(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{
        AstBlock, AstDialectVersion, AstExpr, AstLogicalExpr, AstModule, AstNameRef, AstStmt,
        AstTargetDialect, AstUnaryExpr, AstUnaryOpKind,
    };
    use crate::hir::ParamId;

    use super::super::ReadabilityContext;
    use super::{apply, hir_from_ast_expr};

    fn and(lhs: AstExpr, rhs: AstExpr) -> AstExpr {
        AstExpr::LogicalAnd(Box::new(AstLogicalExpr { lhs, rhs }))
    }

    fn or(lhs: AstExpr, rhs: AstExpr) -> AstExpr {
        AstExpr::LogicalOr(Box::new(AstLogicalExpr { lhs, rhs }))
    }

    fn not(expr: AstExpr) -> AstExpr {
        AstExpr::Unary(Box::new(AstUnaryExpr {
            op: AstUnaryOpKind::Not,
            expr,
        }))
    }

    #[test]
    fn rewrites_ultimate_mess_shape_towards_guarded_source_form() {
        let a = AstExpr::Var(AstNameRef::Param(ParamId(1)));
        let b = AstExpr::Var(AstNameRef::Param(ParamId(2)));
        let c = AstExpr::Var(AstNameRef::Param(ParamId(3)));
        let fallback = and(not(a.clone()), not(b.clone()));
        let mut module = AstModule {
            body: AstBlock {
                stmts: vec![AstStmt::Return(Box::new(crate::ast::AstReturn {
                    values: vec![or(
                        or(
                            and(a.clone(), b.clone()),
                            and(
                                c.clone(),
                                or(b.clone(), or(and(c.clone(), a.clone()), fallback.clone())),
                            ),
                        ),
                        fallback.clone(),
                    )],
                }))],
            },
        };

        assert!(apply(
            &mut module,
            ReadabilityContext {
                target: AstTargetDialect::new(AstDialectVersion::Lua55),
                options: Default::default(),
            }
        ));

        let AstStmt::Return(ret) = &module.body.stmts[0] else {
            panic!("expected return");
        };
        let expected = or(
            and(or(and(a.clone(), b.clone()), c.clone()), or(b, and(c, a))),
            fallback,
        );
        assert_eq!(ret.values, vec![expected]);
    }

    #[test]
    fn rejects_impure_index_accesses() {
        let expr = AstExpr::IndexAccess(Box::new(crate::ast::AstIndexAccess {
            base: AstExpr::Var(AstNameRef::Param(ParamId(0))),
            index: AstExpr::Var(AstNameRef::Param(ParamId(1))),
        }));
        assert!(hir_from_ast_expr(&expr).is_none());
    }
}
