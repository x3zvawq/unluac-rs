//! 把显然属于同一次源码声明的相邻语句重新合并。

use super::super::common::{
    AstBindingRef, AstBlock, AstFunctionExpr, AstLValue, AstLocalAttr, AstLocalDecl, AstModule,
    AstNameRef, AstStmt,
};
use super::ReadabilityContext;

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    rewrite_block(&mut module.body)
}

fn rewrite_block(block: &mut AstBlock) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= rewrite_nested(stmt);
    }

    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut index = 0;
    while index < old_stmts.len() {
        let Some(next_stmt) = old_stmts.get(index + 1) else {
            new_stmts.push(old_stmts[index].clone());
            index += 1;
            continue;
        };

        if let Some(merged) = try_merge_local_decl_with_assign(&old_stmts[index], next_stmt) {
            new_stmts.push(AstStmt::LocalDecl(Box::new(merged)));
            changed = true;
            index += 2;
            continue;
        }

        new_stmts.push(old_stmts[index].clone());
        index += 1;
    }

    block.stmts = new_stmts;
    changed
}

fn rewrite_nested(stmt: &mut AstStmt) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            let mut changed = rewrite_block(&mut if_stmt.then_block);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block);
            }
            changed
        }
        AstStmt::While(while_stmt) => rewrite_block(&mut while_stmt.body),
        AstStmt::Repeat(repeat_stmt) => rewrite_block(&mut repeat_stmt.body),
        AstStmt::NumericFor(numeric_for) => rewrite_block(&mut numeric_for.body),
        AstStmt::GenericFor(generic_for) => rewrite_block(&mut generic_for.body),
        AstStmt::DoBlock(block) => rewrite_block(block),
        AstStmt::FunctionDecl(function_decl) => rewrite_function(&mut function_decl.func),
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            rewrite_function(&mut local_function_decl.func)
        }
        AstStmt::LocalDecl(_)
        | AstStmt::GlobalDecl(_)
        | AstStmt::Assign(_)
        | AstStmt::CallStmt(_)
        | AstStmt::Return(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) => false,
    }
}

fn rewrite_function(function: &mut AstFunctionExpr) -> bool {
    rewrite_block(&mut function.body)
}

fn try_merge_local_decl_with_assign(current: &AstStmt, next: &AstStmt) -> Option<AstLocalDecl> {
    let AstStmt::LocalDecl(local_decl) = current else {
        return None;
    };
    let AstStmt::Assign(assign) = next else {
        return None;
    };
    if !local_decl.values.is_empty() || local_decl.bindings.is_empty() {
        return None;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| binding.attr != AstLocalAttr::None)
    {
        return None;
    }
    if local_decl.bindings.len() != assign.targets.len() || assign.values.is_empty() {
        return None;
    }
    if !local_decl
        .bindings
        .iter()
        .zip(assign.targets.iter())
        .all(|(binding, target)| local_binding_matches_target(binding.id, target))
    {
        return None;
    }

    Some(AstLocalDecl {
        bindings: local_decl.bindings.clone(),
        values: assign.values.clone(),
    })
}

fn local_binding_matches_target(binding: AstBindingRef, target: &AstLValue) -> bool {
    match (binding, target) {
        (AstBindingRef::Local(local), AstLValue::Name(AstNameRef::Local(target_local))) => {
            local == *target_local
        }
        (AstBindingRef::Temp(temp), AstLValue::Name(AstNameRef::Temp(target_temp))) => {
            temp == *target_temp
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::common::{AstCallExpr, AstCallKind, AstLocalBinding};
    use crate::ast::{
        AstExpr, AstLValue, AstLocalAttr, AstLocalDecl, AstModule, AstNameRef, AstStmt,
        AstTargetDialect, make_readable_with_options,
    };
    use crate::hir::{LocalId, TempId};

    #[test]
    fn merges_empty_local_decl_followed_by_matching_assign() {
        let temp = TempId(0);
        let module = AstModule {
            body: crate::ast::AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: crate::ast::AstBindingRef::Temp(temp),
                            attr: AstLocalAttr::None,
                        }],
                        values: Vec::new(),
                    })),
                    AstStmt::Assign(Box::new(crate::ast::AstAssign {
                        targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                        values: vec![AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                            args: vec![AstExpr::Integer(1)],
                        }))],
                    })),
                ],
            },
        };

        let module = make_readable_with_options(
            &module,
            AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            Default::default(),
        );
        assert_eq!(
            module.body.stmts,
            vec![AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: crate::ast::AstBindingRef::Temp(temp),
                    attr: AstLocalAttr::None,
                }],
                values: vec![AstExpr::Call(Box::new(AstCallExpr {
                    callee: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                    args: vec![AstExpr::Integer(1)],
                }))],
            }))]
        );
    }

    #[test]
    fn does_not_merge_when_assign_targets_do_not_match_decl_bindings() {
        let module = AstModule {
            body: crate::ast::AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: crate::ast::AstBindingRef::Local(LocalId(0)),
                            attr: AstLocalAttr::None,
                        }],
                        values: Vec::new(),
                    })),
                    AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                        call: AstCallKind::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Local(LocalId(1))),
                            args: vec![AstExpr::Integer(1)],
                        })),
                    })),
                ],
            },
        };

        let module = make_readable_with_options(
            &module,
            AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            Default::default(),
        );
        assert_eq!(module.body.stmts.len(), 2);
    }
}
