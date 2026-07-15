//! AST 方言特性收集。

use std::collections::BTreeSet;

use crate::ast::traverse::{
    traverse_call_children, traverse_expr_children, traverse_lvalue_children,
    traverse_stmt_children,
};
use crate::ast::{AstExpr, AstFeature, AstGlobalAttr, AstLocalAttr, AstModule, AstStmt};

pub(crate) fn collect_ast_features(module: &AstModule) -> (BTreeSet<AstFeature>, bool) {
    let mut features = BTreeSet::new();
    let mut has_errors = false;
    collect_block_features(&module.body, &mut features, &mut has_errors);
    (features, has_errors)
}

fn collect_block_features(
    block: &crate::ast::AstBlock,
    features: &mut BTreeSet<AstFeature>,
    has_errors: &mut bool,
) {
    for stmt in &block.stmts {
        collect_stmt_features(stmt, features, has_errors);
    }
}

fn collect_stmt_features(
    stmt: &AstStmt,
    features: &mut BTreeSet<AstFeature>,
    has_errors: &mut bool,
) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                match binding.attr {
                    AstLocalAttr::Const => {
                        features.insert(AstFeature::LocalConst);
                    }
                    AstLocalAttr::Close => {
                        features.insert(AstFeature::LocalClose);
                    }
                    AstLocalAttr::None => {}
                }
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            features.insert(AstFeature::GlobalDecl);
            if global_decl
                .bindings
                .iter()
                .any(|binding| binding.attr == AstGlobalAttr::Const)
            {
                features.insert(AstFeature::GlobalConst);
            }
        }
        AstStmt::Continue => {
            features.insert(AstFeature::ContinueStmt);
        }
        AstStmt::Goto(_) | AstStmt::Label(_) => {
            features.insert(AstFeature::GotoLabel);
        }
        AstStmt::Error(_) => *has_errors = true,
        _ => {}
    }

    traverse_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(e) => { collect_expr_features(e, features, has_errors); },
        lvalue(lv) => {
            traverse_lvalue_children!(
                lv,
                borrow = [&],
                expr(e) => { collect_expr_features(e, features, has_errors); }
            );
        },
        block(b) => { collect_block_features(b, features, has_errors); },
        function(f) => { collect_block_features(&f.body, features, has_errors); },
        condition(c) => { collect_expr_features(c, features, has_errors); },
        call(c) => {
            traverse_call_children!(
                c,
                iter = iter,
                borrow = [&],
                expr(e) => { collect_expr_features(e, features, has_errors); }
            );
        }
    );
}

fn collect_expr_features(
    expr: &AstExpr,
    features: &mut BTreeSet<AstFeature>,
    has_errors: &mut bool,
) {
    if matches!(expr, AstExpr::Error(_)) {
        *has_errors = true;
    }
    traverse_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(e) => { collect_expr_features(e, features, has_errors); },
        function(f) => { collect_block_features(&f.body, features, has_errors); }
    );
}
