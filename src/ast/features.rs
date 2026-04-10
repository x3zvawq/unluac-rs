//! AST feature collection — 递归扫描 AST 以发现需要特定方言版本才能表达的特性。
//!
//! 这里使用 `src/ast/traverse.rs` 里的共享宏完成子节点递归骨架，
//! 仅在宏不覆盖的 variant 前做少量手动 match（属性、Continue、Goto/Label）。

use std::collections::BTreeSet;

use crate::ast::traverse::{
    traverse_call_children, traverse_expr_children, traverse_lvalue_children,
    traverse_stmt_children,
};
use crate::ast::{AstExpr, AstFeature, AstGlobalAttr, AstLocalAttr, AstModule, AstStmt};

pub(crate) fn collect_ast_features(module: &AstModule) -> BTreeSet<AstFeature> {
    let mut features = BTreeSet::new();
    collect_block_features(&module.body, &mut features);
    features
}

fn collect_block_features(block: &crate::ast::AstBlock, features: &mut BTreeSet<AstFeature>) {
    for stmt in &block.stmts {
        collect_stmt_features(stmt, features);
    }
}

fn collect_stmt_features(stmt: &AstStmt, features: &mut BTreeSet<AstFeature>) {
    // 宏不覆盖的 variant 特性：属性、continue、goto/label
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
            for binding in &global_decl.bindings {
                if binding.attr == AstGlobalAttr::Const {
                    features.insert(AstFeature::GlobalConst);
                }
            }
        }
        AstStmt::Continue => {
            features.insert(AstFeature::ContinueStmt);
        }
        AstStmt::Goto(_) | AstStmt::Label(_) | AstStmt::Error(_) => {
            features.insert(AstFeature::GotoLabel);
        }
        _ => {}
    }

    traverse_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(e) => { collect_expr_features(e, features); },
        lvalue(lv) => {
            traverse_lvalue_children!(
                lv,
                borrow = [&],
                expr(e) => { collect_expr_features(e, features); }
            );
        },
        block(b) => { collect_block_features(b, features); },
        function(f) => { collect_block_features(&f.body, features); },
        condition(c) => { collect_expr_features(c, features); },
        call(c) => {
            traverse_call_children!(
                c,
                iter = iter,
                borrow = [&],
                expr(e) => { collect_expr_features(e, features); }
            );
        }
    );
}

fn collect_expr_features(expr: &AstExpr, features: &mut BTreeSet<AstFeature>) {
    traverse_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(e) => { collect_expr_features(e, features); },
        function(f) => { collect_block_features(&f.body, features); }
    );
}