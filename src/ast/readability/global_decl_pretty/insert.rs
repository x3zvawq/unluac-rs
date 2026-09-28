//! 将已确定的缺失 global 声明插回原 gate 激活位置。
//!
//! 消费 facts 和 collective 选择结果，不重新判断名字属性或声明必要性。

use crate::ast::AstGlobalAttr;
use crate::ast::common::{
    AstBlock, AstGlobalBinding, AstGlobalBindingTarget, AstGlobalDecl, AstGlobalName, AstStmt,
};

use super::facts::MissingGlobals;

pub(super) fn insert_missing_global_decls(
    block: &mut AstBlock,
    missing: &MissingGlobals,
    insert_at: usize,
) {
    let mut inserted = Vec::new();
    if !missing.none.is_empty() {
        inserted.push(build_global_decl(&missing.none, AstGlobalAttr::None));
    }
    if !missing.const_.is_empty() {
        inserted.push(build_global_decl(&missing.const_, AstGlobalAttr::Const));
    }
    if inserted.is_empty() {
        return;
    }

    let mut old_stmts = std::mem::take(&mut block.stmts).into_iter();
    let insert_at = insert_at.min(old_stmts.len());
    let mut new_stmts = Vec::with_capacity(old_stmts.len() + inserted.len());
    new_stmts.extend(old_stmts.by_ref().take(insert_at));
    new_stmts.extend(inserted);
    new_stmts.extend(old_stmts);
    block.stmts = new_stmts;
}

pub(super) fn build_wildcard_global_decl(attr: AstGlobalAttr) -> AstStmt {
    AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
        bindings: vec![AstGlobalBinding {
            target: AstGlobalBindingTarget::Wildcard,
            attr,
        }],
        values: Vec::new(),
    }))
}

fn build_global_decl(names: &[String], attr: AstGlobalAttr) -> AstStmt {
    AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
        bindings: names
            .iter()
            .cloned()
            .map(|name| AstGlobalBinding {
                target: AstGlobalBindingTarget::Name(AstGlobalName { text: name }),
                attr,
            })
            .collect(),
        values: Vec::new(),
    }))
}
