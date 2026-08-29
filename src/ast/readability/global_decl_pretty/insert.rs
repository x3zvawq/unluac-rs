//! 这个子模块负责把缺失的 global decl 插回事实层确定的 gate 激活点。
//!
//! 它依赖 `facts` 已经判定好的 missing globals，只负责插入 AST `GlobalDecl`，不会重新
//! 计算哪些名字该声明成 const 或 none。
//! 例如：块内首次写 `installer` 且未声明时，这里会在约束该访问的既有 gate 后补
//! `global installer`；外层 gate 已生效时才放在当前 block 前缀。
//! 若上层已经决定要落成 collective gate，这里也只负责把 `global *` 这个 AST 节点造出来。

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

    let old_stmts = std::mem::take(&mut block.stmts);
    let insert_at = insert_at.min(old_stmts.len());
    let mut new_stmts = Vec::with_capacity(old_stmts.len() + inserted.len());
    new_stmts.extend(old_stmts.iter().take(insert_at).cloned());
    new_stmts.extend(inserted);
    new_stmts.extend(old_stmts.into_iter().skip(insert_at));
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
