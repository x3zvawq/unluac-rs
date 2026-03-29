//! 这个子模块是 `global_decl_pretty` pass 的 scoped 重写入口。
//!
//! 它依赖 `facts/insert/merge` 和共享 scoped walker，只负责在 block 作用域链上协调
//! merge + missing-global 插入，不会在这里重写普通表达式 sugar。
//! 例如：一个子块里首次写全局名时，这里会先继承外层可见声明，再决定要不要补前缀声明。

use std::collections::BTreeSet;

use super::super::ReadabilityContext;
use super::super::walk::{BlockKind, ScopedAstRewritePass, rewrite_module_scoped};
use super::facts::BlockFacts;
use super::insert::insert_missing_global_decls;
use super::merge::merge_seed_global_runs;
use crate::ast::common::{AstBlock, AstModule};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    if !context.target.caps.global_decl {
        return false;
    }

    let mut pass = GlobalDeclPrettyPass;
    rewrite_module_scoped(module, &BTreeSet::new(), &mut pass)
}

struct GlobalDeclPrettyPass;

impl ScopedAstRewritePass for GlobalDeclPrettyPass {
    type Scope = BTreeSet<String>;

    fn enter_block(
        &mut self,
        block: &mut AstBlock,
        _kind: BlockKind,
        outer_declared: &Self::Scope,
    ) -> (bool, Self::Scope) {
        // AST build 只负责把字节码里显式存在的 `global ... = ...` 降回合法语法；
        // 这里再补“源码里本该先声明、但前层没有显式写出来”的 missing/merged global decl。
        let mut changed = merge_seed_global_runs(block);
        let facts = BlockFacts::collect(block);
        let missing = facts.infer_missing(outer_declared);
        if !missing.is_empty() {
            insert_missing_global_decls(block, &missing);
            changed = true;
        }

        let visible = facts.visible_globals(outer_declared, &missing);
        (changed, visible)
    }
}
