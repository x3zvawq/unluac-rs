//! 这个子模块是 `global_decl_pretty` pass 的 scoped 重写入口。
//!
//! 它依赖 `facts/insert/merge` 和共享 scoped walker，只负责在 block 作用域链上协调
//! merge + 可见 global 集维护，不会在这里重写普通表达式 sugar。
//! 例如：块前缀上一串 seed local + `global` run 会在这里先合并；Lua 5.5 的 missing
//! global 前导只会在“当前作用域已经有显式 global 证据”时才从观测推断，因为默认
//! `global *` 与 stripped bytecode 下的纯声明形式并不总是可区分。

use std::collections::BTreeSet;

use super::super::ReadabilityContext;
use super::super::walk::{BlockKind, ScopedAstRewritePass, rewrite_module_scoped};
use super::facts::{BlockFacts, MissingGlobals};
use super::insert::insert_missing_global_decls;
use super::merge::merge_seed_global_runs;
use crate::ast::common::{AstBlock, AstDialectVersion, AstModule};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    if !context.target.caps.global_decl {
        return false;
    }

    let mut pass = GlobalDeclPrettyPass {
        infer_missing: context.target.version != AstDialectVersion::Lua55,
    };
    rewrite_module_scoped(module, &BTreeSet::new(), &mut pass)
}

struct GlobalDeclPrettyPass {
    infer_missing: bool,
}

impl ScopedAstRewritePass for GlobalDeclPrettyPass {
    type Scope = BTreeSet<String>;

    fn enter_block(
        &mut self,
        block: &mut AstBlock,
        _kind: BlockKind,
        outer_declared: &Self::Scope,
    ) -> (bool, Self::Scope) {
        // AST build 只负责把字节码里显式存在的 `global ... = ...` 降回合法语法；
        // 这里仅合并 seed run，并在“当前作用域已经有显式 global 证据”的情况下再补
        // missing global。Lua 5.5 默认 `global *`，所以完全没有显式证据时不能凭
        // 观测补声明；但一旦当前或外层作用域已经显式打开了 global gate，就需要继续
        // 为同一作用域里剩余的 global 访问补齐声明，才能生成可重新编译的源码。
        let mut changed = merge_seed_global_runs(block);
        let facts = BlockFacts::collect(block);
        let missing =
            if self.infer_missing || facts.has_explicit_globals() || !outer_declared.is_empty() {
                facts.infer_missing(outer_declared)
            } else {
                MissingGlobals::default()
            };
        if !missing.is_empty() {
            insert_missing_global_decls(block, &missing);
            changed = true;
        }

        let visible = facts.visible_globals(outer_declared, &missing);
        (changed, visible)
    }
}
