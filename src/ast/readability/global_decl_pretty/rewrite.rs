//! 这个子模块是 `global_decl_pretty` pass 的 scoped 重写入口。
//!
//! 它依赖 `facts/insert/merge` 和共享 scoped walker，只负责在 block 作用域链上协调
//! merge + 可见 global 集维护，不会在这里重写普通表达式 sugar。
//! 例如：块前缀上一串 seed local + `global` run 会在这里先合并；Lua 5.5 的 missing
//! global 声明只会在“当前作用域已经有显式 global 证据”时才从观测推断，并放回原 gate
//! 的激活点；默认 `global *` 与 stripped bytecode 下的纯声明形式并不总是可区分。

use super::super::ReadabilityContext;
use super::super::walk::{BlockKind, ScopedAstRewritePass, rewrite_module_scoped};
use super::collective::try_wrap_missing_collective_suffix;
use super::facts::{BlockFacts, MissingGlobals, VisibleGlobals};
use super::insert::insert_missing_global_decls;
use super::merge::merge_seed_global_runs;
use crate::ast::DecompileDialect;
use crate::ast::common::{AstBlock, AstModule};

pub(in crate::ast::readability) fn apply(
    module: &mut AstModule,
    context: ReadabilityContext,
) -> bool {
    if !context.target.caps.global_decl {
        // 分析停用[TargetConstraint]：目标方言没有 `global` 声明语法，整个 pass 不得生成不可编译节点。
        return false;
    }

    let mut pass = GlobalDeclPrettyPass {
        infer_missing: context.target.version != DecompileDialect::Lua55,
    };
    rewrite_module_scoped(module, &VisibleGlobals::default(), &mut pass)
}

struct GlobalDeclPrettyPass {
    infer_missing: bool,
}

impl ScopedAstRewritePass for GlobalDeclPrettyPass {
    type Scope = VisibleGlobals;

    fn enter_block(
        &mut self,
        block: &mut AstBlock,
        kind: BlockKind,
        outer_declared: &Self::Scope,
    ) -> (bool, Self::Scope) {
        self.enter_scoped_block(block, kind, outer_declared, None, true)
    }

    fn enter_repeat_body(
        &mut self,
        block: &mut AstBlock,
        condition: &crate::ast::common::AstExpr,
        outer_declared: &Self::Scope,
    ) -> (bool, Self::Scope) {
        self.enter_scoped_block(
            block,
            BlockKind::Regular,
            outer_declared,
            Some(condition),
            false,
        )
    }

    fn scope_for_stmt_children(
        &mut self,
        stmt: &crate::ast::common::AstStmt,
        scope: &Self::Scope,
    ) -> Self::Scope {
        if matches!(stmt, crate::ast::common::AstStmt::FunctionDecl(_)) {
            scope.after_stmt(stmt)
        } else {
            scope.clone()
        }
    }

    fn scope_after_stmt(
        &mut self,
        stmt: &crate::ast::common::AstStmt,
        scope: &Self::Scope,
    ) -> Self::Scope {
        scope.after_stmt(stmt)
    }
}

impl GlobalDeclPrettyPass {
    fn enter_scoped_block(
        &mut self,
        block: &mut AstBlock,
        kind: BlockKind,
        outer_declared: &VisibleGlobals,
        trailing_expr: Option<&crate::ast::common::AstExpr>,
        allow_collective_suffix: bool,
    ) -> (bool, VisibleGlobals) {
        // AST build 只负责把字节码里显式存在的 `global ... = ...` 降回合法语法；
        // 这里仅合并 seed run，并在“当前作用域已经有显式 global 证据”的情况下再补
        // missing global。Lua 5.5 默认 `global *`，完全没有显式证据时不能凭观测补声明；
        // repeat condition 与 body 共用事实，但不能用 do 包裹 body suffix，否则会切断
        // condition 对 body local 的可见性（regress_424）。
        let mut changed = merge_seed_global_runs(block);
        let facts = trailing_expr.map_or_else(
            || BlockFacts::collect(block),
            |condition| BlockFacts::collect_repeat(block, condition),
        );
        let mut missing = if self.infer_missing
            || facts.has_explicit_globals()
            || outer_declared.has_explicit_gate()
        {
            facts.infer_missing(outer_declared)
        } else {
            MissingGlobals::default()
        };
        if !missing.is_empty()
            && !self.infer_missing
            && !facts.has_explicit_globals()
            && allow_collective_suffix
            && try_wrap_missing_collective_suffix(block, kind, &missing)
        {
            missing = MissingGlobals::default();
            changed = true;
        }
        if !missing.is_empty() {
            let insert_at = facts.missing_insert_at(outer_declared);
            insert_missing_global_decls(block, &missing, insert_at);
            changed = true;
        }

        (changed, outer_declared.clone())
    }
}
