//! 协调 global 声明的作用域内重写与可见性维护。
//!
//! 消费当前 AST 的显式 gate 和各子模块发布的声明事实，不凭普通全局访问发明 gate。

use super::super::ReadabilityContext;
use super::super::walk::{ScopedAstRewritePass, rewrite_module_scoped};
use super::collective::try_wrap_missing_collective_suffix;
use super::facts::{BlockFacts, MissingGlobals, VisibleGlobals};
use super::insert::insert_missing_global_decls;
use super::merge::merge_seed_global_runs;
use crate::ast::common::{AstBlock, AstModule};
use crate::ast::traverse::BlockKind;

pub(in crate::ast::readability) fn apply(
    module: &mut AstModule,
    context: ReadabilityContext,
) -> bool {
    if !context.target.caps.global_decl {
        // 分析停用[TargetConstraint]：只有 Lua 5.5 语法接受 `global`；Lua 5.1--5.4、LuaJIT 与 Luau 的 AST build 也不会产出本 pass 的声明候选。
        return false;
    }

    let mut pass = GlobalDeclPrettyPass;
    rewrite_module_scoped(module, VisibleGlobals::default(), &mut pass)
}

struct GlobalDeclPrettyPass;

impl ScopedAstRewritePass for GlobalDeclPrettyPass {
    type Scope = VisibleGlobals;

    fn enter_block(
        &mut self,
        block: &mut AstBlock,
        _kind: BlockKind,
        outer_declared: &mut Self::Scope,
    ) -> bool {
        self.enter_scoped_block(block, outer_declared, None)
    }

    fn enter_repeat_body(
        &mut self,
        block: &mut AstBlock,
        condition: &crate::ast::common::AstExpr,
        lifetime: &crate::hir::HirRepeatConditionLifetimeFacts,
        outer_declared: &mut Self::Scope,
    ) -> bool {
        self.enter_scoped_block(block, outer_declared, Some((condition, lifetime)))
    }

    fn enter_stmt_children(&mut self, stmt: &crate::ast::common::AstStmt, scope: &mut Self::Scope) {
        scope.enter_stmt_children(stmt);
    }

    fn after_stmt(&mut self, stmt: &crate::ast::common::AstStmt, scope: &mut Self::Scope) {
        scope.apply_stmt(stmt);
    }
}

impl GlobalDeclPrettyPass {
    fn enter_scoped_block(
        &mut self,
        block: &mut AstBlock,
        outer_declared: &VisibleGlobals,
        trailing: Option<(
            &crate::ast::common::AstExpr,
            &crate::hir::HirRepeatConditionLifetimeFacts,
        )>,
    ) -> bool {
        // AST build 只消费 HIR 发布的 typed `HirGlobalDecl` 并验证目标语法；这里仅合并
        // singleton seed handoff，并在当前作用域已有 AST 显式 global gate 时再补
        // missing global。Lua 5.5 默认 `global *`，完全没有显式证据时不能凭观测补声明；
        // repeat condition 与 body 共用事实；collective owner 会按 condition 实际引用的
        // body local 精确判断 suffix 能否包进 do，而不是停用整个 repeat 候选集。
        let mut changed = merge_seed_global_runs(block);
        let facts = trailing.map_or_else(
            || BlockFacts::collect(block),
            |(condition, _)| BlockFacts::collect_repeat(block, condition),
        );
        let body_missing = facts.infer_body_missing(outer_declared);
        let mut missing = if !body_missing.is_empty()
            && !facts.has_explicit_globals()
            && try_wrap_missing_collective_suffix(
                block,
                &body_missing,
                trailing.map(|(condition, _)| condition),
                trailing.map(|(_, lifetime)| lifetime),
            ) {
            // 新 gate 位于 suffix 的 `do` 内，只覆盖 body 观测。until 条件仍在该 `do`
            // 外，必须把它自己的 missing 保留下来交给逐名声明 owner。
            changed = true;
            MissingGlobals::default()
        } else if facts.has_explicit_globals() || outer_declared.has_explicit_gate() {
            body_missing
        } else {
            return changed;
        };
        facts.extend_trailing_missing(outer_declared, &mut missing);
        if !missing.is_empty() {
            let insert_at = facts.missing_insert_at(outer_declared);
            insert_missing_global_decls(block, &missing, insert_at);
            changed = true;
        }

        changed
    }
}
