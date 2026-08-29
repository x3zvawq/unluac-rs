//! 终止语句之后仍需保留 sibling 时的块尾语法合法化。
//!
//! Lua 要求 `return`/`break`/`continue` 位于所属语法块的尾部。island 的
//! terminal target 会在后面留下 label；branch-control 也会按项目策略保留
//! 不可达的 debug/diagnostic sibling。本 pass 在 cleanup 完成后查看最终相邻关系，
//! 只把非末尾终止语句包进窄 `do ... end`，不重建 HIR 控制 owner。
//!
//! 例如 `break; local kept` 会生成 `do break end; local kept`；本就在 block
//! 尾部的 `break` 保持不变。

use super::super::common::{AstBlock, AstModule, AstStmt};
use super::ReadabilityContext;
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    walk::rewrite_module(module, &mut GotoSyntaxSafetyPass)
}

struct GotoSyntaxSafetyPass;

impl AstRewritePass for GotoSyntaxSafetyPass {
    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        let statement_count = block.stmts.len();
        if statement_count < 2
            || !block.stmts[..statement_count - 1]
                .iter()
                .any(is_terminal_last_statement)
        {
            return false;
        }

        block.stmts = std::mem::take(&mut block.stmts)
            .into_iter()
            .enumerate()
            .map(|(index, stmt)| {
                if index + 1 < statement_count && is_terminal_last_statement(&stmt) {
                    AstStmt::DoBlock(Box::new(AstBlock { stmts: vec![stmt] }))
                } else {
                    stmt
                }
            })
            .collect();
        true
    }
}

fn is_terminal_last_statement(stmt: &AstStmt) -> bool {
    matches!(
        stmt,
        AstStmt::Return(_) | AstStmt::Break | AstStmt::Continue
    )
}
