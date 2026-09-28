//! 为块尾终止语句之后仍有 sibling 的 AST 补齐合法语法作用域。
//!
//! 消费 cleanup 后的最终相邻关系，保留原控制 owner 与后续语句。

use super::super::common::{AstBlock, AstModule, AstStmt};
use super::ReadabilityContext;
use super::walk::{self, AstRewritePass};
use crate::ast::traverse::BlockKind;

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
