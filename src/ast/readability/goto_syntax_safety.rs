//! goto 方言中 `return`/`break` 后仍有 label 时的块尾语法合法化。
//!
//! `return` 必须是当前 block 的最后一条语句；LuaJIT 对 `break` 也有同类限制。
//! island 的多个 terminal target 会让同层 block 在终止语句后继续发射 label，因此
//! 把非末尾终止语句包进窄 `do ... end`，既保留控制流，也满足所有 goto 方言语法。

use super::super::common::{AstBlock, AstModule, AstStmt};
use super::ReadabilityContext;
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    if !context.target.caps.goto_label {
        return false;
    }
    walk::rewrite_module(module, &mut GotoSyntaxSafetyPass)
}

struct GotoSyntaxSafetyPass;

impl AstRewritePass for GotoSyntaxSafetyPass {
    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        let statement_count = block.stmts.len();
        if statement_count < 2
            || !block.stmts[..statement_count - 1]
                .iter()
                .any(|stmt| matches!(stmt, AstStmt::Return(_) | AstStmt::Break))
        {
            return false;
        }

        block.stmts = std::mem::take(&mut block.stmts)
            .into_iter()
            .enumerate()
            .map(|(index, stmt)| {
                if index + 1 < statement_count
                    && matches!(&stmt, AstStmt::Return(_) | AstStmt::Break)
                {
                    AstStmt::DoBlock(Box::new(AstBlock { stmts: vec![stmt] }))
                } else {
                    stmt
                }
            })
            .collect();
        true
    }
}
