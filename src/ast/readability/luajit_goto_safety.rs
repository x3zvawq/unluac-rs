//! LuaJIT 对 `return`/`break` 的块尾约束比我们当前 AST fallback 更敏感。
//!
//! 当 block 里还有后续 label/goto 需要继续承载控制流时，直接把 `return` 或 `break`
//! 留在同一层 block 中会导致 LuaJIT parser 在后续 `::label::` 处报语法错误。
//! 这里把这类终止语句包进一个窄 `do ... end`，既保留控制流，又满足目标语法。

use super::super::common::{AstBlock, AstModule, AstStmt};
use super::ReadabilityContext;
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    if context.target.version != crate::ast::AstDialectVersion::LuaJit {
        return false;
    }
    walk::rewrite_module(module, &mut LuajitGotoSafetyPass)
}

struct LuajitGotoSafetyPass;

impl AstRewritePass for LuajitGotoSafetyPass {
    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        let needs_wrap = block
            .stmts
            .iter()
            .enumerate()
            .filter_map(|(index, stmt)| {
                matches!(stmt, AstStmt::Return(_) | AstStmt::Break).then_some(index)
            })
            .collect::<Vec<_>>();

        let mut changed = false;
        for index in needs_wrap.into_iter().rev() {
            if index + 1 >= block.stmts.len() {
                continue;
            }
            let stmt = block.stmts.remove(index);
            block.stmts.insert(
                index,
                AstStmt::DoBlock(Box::new(AstBlock { stmts: vec![stmt] })),
            );
            changed = true;
        }

        changed
    }
}
