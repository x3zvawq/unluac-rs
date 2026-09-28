//! 校验 AST 中 capture 与 local 声明的层间合同。
//!
//! 消费显式 binding 身份及词法顺序，供 AST build 和 Readability 出口共享。

use std::collections::BTreeMap;

use super::common::{AstBindingRef, AstBlock, AstExpr, AstFunctionExpr, AstModule, AstStmt};
use super::error::AstLowerError;
use super::traverse::BlockKind;
use super::visit::{self, AstVisitor};

pub(super) fn verify_forward_local_captures(module: &AstModule) -> Result<(), AstLowerError> {
    verify_block(module.entry_function.index(), &module.body)
}

fn verify_block(function: usize, block: &AstBlock) -> Result<(), AstLowerError> {
    let declarations = block
        .stmts
        .iter()
        .enumerate()
        .flat_map(|(index, stmt)| match stmt {
            AstStmt::LocalDecl(decl) => decl
                .bindings
                .iter()
                .map(move |binding| (binding.id, index))
                .collect::<Vec<_>>(),
            AstStmt::LocalFunctionDecl(decl) => vec![(decl.name, index)],
            _ => Vec::new(),
        })
        .collect::<BTreeMap<_, _>>();

    for (index, stmt) in block.stmts.iter().enumerate() {
        verify_direct_local_closure(function, index, stmt, &declarations)?;
        let mut children = ChildScopes {
            function,
            result: Ok(()),
        };
        visit::visit_stmt(stmt, &mut children);
        children.result?;
    }
    Ok(())
}

fn verify_direct_local_closure(
    function: usize,
    index: usize,
    stmt: &AstStmt,
    declarations: &BTreeMap<AstBindingRef, usize>,
) -> Result<(), AstLowerError> {
    let (closures, self_binding) = match stmt {
        AstStmt::LocalDecl(decl) => {
            let closures = decl.values.iter().filter_map(|value| match value {
                AstExpr::FunctionExpr(function) => Some(function.as_ref()),
                _ => None,
            });
            (closures.collect::<Vec<_>>(), None)
        }
        AstStmt::LocalFunctionDecl(decl) => (vec![&decl.func], Some(decl.name)),
        _ => return Ok(()),
    };

    for closure in closures {
        for &capture in &closure.captured_bindings {
            let valid = declarations
                .get(&capture)
                .is_none_or(|&declaration| declaration < index)
                || declarations.get(&capture) == Some(&index) && self_binding == Some(capture);
            if !valid {
                return Err(AstLowerError::InvalidForwardLocalCapture {
                    function,
                    binding: capture,
                });
            }
        }
    }
    Ok(())
}

/// 当前 block 的声明表只用于直属语句；子函数切换身份后建立自己的声明域。
struct ChildScopes {
    function: usize,
    result: Result<(), AstLowerError>,
}

impl AstVisitor for ChildScopes {
    fn visit_block(&mut self, block: &AstBlock, _kind: BlockKind) -> bool {
        if self.result.is_ok() {
            self.result = verify_block(self.function, block);
        }
        false
    }

    fn visit_function_expr(&mut self, function: &AstFunctionExpr) -> bool {
        if self.result.is_ok() {
            self.result = verify_block(function.function.index(), &function.body);
        }
        false
    }
}
