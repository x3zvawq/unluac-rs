//! 当前 AST 函数体的名字访问查询。
//!
//! 消费共享 visitor 的声明、读写和 capture 角色，不进入 child body。

use std::collections::BTreeSet;
use std::ops::ControlFlow;

use crate::ast::common::{
    AstBindingRef, AstBlock, AstExpr, AstFunctionExpr, AstLocalBinding, AstNameRef, AstStmt,
};
use crate::ast::visit::{self, AstVisitor, NameAccess};

#[derive(Debug, Default)]
pub(in crate::ast::readability) struct BindingRefSet {
    ids: BTreeSet<AstBindingRef>,
}

impl BindingRefSet {
    fn finder(&self) -> NameFinder<impl FnMut(&AstNameRef, NameAccess) -> bool + '_> {
        NameFinder::new(|name, _| {
            AstBindingRef::from_name_ref(name).is_some_and(|binding| self.ids.contains(&binding))
        })
    }

    pub(in crate::ast::readability) fn from_bindings(bindings: &[AstLocalBinding]) -> Self {
        Self {
            ids: bindings.iter().map(|binding| binding.id).collect(),
        }
    }
}

pub(in crate::ast::readability) fn stmt_references_binding_set(
    stmt: &AstStmt,
    bindings: &BindingRefSet,
) -> bool {
    bindings.finder().in_stmt(stmt)
}

pub(in crate::ast::readability) fn block_references_binding_set(
    block: &AstBlock,
    bindings: &BindingRefSet,
) -> bool {
    bindings.finder().in_block(block)
}

pub(in crate::ast::readability) fn expr_references_any_binding(
    expr: &AstExpr,
    bindings: &[AstLocalBinding],
) -> bool {
    expr_references_binding_set(expr, &BindingRefSet::from_bindings(bindings))
}

pub(in crate::ast::readability) fn expr_references_binding_set(
    expr: &AstExpr,
    bindings: &BindingRefSet,
) -> bool {
    bindings.finder().in_expr(expr)
}

/// 只查直属声明是否被当前函数内的 closure 捕获；子块声明不属于本块的结束边界。
pub(in crate::ast::readability) fn block_captures_direct_local(block: &AstBlock) -> bool {
    let direct_bindings = block
        .stmts
        .iter()
        .flat_map(AstStmt::local_bindings)
        .map(|binding| binding.id)
        .collect::<BTreeSet<_>>();
    !direct_bindings.is_empty()
        && NameFinder::new(|name, access| {
            matches!(access, NameAccess::Capture)
                && AstBindingRef::from_name_ref(name)
                    .is_some_and(|binding| direct_bindings.contains(&binding))
        })
        .in_block(block)
}

pub(in crate::ast::readability) fn expr_reads_name(expr: &AstExpr, target: &AstNameRef) -> bool {
    NameFinder::new(|name, access| matches!(access, NameAccess::Read) && name == target)
        .in_expr(expr)
}

pub(in crate::ast::readability) fn expr_reads_binding(
    expr: &AstExpr,
    binding: AstBindingRef,
) -> bool {
    expr_has_binding_read(expr, |read| read == binding)
}

pub(in crate::ast::readability) fn expr_has_binding_read(
    expr: &AstExpr,
    mut accepts: impl FnMut(AstBindingRef) -> bool,
) -> bool {
    NameFinder::new(|name, access| {
        matches!(access, NameAccess::Read)
            && AstBindingRef::from_name_ref(name).is_some_and(&mut accepts)
    })
    .in_expr(expr)
}

pub(in crate::ast::readability) fn expr_uses_binding(
    expr: &AstExpr,
    binding: AstBindingRef,
) -> bool {
    use_finder(binding).in_expr(expr)
}

pub(in crate::ast::readability) fn stmt_uses_binding(
    stmt: &AstStmt,
    binding: AstBindingRef,
) -> bool {
    use_finder(binding).in_stmt(stmt)
}

pub(in crate::ast::readability) fn stmt_writes_name(stmt: &AstStmt, target: &AstNameRef) -> bool {
    NameFinder::new(|name, access| matches!(access, NameAccess::Write) && name == target)
        .in_stmt(stmt)
}

fn use_finder(binding: AstBindingRef) -> NameFinder<impl FnMut(&AstNameRef, NameAccess) -> bool> {
    NameFinder::new(move |name, access| {
        matches!(access, NameAccess::Read | NameAccess::Capture) && binding.matches_name_ref(name)
    })
}

struct NameFinder<F> {
    predicate: F,
    found: bool,
}

impl<F: FnMut(&AstNameRef, NameAccess) -> bool> NameFinder<F> {
    fn new(predicate: F) -> Self {
        Self {
            predicate,
            found: false,
        }
    }

    fn in_stmt(mut self, stmt: &AstStmt) -> bool {
        visit::visit_stmt(stmt, &mut self);
        self.found
    }

    fn in_expr(mut self, expr: &AstExpr) -> bool {
        visit::visit_expr(expr, &mut self);
        self.found
    }

    fn in_block(mut self, block: &AstBlock) -> bool {
        visit::visit_block(block, &mut self);
        self.found
    }
}

impl<F: FnMut(&AstNameRef, NameAccess) -> bool> AstVisitor for NameFinder<F> {
    fn visit_name(&mut self, name: &AstNameRef, access: NameAccess) -> ControlFlow<()> {
        if (self.predicate)(name, access) {
            self.found = true;
            ControlFlow::Break(())
        } else {
            ControlFlow::Continue(())
        }
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}
