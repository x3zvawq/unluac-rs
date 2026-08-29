use super::super::common::{AstBlock, AstFunctionExpr, AstStmt};
use super::visit::{self, AstVisitor};

struct LabelOrGotoVisitor(bool);

impl AstVisitor for LabelOrGotoVisitor {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        self.0 |= matches!(stmt, AstStmt::Label(_) | AstStmt::Goto(_));
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}

pub(super) fn block_contains_label_or_goto(block: &AstBlock) -> bool {
    let mut visitor = LabelOrGotoVisitor(false);
    visit::visit_block(block, &mut visitor);
    visitor.0
}

pub(super) fn stmt_contains_label_or_goto(stmt: &AstStmt) -> bool {
    let mut visitor = LabelOrGotoVisitor(false);
    visit::visit_stmt(stmt, &mut visitor);
    visitor.0
}
