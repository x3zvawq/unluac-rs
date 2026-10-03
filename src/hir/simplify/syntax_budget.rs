//! 约束 HIR 一元表达式拼接后的源码语法规模。
//! 临时值内联与完整帧恢复共用预算，保留目标解析器需要的表达式分段。

use crate::hir::common::{HirExpr, HirStmt};
use crate::hir::visit::{HirVisitor, visit_expr, visit_stmt_header};

// PUC 的语法递归上限约为 200；为外围调用、控制结构和源码投影留出余量。
// 只约束一元链的拼接；左结合算术的长度不等于解析递归深度。
// 节点预算保守覆盖一元嵌套，每次查询最多访问固定数量节点。
const INLINE_SYNTAX_NODE_BUDGET: usize = 128;

struct InlineSyntaxBudget(usize);

impl HirVisitor<'_> for InlineSyntaxBudget {
    fn is_complete(&self) -> bool {
        self.0 == 0
    }

    fn visit_expr(&mut self, _expr: &HirExpr) {
        self.0 -= 1;
    }
}

pub(super) fn inline_syntax_budget(sink: &HirStmt) -> usize {
    let mut budget = InlineSyntaxBudget(INLINE_SYNTAX_NODE_BUDGET);
    visit_stmt_header(sink, &mut budget);
    budget.0
}

pub(super) fn spend_inline_syntax_budget(value: &HirExpr, remaining: usize) -> Option<usize> {
    // 代换移除一个 TempRef 叶子；至少留一格，区分刚好到界与提前终止遍历。
    let mut budget = InlineSyntaxBudget(remaining + 1);
    visit_expr(value, &mut budget);
    (budget.0 != 0).then_some(budget.0)
}

pub(super) fn inline_expansion_budget(sink: &HirStmt, value: &HirExpr) -> Option<usize> {
    if matches!(value, HirExpr::Unary(_)) {
        spend_inline_syntax_budget(value, inline_syntax_budget(sink))
    } else {
        Some(INLINE_SYNTAX_NODE_BUDGET)
    }
}

pub(super) fn unary_frame_fits(value: &HirExpr) -> bool {
    if !matches!(value, HirExpr::Unary(_)) {
        return true;
    }
    let mut budget = InlineSyntaxBudget(INLINE_SYNTAX_NODE_BUDGET);
    visit_expr(value, &mut budget);
    budget.0 != 0
}
