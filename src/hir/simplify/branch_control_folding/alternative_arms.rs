//! 合并互斥且语义结构完全相同的分支，保留所有读取来源。
//!
//! 这里仅撤销用于选择同一操作的外层条件；条件求值/控制入口/声明身份仍由 branch-control
//! 原事务检查。读取的 base、key、metamethod 与 method 协议必须相同，只有 sources 可不同。
//! 例如 `if p then if t[k] then break end else if t[k] then break end end` 合并为一次读取，
//! 结果槽与输入布局仍由 Promotion 对两处 GETTABLE 求交，不继承任一分支的单点许可。

use crate::hir::common::{HirBlock, HirExpr, HirOperationSources};
use crate::hir::simplify::walk::{HirRewritePass, rewrite_block};
use crate::hir::visit::{HirVisitor, visit_block};

pub(super) type ReadAlternativeCache = crate::hir::common::HirSourceFactsCache<(
    crate::hir::promotion::HomeSlotKey,
    crate::hir::promotion::NativeTableReadLayout,
)>;

pub(super) fn merge_read_alternatives(
    left: &HirBlock,
    right: &HirBlock,
    facts: &crate::hir::promotion::ProtoPromotionFacts,
    cache: &mut ReadAlternativeCache,
) -> Option<HirBlock> {
    if left.stmts.len() != right.stmts.len() || !same_node_count(left, right) {
        return None;
    }
    struct Sources(Vec<HirOperationSources>);
    impl HirVisitor<'_> for Sources {
        fn visit_expr(&mut self, expr: &HirExpr) {
            if let HirExpr::TableAccess(access) = expr {
                self.0.push(access.sources.clone());
            }
        }
    }
    let mut sources = Sources(Vec::new());
    visit_block(right, &mut sources);
    if sources.0.is_empty() {
        return None;
    }

    struct Project<'a> {
        sources: &'a [HirOperationSources],
        merged: Vec<HirOperationSources>,
        index: usize,
        merge: bool,
    }
    impl HirRewritePass for Project<'_> {
        const PRESERVES_GENERIC_FOR_INITIALIZER_TRANSACTION: bool = true;
        fn rewrite_expr_before_children(&mut self, expr: &mut HirExpr) -> bool {
            let HirExpr::TableAccess(access) = expr else {
                return false;
            };
            let index = self.index;
            self.index += 1;
            let Some(source) = self.sources.get(index) else {
                return false;
            };
            if self.merge {
                self.merged.push(access.sources.alternatives(source));
            }
            access.sources = source.clone();
            true
        }
    }
    // 一次克隆和两次相同 visitor 顺序投影。第一次只消除 metadata 差别供严格结构相等
    // 校验；若失败则丢弃整个候选，不能留下部分 source 合并。第二次才发布持久来源 DAG。
    let mut candidate = left.clone();
    let mut project = Project {
        sources: &sources.0,
        merged: Vec::new(),
        index: 0,
        merge: true,
    };
    rewrite_block(&mut candidate, &mut project);
    if project.index != sources.0.len() || candidate != *right {
        return None;
    }
    // 同一 pass 快照内按来源 DAG 归约；逐层合并只有新增的来源需要核对。
    for sources in &project.merged {
        cache.common_fact(sources, |site| {
            if !facts.operation_result_reference_unaliased(site) {
                return None;
            }
            Some((
                facts.operation_result_home(site)?,
                facts.native_table_read_layout_at(site)?,
            ))
        })?;
    }
    let mut commit = Project {
        sources: &project.merged,
        merged: Vec::new(),
        index: 0,
        merge: false,
    };
    rewrite_block(&mut candidate, &mut commit);
    Some(candidate)
}

/// 用相同的递增预算同时扫描两臂；任一臂先结束即可拒绝。因此单边深链的每个父 If
/// 不会反复克隆/全扫较长子树，工作量受较短一侧限制，而非任选右臂作无界基准。
fn same_node_count(left: &HirBlock, right: &HirBlock) -> bool {
    struct Count {
        remaining: usize,
    }
    impl HirVisitor<'_> for Count {
        fn is_complete(&self) -> bool {
            self.remaining == 0
        }
        fn visit_block(&mut self, _: &HirBlock) {
            self.remaining -= 1;
        }
        fn visit_stmt(&mut self, _: &crate::hir::common::HirStmt) {
            self.remaining -= 1;
        }
        fn visit_expr(&mut self, _: &HirExpr) {
            self.remaining -= 1;
        }
        fn visit_lvalue(&mut self, _: &crate::hir::common::HirLValue) {
            self.remaining -= 1;
        }
        fn visit_call(&mut self, _: &crate::hir::common::HirCallExpr) {
            self.remaining -= 1;
        }
    }
    let mut budget = 8usize;
    loop {
        let mut lhs = Count { remaining: budget };
        let mut rhs = Count { remaining: budget };
        visit_block(left, &mut lhs);
        visit_block(right, &mut rhs);
        if lhs.remaining != 0 || rhs.remaining != 0 {
            return lhs.remaining == rhs.remaining;
        }
        budget = budget.saturating_mul(2);
    }
}
