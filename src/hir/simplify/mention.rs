//! HIR simplify 里的 binding/temp 提及查询。
//!
//! 多个 pass 都需要回答“某段 HIR 是否还引用某个 local/temp”以及“某条语句是否写入
//! temp”。这些问题属于只读树遍历，不应散落在各个 pass 里各写一套 visitor。
//! 本模块只提供语法树提及事实，不判断 carried-local、branch-value 等业务形状。

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirStmt, LocalId, TempId};

use super::visit::{HirVisitor, visit_block, visit_expr, visit_stmts};

pub(super) fn stmts_mention_local(stmts: &[HirStmt], local: LocalId) -> bool {
    LocalMentionCollector::mentions_in_stmts(stmts, local)
}

pub(super) fn block_mentions_local(block: &HirBlock, local: LocalId) -> bool {
    LocalMentionCollector::mentions_in_block(block, local)
}

pub(super) fn expr_mentions_local(expr: &HirExpr, local: LocalId) -> bool {
    LocalMentionCollector::mentions_in_expr(expr, local)
}

pub(super) fn stmt_captures_local(stmt: &HirStmt, local: LocalId) -> bool {
    LocalCaptureCollector::captures_in_stmt(stmt, local)
}

pub(super) fn stmts_mention_temp(stmts: &[HirStmt], temp: TempId) -> bool {
    TempMentionCollector::mentions_in_stmts(stmts, temp)
}

pub(super) fn stmt_writes_temp(stmt: &HirStmt, temp: TempId) -> bool {
    TempWriteCollector::writes_in_stmt(stmt, temp)
}

struct LocalMentionCollector {
    local: LocalId,
    mentioned: bool,
}

impl LocalMentionCollector {
    fn mentions_in_stmts(stmts: &[HirStmt], local: LocalId) -> bool {
        let mut collector = Self {
            local,
            mentioned: false,
        };
        visit_stmts(stmts, &mut collector);
        collector.mentioned
    }

    fn mentions_in_block(block: &HirBlock, local: LocalId) -> bool {
        let mut collector = Self {
            local,
            mentioned: false,
        };
        visit_block(block, &mut collector);
        collector.mentioned
    }

    fn mentions_in_expr(expr: &HirExpr, local: LocalId) -> bool {
        let mut collector = Self {
            local,
            mentioned: false,
        };
        visit_expr(expr, &mut collector);
        collector.mentioned
    }
}

impl HirVisitor for LocalMentionCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.mentioned |= matches!(expr, HirExpr::LocalRef(local) if *local == self.local);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.mentioned |= matches!(lvalue, HirLValue::Local(local) if *local == self.local);
    }
}

struct LocalCaptureCollector {
    local: LocalId,
    captured: bool,
}

impl LocalCaptureCollector {
    fn captures_in_stmt(stmt: &HirStmt, local: LocalId) -> bool {
        let mut collector = Self {
            local,
            captured: false,
        };
        visit_stmts(std::slice::from_ref(stmt), &mut collector);
        collector.captured
    }
}

impl HirVisitor for LocalCaptureCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::Closure(closure) = expr {
            self.captured |= closure
                .captures
                .iter()
                .any(|capture| expr_mentions_local(&capture.value, self.local));
        }
    }
}

struct TempMentionCollector {
    temp: TempId,
    mentioned: bool,
}

impl TempMentionCollector {
    fn mentions_in_stmts(stmts: &[HirStmt], temp: TempId) -> bool {
        let mut collector = Self {
            temp,
            mentioned: false,
        };
        visit_stmts(stmts, &mut collector);
        collector.mentioned
    }
}

impl HirVisitor for TempMentionCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.mentioned |= matches!(expr, HirExpr::TempRef(temp) if *temp == self.temp);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.mentioned |= matches!(lvalue, HirLValue::Temp(temp) if *temp == self.temp);
    }
}

struct TempWriteCollector {
    temp: TempId,
    written: bool,
}

impl TempWriteCollector {
    fn writes_in_stmt(stmt: &HirStmt, temp: TempId) -> bool {
        let mut collector = Self {
            temp,
            written: false,
        };
        visit_stmts(std::slice::from_ref(stmt), &mut collector);
        collector.written
    }
}

impl HirVisitor for TempWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.written |= matches!(lvalue, HirLValue::Temp(temp) if *temp == self.temp);
    }
}
