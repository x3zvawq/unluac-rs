//! 这个文件负责清理 simplify 出口上已经没有任何读取者的 unresolved temp 物化。
//!
//! 结构层在 block 入口会先把一批 phi/temp 物化出来，后续 branch/loop/readability pass
//! 再把真正活着的那部分折进源码结构。对大函数来说，最后常会留下“只赋值一次、后面从未
//! 再读”的机械 temp 壳；它们继续留在 HIR 里不仅会制造残余 unresolved warning，
//! 还会直接挡住 AST lowering。
//!
//! 这里刻意只删“目标 temp 全局无读者，且 RHS 本身就是 unresolved placeholder”的
//! 那一类语句，不会越权移除任意 dead assign，更不会吞掉可能带副作用的表达式。

use std::collections::BTreeSet;

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirProto, HirStmt, TempId};

use super::visit::{HirVisitor, visit_proto};
use super::walk::{HirRewritePass, rewrite_proto};

#[cfg(test)]
mod tests;

pub(super) fn remove_dead_unresolved_temp_materializations_in_proto(proto: &mut HirProto) -> bool {
    let live_reads = collect_live_temp_reads(proto);
    let mut pass = DeadUnresolvedTempPass {
        live_reads: &live_reads,
    };
    rewrite_proto(proto, &mut pass)
}

struct DeadUnresolvedTempPass<'a> {
    live_reads: &'a BTreeSet<TempId>,
}

impl HirRewritePass for DeadUnresolvedTempPass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let original_len = block.stmts.len();
        block.stmts.retain(|stmt| !is_dead_unresolved_temp_materialization(stmt, self.live_reads));
        block.stmts.len() != original_len
    }
}

fn collect_live_temp_reads(proto: &HirProto) -> BTreeSet<TempId> {
    let mut collector = TempReadCollector::default();
    visit_proto(proto, &mut collector);
    collector.reads
}

#[derive(Default)]
struct TempReadCollector {
    reads: BTreeSet<TempId>,
}

impl HirVisitor for TempReadCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::TempRef(temp) = expr {
            self.reads.insert(*temp);
        }
    }
}

fn is_dead_unresolved_temp_materialization(stmt: &HirStmt, live_reads: &BTreeSet<TempId>) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    matches!(
        (assign.targets.as_slice(), assign.values.as_slice()),
        ([HirLValue::Temp(temp)], [HirExpr::Unresolved(_)]) if !live_reads.contains(temp)
    )
}
