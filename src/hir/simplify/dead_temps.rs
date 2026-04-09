//! 这个文件负责清理 simplify 出口上已经没有任何读取者的无副作用 temp 赋值。
//!
//! 结构层在 block 入口会先把一批 phi/temp 物化出来，后续 branch/loop/readability pass
//! 再把真正活着的那部分折进源码结构。对大函数来说，最后常会留下"只赋值一次、后面从未
//! 再读"的机械 temp 壳；它们继续留在 HIR 里不仅会制造残余 unresolved warning，
//! 还会直接挡住 AST lowering。
//!
//! 清理范围：目标 temp 全局无读者，且 RHS 不含潜在副作用（调用、metamethod 触发、
//! table 构造等）的赋值语句。对于可能带 side-effect 的 RHS（函数调用、table access
//! 等），即使 temp 无读者也必须保留，避免丢失语义。

use std::collections::BTreeSet;

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirProto, HirStmt, TempId};

use super::visit::{HirVisitor, visit_proto};
use super::walk::{HirRewritePass, rewrite_proto};

#[cfg(test)]
mod tests;

pub(super) fn remove_dead_temp_materializations_in_proto(proto: &mut HirProto) -> bool {
    let live_reads = collect_live_temp_reads(proto);
    let mut pass = DeadTempPass {
        live_reads: &live_reads,
    };
    rewrite_proto(proto, &mut pass)
}

struct DeadTempPass<'a> {
    live_reads: &'a BTreeSet<TempId>,
}

impl HirRewritePass for DeadTempPass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let original_len = block.stmts.len();
        block
            .stmts
            .retain(|stmt| !is_dead_pure_temp_assignment(stmt, self.live_reads));
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

fn is_dead_pure_temp_assignment(stmt: &HirStmt, live_reads: &BTreeSet<TempId>) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let ([HirLValue::Temp(temp)], [value]) = (assign.targets.as_slice(), assign.values.as_slice())
    else {
        return false;
    };
    !live_reads.contains(temp) && is_pure_value(value)
}

/// RHS 不含任何潜在副作用时返回 true。
///
/// Lua 里 table access 可能触发 `__index`，算术/比较可能触发 metamethod，
/// 函数调用当然有副作用 —— 这些都不能安全删除。只有确定无副作用的常量和引用可以消除。
fn is_pure_value(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Complex { .. }
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
            | HirExpr::GlobalRef(_)
            | HirExpr::VarArg
            | HirExpr::Unresolved(_)
    )
}
