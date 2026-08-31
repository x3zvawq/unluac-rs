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

use crate::hir::common::{HirBlock, HirLValue, HirProto, HirStmt, TempId};
use crate::hir::expr_safety::expr_is_discard_safe;

use super::temp_touch::collect_temp_reads_in_proto;
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn remove_dead_temp_materializations_in_proto(proto: &mut HirProto) -> bool {
    let live_reads = collect_temp_reads_in_proto(proto);
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

fn is_dead_pure_temp_assignment(stmt: &HirStmt, live_reads: &BTreeSet<TempId>) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let ([HirLValue::Temp(temp)], [value]) =
        (assign.targets.as_slice(), assign.values.fixed.as_slice())
    else {
        return false;
    };
    // 候选拒绝[SemanticBarrier:ValueArity]：tail 即使不供目标取值仍必须求值；删除
    // `t = nil, side()` 会漏掉 `side()` 的调用和它的可观察结果宽度协议。
    if assign.values.tail.is_some() {
        return false;
    }
    // 候选拒绝[SemanticBarrier:Value]：仍被读取的 temp 定义决定后续值；删除
    // `t = 1; return t` 会把读取变成未定义槽。
    if live_reads.contains(temp) {
        return false;
    }
    // 候选拒绝[SemanticBarrier:EvalMultiplicity]：不可丢弃 RHS 必须求值一次；调用、
    // table/global lookup 或分配即使结果未读也可能执行用户代码、抛错或产生对象身份。
    expr_is_discard_safe(value)
}
