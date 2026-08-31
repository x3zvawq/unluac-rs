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

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirBlock, HirLValue, HirProto, HirStmt, ParamId, TempId};
use crate::hir::expr_safety::expr_is_discard_safe;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::temp_touch::collect_temp_reads_in_proto;
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn remove_dead_temp_materializations_in_proto(
    proto: &mut HirProto,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    let live_reads = collect_temp_reads_in_proto(proto);
    let parameters_by_home = proto
        .params
        .iter()
        .map(|param| (HomeSlotKey::new(param.index(), 0), *param))
        .collect::<BTreeMap<_, _>>();
    let parameter_by_temp = proto
        .temps
        .iter()
        .filter_map(|temp| {
            promotion_facts
                .home_slot(*temp)
                .and_then(|home| parameters_by_home.get(&home).copied())
                .map(|param| (*temp, param))
        })
        .collect();
    let physical_home_temps = proto
        .temps
        .iter()
        .filter(|temp| promotion_facts.home_slot(**temp).is_some())
        .copied()
        .collect();
    let debug_temps = proto
        .temps
        .iter()
        .zip(&proto.temp_debug_locals)
        .filter_map(|(temp, hint)| hint.as_ref().map(|_| *temp))
        .collect();
    let mut pass = DeadTempPass {
        live_reads: &live_reads,
        parameter_by_temp,
        physical_home_temps,
        debug_temps,
    };
    rewrite_proto(proto, &mut pass)
}

struct DeadTempPass<'a> {
    live_reads: &'a BTreeSet<TempId>,
    parameter_by_temp: BTreeMap<TempId, ParamId>,
    physical_home_temps: BTreeSet<TempId>,
    debug_temps: BTreeSet<TempId>,
}

impl HirRewritePass for DeadTempPass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let mut changed = false;
        block.stmts.retain_mut(|stmt| {
            let Some(temp) = dead_pure_temp_assignment(stmt, self.live_reads) else {
                return true;
            };
            // 候选拒绝[PolicyBoundary]：debug temp 是源码 binding；即使值无读取，删除定义也会抹掉项目选择保留的 source identity。
            if self.debug_temps.contains(&temp) {
                return true;
            }
            if let Some(param) = self.parameter_by_temp.get(&temp).copied() {
                let HirStmt::Assign(assign) = stmt else {
                    unreachable!("dead temp candidate must remain an assignment")
                };
                // raw home 证明该 SSA temp 实际覆盖参数槽；保留为参数赋值才能维持 regress_342 中可观察的 GC root 释放时点。
                assign.targets[0] = HirLValue::Param(param);
                changed = true;
                return true;
            }
            if self.physical_home_temps.contains(&temp) {
                // 候选拒绝[ProofIncomplete]：raw home temp 的纯死写仍可能释放旧槽位中的 GC root；需接入 reaching resource-value 与可见 binding 映射后再删除。
                return true;
            }
            changed = true;
            false
        });
        changed
    }
}

fn dead_pure_temp_assignment(stmt: &HirStmt, live_reads: &BTreeSet<TempId>) -> Option<TempId> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([HirLValue::Temp(temp)], [value]) =
        (assign.targets.as_slice(), assign.values.fixed.as_slice())
    else {
        return None;
    };
    // 候选拒绝[SemanticBarrier:ValueArity]：tail 即使不供目标取值仍必须求值；删除
    // `t = nil, side()` 会漏掉 `side()` 的调用和它的可观察结果宽度协议。
    if assign.values.tail.is_some() {
        return None;
    }
    // 候选拒绝[SemanticBarrier:Value]：仍被读取的 temp 定义决定后续值；删除
    // `t = 1; return t` 会把读取变成未定义槽。
    if live_reads.contains(temp) {
        return None;
    }
    // 候选拒绝[SemanticBarrier:EvalMultiplicity]：不可丢弃 RHS 必须求值一次；调用、
    // table/global lookup 或分配即使结果未读也可能执行用户代码、抛错或产生对象身份。
    expr_is_discard_safe(value).then_some(*temp)
}
