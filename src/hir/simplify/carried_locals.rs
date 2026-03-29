//! 这个文件负责把 fallback label/goto 区域里“交棒给 temp 的 local”认回原绑定。
//!
//! 某些 `<close> + goto` 形状因为暂时无法整体结构化，只能先在 HIR 里保留成
//! `assign tX = lY; ... label/goto ...; tX = ...` 这样的状态 temp。语义虽然对，
//! 但它会把本来是同一个源码 local 的身份拆成“两段 binding”，最终长成
//! `local turn = 1; do state = turn; ... state = state + 1 end` 这种机械形状。
//!
//! 这个 pass 只吃一个很窄的 handoff：
//! - seed 必须是单目标 `assign tX = lY`
//! - seed 之后的当前 block 里，`lY` 自己不再出现
//! - `tX` 在 seed 之后确实继续承担后续读写
//!
//! 满足这几个条件时，说明这个 block 已经把“后半段状态身份”完全交给了 temp；
//! 这里把它认回原 local，删掉 handoff seed。它不会发明新 local，也不会在原 local
//! 仍然活跃时强行合并两段状态。
//!
//! 例子：
//! - 输入：`local l0 = 1; do t4 = l0; ::L1:: if t4 < 3 then t4 = t4 + 1; goto L1 end end`
//! - 输出：`local l0 = 1; do ::L1:: if l0 < 3 then l0 = l0 + 1; goto L1 end end`

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirProto, HirStmt, LocalId, TempId};

use super::visit::{HirVisitor, visit_stmts};
use super::walk::{HirRewritePass, rewrite_proto, rewrite_stmts};

pub(super) fn collapse_carried_local_handoffs_in_proto(proto: &mut HirProto) -> bool {
    rewrite_proto(proto, &mut CarriedLocalPass)
}

struct CarriedLocalPass;

impl HirRewritePass for CarriedLocalPass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        collapse_block_handoffs(block)
    }
}

fn collapse_block_handoffs(block: &mut HirBlock) -> bool {
    let mut changed = false;
    let mut index = 0;

    while index < block.stmts.len() {
        let Some((temp, local)) = local_handoff_seed(&block.stmts[index]) else {
            index += 1;
            continue;
        };

        let suffix = &block.stmts[index + 1..];
        if suffix.is_empty()
            || suffix_mentions_local(suffix, local)
            || !suffix_mentions_temp(suffix, temp)
        {
            index += 1;
            continue;
        }

        let mut pass = TempToLocalPass { temp, local };
        let rewritten = rewrite_stmts(&mut block.stmts[index + 1..], &mut pass);
        if !rewritten {
            index += 1;
            continue;
        }

        block.stmts.remove(index);
        changed = true;
    }

    changed
}

fn local_handoff_seed(stmt: &HirStmt) -> Option<(TempId, LocalId)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(temp)] = assign.targets.as_slice() else {
        return None;
    };
    let [HirExpr::LocalRef(local)] = assign.values.as_slice() else {
        return None;
    };
    Some((*temp, *local))
}

fn suffix_mentions_local(stmts: &[HirStmt], local: LocalId) -> bool {
    let mut collector = LocalMentionCollector {
        local,
        mentioned: false,
    };
    visit_stmts(stmts, &mut collector);
    collector.mentioned
}

fn suffix_mentions_temp(stmts: &[HirStmt], temp: TempId) -> bool {
    let mut collector = TempMentionCollector {
        temp,
        mentioned: false,
    };
    visit_stmts(stmts, &mut collector);
    collector.mentioned
}

struct TempToLocalPass {
    temp: TempId,
    local: LocalId,
}

impl HirRewritePass for TempToLocalPass {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        let HirExpr::TempRef(temp) = expr else {
            return false;
        };
        if *temp != self.temp {
            return false;
        }
        *expr = HirExpr::LocalRef(self.local);
        true
    }

    fn rewrite_lvalue(&mut self, lvalue: &mut HirLValue) -> bool {
        let HirLValue::Temp(temp) = lvalue else {
            return false;
        };
        if *temp != self.temp {
            return false;
        }
        *lvalue = HirLValue::Local(self.local);
        true
    }
}

struct LocalMentionCollector {
    local: LocalId,
    mentioned: bool,
}

impl HirVisitor for LocalMentionCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.mentioned |= matches!(expr, HirExpr::LocalRef(local) if *local == self.local);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.mentioned |= matches!(lvalue, HirLValue::Local(local) if *local == self.local);
    }
}

struct TempMentionCollector {
    temp: TempId,
    mentioned: bool,
}

impl HirVisitor for TempMentionCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.mentioned |= matches!(expr, HirExpr::TempRef(temp) if *temp == self.temp);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.mentioned |= matches!(lvalue, HirLValue::Temp(temp) if *temp == self.temp);
    }
}

#[cfg(test)]
mod tests;
