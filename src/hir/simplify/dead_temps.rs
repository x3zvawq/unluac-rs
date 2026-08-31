//! 这个文件负责清理 simplify 出口上已经没有任何读取者的无副作用 temp 赋值。
//!
//! 结构层在 block 入口会先把一批 phi/temp 物化出来，后续 branch/loop/readability pass
//! 再把真正活着的那部分折进源码结构。对大函数来说，最后常会留下"只赋值一次、后面从未
//! 再读"的机械 temp 壳；它们继续留在 HIR 里不仅会制造残余 unresolved warning，
//! 还会直接挡住 AST lowering。
//!
//! 清理范围：目标 temp 全局无读者，且 RHS 不含潜在副作用（调用、metamethod 触发、
//! table 构造等）的赋值语句。它依赖 promotion 保存的物理 home 与 entry-nil provenance：
//! 无物理 home 的纯死写可直接删除；参数同槽写改回参数赋值；proto 根直线前缀中
//! `entry nil -> GC-inert value` 的写入也可删除。其余有 home 的写入不在这里猜 reaching
//! value，因为它仍可能决定旧对象或新对象的 GC root 生命周期。
//!
//! 例子：根前缀里的机械 `t = false` 若 `t` 是非参数槽首个 fixed def，可删成空；
//! `t = p` 即使没有值读取也不能删，因为该物理槽可能让 `p` 指向的对象继续存活。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirProto, HirStmt, ParamId, TempId};
use crate::hir::expr_safety::{expr_is_discard_safe, expr_result_is_gc_inert};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::mention::stmts_reference_captured_bindings;
use super::temp_touch::{collect_temp_reads_in_proto, stmt_contains_nested_nonlocal_control};
use super::visit::{self, HirVisitor};
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn remove_dead_temp_materializations_in_proto(
    proto: &mut HirProto,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    let live_reads = collect_temp_reads_in_proto(proto);
    let parameters_by_home = proto
        .params
        .iter()
        .filter_map(|param| {
            promotion_facts
                .trusted_param_home_slot(*param)
                .map(|home| (home, *param))
        })
        .collect::<BTreeMap<_, _>>();
    let parameter_by_temp = proto
        .temps
        .iter()
        .filter_map(|temp| {
            promotion_facts
                .trusted_temp_home_slot(*temp)
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
    let reference_captured = stmts_reference_captured_bindings(&proto.body.stmts);
    // 参数覆盖在本 pass 入口可能仍是写同 home 的 Local/Temp，不能只扫描已经语法化成
    // HirLValue::Param 的目标；缺可信 home 的直接 binding 写也不能用于稳定性正证明。
    let overwritten_visible_params = proto
        .params
        .iter()
        .filter(|param| {
            promotion_facts.trusted_param_home_slot(**param).is_some()
                && !reference_captured.params.contains(param)
                && proto_may_write_param_home(proto, **param, promotion_facts)
        })
        .copied()
        .collect::<BTreeSet<_>>();
    let stable_visible_params = proto
        .params
        .iter()
        .filter(|param| {
            promotion_facts.trusted_param_home_slot(**param).is_some()
                && !reference_captured.params.contains(param)
                && !overwritten_visible_params.contains(param)
        })
        .copied()
        .collect();
    let mut pass = DeadTempPass {
        live_reads: &live_reads,
        parameter_by_temp,
        physical_home_temps,
        debug_temps,
        facts: promotion_facts,
        stable_visible_params,
        overwritten_visible_params,
        physical_root_temps: BTreeSet::new(),
    };
    let mut changed = rewrite_proto(proto, &mut pass);
    let original_physical_root_count = proto.physical_root_temps.len();
    proto
        .physical_root_temps
        .extend(pass.physical_root_temps.iter().copied());
    changed |= proto.physical_root_temps.len() != original_physical_root_count;
    changed |= remove_dead_entry_nil_writes_from_root_prefix(
        &mut proto.body,
        &live_reads,
        &pass.debug_temps,
        promotion_facts,
    );
    changed
}

fn remove_dead_entry_nil_writes_from_root_prefix(
    block: &mut HirBlock,
    live_reads: &BTreeSet<TempId>,
    debug_temps: &BTreeSet<TempId>,
    facts: &ProtoPromotionFacts,
) -> bool {
    let mut changed = false;
    let mut in_single_pass_prefix = true;
    let mut captured_homes = BTreeSet::new();
    block.stmts.retain(|stmt| {
        if !in_single_pass_prefix {
            return true;
        }
        if !root_prefix_stmt_preserves_single_pass_continuation(stmt) {
            // 分析停用[SemanticBarrier:ControlFlow]：任意深度的 label/goto 可能让后缀重新进入已扫描区间。
            // 分析停用[LayerBoundary]：root terminal 后的不可达后缀属于前层 CFG/dead-code owner。
            in_single_pass_prefix = false;
            return true;
        }

        let removable = dead_pure_temp_assignment(stmt, live_reads).is_some_and(|temp| {
            let home = facts.home_slot(temp);
            facts.overwrites_entry_nil(temp)
                // 候选拒绝[PolicyBoundary]：debug temp 是源码 binding；即使入口旧值为 nil，删除定义也会抹掉项目选择保留的 source identity。
                && !debug_temps.contains(&temp)
                // 候选拒绝[ProofIncomplete]：entry-nil 只证明旧值非资源；RHS 若可能引用对象，删除物理写会缩短新对象作为 VM root 的存活期。
                && dead_write_value_is_gc_inert(stmt)
                // 候选拒绝[SemanticBarrier:Capture]：`local x; f=function() return x end; x=false` 中先建立的 closure 会观察同槽写入；删除后返回 nil。
                && home.is_some_and(|home| !captured_homes.contains(&home))
        });
        facts.collect_captured_home_slots_in_stmt(stmt, &mut captured_homes);
        changed |= removable;
        !removable
    });
    changed
}

fn root_prefix_stmt_preserves_single_pass_continuation(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_) => true,
        HirStmt::If(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Block(_) => !stmt_contains_nested_nonlocal_control(stmt),
        HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn dead_write_value_is_gc_inert(stmt: &HirStmt) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return false;
    };
    expr_result_is_gc_inert(value)
}

struct DeadTempPass<'a> {
    live_reads: &'a BTreeSet<TempId>,
    parameter_by_temp: BTreeMap<TempId, ParamId>,
    physical_home_temps: BTreeSet<TempId>,
    debug_temps: BTreeSet<TempId>,
    facts: &'a ProtoPromotionFacts,
    stable_visible_params: BTreeSet<ParamId>,
    overwritten_visible_params: BTreeSet<ParamId>,
    physical_root_temps: BTreeSet<TempId>,
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
            let HirStmt::Assign(assign) = stmt else {
                unreachable!("dead temp candidate must remain an assignment")
            };
            let value = &assign.values.fixed[0];
            if self.facts.copies_same_visible_home_value(temp, value) {
                // 候选接受[NoOpRootProof]：目标 raw home 与可见 Param/Local 的 trusted home 相同，删除只是去掉同一 cell 的自写回，不改变 root 集或别名含义。
                changed = true;
                return false;
            }
            if matches!(value, HirExpr::ParamRef(param) if self.stable_visible_params.contains(param))
            {
                // 候选接受[VisibleRootProof]：RHS 参数仍是 trusted visible root，且整个 proto 无同 physical-home 写入/ByReference capture，删除只会去掉冗余 alias root。
                changed = true;
                return false;
            }
            if let Some(param) = self.parameter_by_temp.get(&temp).copied() {
                // 双方可信 home 证明该 SSA temp 实际覆盖参数槽；改回参数赋值才能维持 regress_342 中可观察的 GC root 释放时点。
                assign.targets[0] = HirLValue::Param(param);
                changed = true;
                return true;
            }
            if self.physical_home_temps.contains(&temp) {
                if expr_may_alias_overwritten_param(value, &self.overwritten_visible_params) {
                    // 候选拒绝[SemanticBarrier:Lifetime]：RHS 参数会在当前 slot 生命周期
                    // 结束前被同 home 写覆盖；把该 temp 标成
                    // PhysicalRoot，防止 AST cleanup 再删除这个保活 alias。
                    self.physical_root_temps.insert(temp);
                }
                // 候选拒绝[ProofIncomplete]：root-prefix entry-nil/inert 子集已在专用证明中删除；其余 raw-home 写仍可能释放旧 root，或让 RHS 引用成为新 root，需双向 reaching resource-value 与可见 binding 映射。
                return true;
            }
            changed = true;
            false
        });
        changed
    }
}

fn expr_may_alias_overwritten_param(expr: &HirExpr, params: &BTreeSet<ParamId>) -> bool {
    match expr {
        HirExpr::ParamRef(param) => params.contains(param),
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_may_alias_overwritten_param(&logical.lhs, params)
                || expr_may_alias_overwritten_param(&logical.rhs, params)
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::VarArg
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => false,
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

fn proto_may_write_param_home(
    proto: &HirProto,
    param: ParamId,
    facts: &ProtoPromotionFacts,
) -> bool {
    let Some(home) = facts.trusted_param_home_slot(param) else {
        return true;
    };
    let mut collector = ParamHomeWriteCollector {
        facts,
        home,
        param,
        written: false,
    };
    visit::visit_stmts(&proto.body.stmts, &mut collector);
    collector.written
}

struct ParamHomeWriteCollector<'a> {
    facts: &'a ProtoPromotionFacts,
    home: HomeSlotKey,
    param: ParamId,
    written: bool,
}

impl HirVisitor for ParamHomeWriteCollector<'_> {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.written |= match lvalue {
            HirLValue::Param(param) => {
                *param == self.param
                    || self
                        .facts
                        .trusted_param_home_slot(*param)
                        .is_none_or(|home| home == self.home)
            }
            HirLValue::Local(local) => self
                .facts
                .trusted_local_home_slot(*local)
                .is_none_or(|home| home == self.home),
            HirLValue::Temp(temp) => self
                .facts
                .trusted_temp_home_slot(*temp)
                .is_none_or(|home| home == self.home),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => false,
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{HirGoto, HirIf, HirLabelId, HirReturn, HirValuePack, HirWhile};

    fn block(stmts: Vec<HirStmt>) -> HirBlock {
        HirBlock { stmts }
    }

    #[test]
    fn root_prefix_crosses_closed_structures_and_owned_loop_control() {
        let closed_if = HirStmt::If(Box::new(HirIf {
            cond: HirExpr::Boolean(true),
            then_block: block(Vec::new()),
            else_block: Some(block(Vec::new())),
        }));
        let closed_loop = HirStmt::While(Box::new(HirWhile {
            cond: HirExpr::Boolean(true),
            body: block(vec![HirStmt::Continue, HirStmt::Break]),
        }));

        assert!(root_prefix_stmt_preserves_single_pass_continuation(
            &closed_if
        ));
        assert!(root_prefix_stmt_preserves_single_pass_continuation(
            &closed_loop
        ));
    }

    #[test]
    fn root_prefix_stops_at_nested_nonlocal_control_and_terminal() {
        let nested_goto = HirStmt::If(Box::new(HirIf {
            cond: HirExpr::Boolean(true),
            then_block: block(vec![HirStmt::Goto(Box::new(HirGoto {
                target: HirLabelId(0),
            }))]),
            else_block: None,
        }));
        let terminal = HirStmt::Return(Box::new(HirReturn {
            values: HirValuePack::default(),
        }));

        assert!(!root_prefix_stmt_preserves_single_pass_continuation(
            &nested_goto
        ));
        assert!(!root_prefix_stmt_preserves_single_pass_continuation(
            &terminal
        ));
    }
}
