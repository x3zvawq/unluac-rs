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
//! RHS 的可删除性与 GC 惰性统一消费入口按目标方言构造的表达式安全上下文。
//!
//! 例子：根前缀里的机械 `t = false` 若 `t` 是非参数槽首个 fixed def，可删成空；
//! `t = p` 即使没有值读取也不能删，因为该物理槽可能让 `p` 指向的对象继续存活。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirBlock, HirExpr, HirLValue, HirProto, HirStmt, ParamId, TempId};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::mention::stmts_reference_captured_bindings;
use super::temp_touch::{collect_temp_reads_in_proto, stmt_contains_nested_nonlocal_control};
use super::visit::{self, HirVisitor};
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn remove_dead_temp_materializations_in_proto(
    proto: &mut HirProto,
    promotion_facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
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
        safety,
    };
    let mut changed = rewrite_proto(proto, &mut pass);
    changed |= remove_dead_entry_nil_writes_from_root_prefix(
        &mut proto.body,
        &live_reads,
        &pass.debug_temps,
        &proto.physical_root_temps,
        &pass.stable_visible_params,
        promotion_facts,
        safety,
    );
    changed |= preserve_copy_roots_in_proto(
        proto,
        &live_reads,
        &pass.debug_temps,
        promotion_facts,
        safety,
        &mut pass.physical_root_temps,
    );
    changed |= preserve_adjacent_dead_physical_overwrites(
        &mut proto.body,
        &live_reads,
        &pass.debug_temps,
        promotion_facts,
        safety,
        &mut pass.physical_root_temps,
    );
    let original_physical_root_count = proto.physical_root_temps.len();
    proto
        .physical_root_temps
        .extend(pass.physical_root_temps.iter().copied());
    changed |= proto.physical_root_temps.len() != original_physical_root_count;
    changed
}

fn preserve_copy_roots_in_proto(
    proto: &mut HirProto,
    live_reads: &BTreeSet<TempId>,
    debug_temps: &BTreeSet<TempId>,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    physical_root_temps: &mut BTreeSet<TempId>,
) -> bool {
    rewrite_proto(
        proto,
        &mut CopyRootPass {
            live_reads,
            debug_temps,
            facts,
            safety,
            physical_root_temps,
        },
    )
}

struct CopyRootPass<'a> {
    live_reads: &'a BTreeSet<TempId>,
    debug_temps: &'a BTreeSet<TempId>,
    facts: &'a ProtoPromotionFacts,
    safety: HirExprSafety,
    physical_root_temps: &'a mut BTreeSet<TempId>,
}

impl HirRewritePass for CopyRootPass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        preserve_copy_roots_in_block(
            block,
            self.live_reads,
            self.debug_temps,
            self.facts,
            self.safety,
            self.physical_root_temps,
        )
    }
}

enum CopyRootPlan {
    ScopeEnd { producer: TempId },
    NilOverwrite { producer: TempId, index: usize },
}

fn preserve_copy_roots_in_block(
    block: &mut HirBlock,
    live_reads: &BTreeSet<TempId>,
    debug_temps: &BTreeSet<TempId>,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    physical_root_temps: &mut BTreeSet<TempId>,
) -> bool {
    let mut captured_homes = BTreeSet::new();
    for stmt in &block.stmts {
        facts.collect_captured_home_slots_in_stmt(stmt, &mut captured_homes);
    }

    let mut plans = Vec::new();
    for (producer_index, stmt) in block.stmts.iter().enumerate() {
        let Some((producer, value)) = single_temp_assignment(stmt) else {
            continue;
        };
        if dead_pure_temp_assignment(stmt, live_reads, safety) != Some(producer) {
            continue;
        }
        if safety.result_is_gc_inert(value) {
            continue;
        }
        let scope_end = facts.is_scope_end_copy_root_temp(producer);
        let overwrite = facts.copy_root_overwrite(producer);
        if !scope_end && overwrite.is_none() {
            continue;
        }
        let home = facts
            .trusted_temp_home_slot(producer)
            .expect("validated copy-root fact must retain producer home");
        if captured_homes.contains(&home) {
            // 候选拒绝[SemanticBarrier:Capture]：同槽 capture 可观察独立 cell identity。
            continue;
        }

        if let Some(overwrite) = overwrite {
            let (overwrite_index, hir_overwrite) = block.stmts[producer_index + 1..]
                .iter()
                .enumerate()
                .find_map(|(offset, suffix)| {
                    let Some((temp, HirExpr::Nil)) = single_temp_assignment(suffix) else {
                        return None;
                    };
                    ((temp == overwrite || temp == producer)
                        && dead_pure_temp_assignment(suffix, live_reads, safety) == Some(temp))
                    .then_some((producer_index + 1 + offset, temp))
                })
                .expect("copy-root overwrite fact must retain its direct scalar nil assignment");
            if hir_overwrite == overwrite && debug_temps.contains(&overwrite) {
                // 候选拒绝[SemanticBarrier:DebugScope]：把仍独立存在的 debug overwrite
                // 改写为 producer 会抹掉它自己的源码 local identity。
                continue;
            }
            plans.push(CopyRootPlan::NilOverwrite {
                producer,
                index: overwrite_index,
            });
        } else {
            plans.push(CopyRootPlan::ScopeEnd { producer });
        }
    }

    let mut changed = false;
    for plan in plans {
        match plan {
            CopyRootPlan::ScopeEnd { producer } => {
                physical_root_temps.insert(producer);
            }
            CopyRootPlan::NilOverwrite { producer, index } => {
                let HirStmt::Assign(assign) = &mut block.stmts[index] else {
                    unreachable!("validated copy-root overwrite must remain an assignment")
                };
                changed |= assign.targets[0] != HirLValue::Temp(producer);
                assign.targets[0] = HirLValue::Temp(producer);
                physical_root_temps.insert(producer);
            }
        }
    }
    changed
}

fn preserve_adjacent_dead_physical_overwrites(
    block: &mut HirBlock,
    live_reads: &BTreeSet<TempId>,
    debug_temps: &BTreeSet<TempId>,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    physical_root_temps: &mut BTreeSet<TempId>,
) -> bool {
    let mut captured_homes = BTreeSet::new();
    for stmt in &block.stmts {
        facts.collect_captured_home_slots_in_stmt(stmt, &mut captured_homes);
    }

    let mut changed = false;
    for index in 1..block.stmts.len() {
        let Some(current) = dead_pure_temp_assignment(&block.stmts[index], live_reads, safety)
        else {
            continue;
        };
        let Some((previous, previous_value)) = single_temp_assignment(&block.stmts[index - 1])
        else {
            // 候选拒绝[ProofIncomplete]：非相邻 producer 需要区间 reaching-def、控制流与同槽写入证明。
            continue;
        };
        if safety.result_is_gc_inert(previous_value) {
            continue;
        }
        let Some(home) = facts.trusted_temp_home_slot(previous) else {
            // 候选拒绝[ProofIncomplete]：producer 缺可信 home 时无法证明两次物理写命中同一 root cell。
            continue;
        };
        if current == previous {
            continue;
        }
        if facts.trusted_temp_home_slot(current) != Some(home) {
            // 候选拒绝[SemanticBarrier:Lifetime]：异槽写没有共享物理 root cell，合并会错误延长 previous home 的生命周期。
            continue;
        }
        if live_reads.contains(&previous) {
            // 候选拒绝[SemanticBarrier:ValueFlow]：previous identity 仍被读取，合并覆盖会改变该读取的 reaching value。
            continue;
        }
        if debug_temps.contains(&current) || debug_temps.contains(&previous) {
            // 候选拒绝[SemanticBarrier:DebugScope]：任一写入带已保留的源码 local identity，合并会抹掉一段声明可见期。
            continue;
        }
        if captured_homes.contains(&home) {
            // 候选拒绝[SemanticBarrier:Capture]：同槽 capture 可观察每次写入。
            continue;
        }
        let HirStmt::Assign(assign) = &mut block.stmts[index] else {
            unreachable!("dead temp candidate must remain an assignment")
        };
        assign.targets[0] = HirLValue::Temp(previous);
        physical_root_temps.insert(previous);
        changed = true;
    }
    changed
}

fn single_temp_assignment(stmt: &HirStmt) -> Option<(TempId, &HirExpr)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(temp)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    assign.values.tail.is_none().then_some((*temp, value))
}

fn remove_dead_entry_nil_writes_from_root_prefix(
    block: &mut HirBlock,
    live_reads: &BTreeSet<TempId>,
    debug_temps: &BTreeSet<TempId>,
    physical_root_temps: &BTreeSet<TempId>,
    stable_visible_params: &BTreeSet<ParamId>,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    let mut changed = false;
    let mut in_single_pass_prefix = true;
    let mut captured_homes = BTreeSet::new();
    for stmt in &block.stmts {
        facts.collect_captured_home_slots_in_stmt(stmt, &mut captured_homes);
    }
    block.stmts.retain(|stmt| {
        if !in_single_pass_prefix {
            return true;
        }
        if !root_prefix_stmt_preserves_single_pass_continuation(stmt) {
            in_single_pass_prefix = false;
            return true;
        }

        let removable = dead_pure_temp_assignment(stmt, live_reads, safety).is_some_and(|temp| {
            let home = facts.home_slot(temp);
            facts.overwrites_entry_nil(temp)
                // 候选拒绝[SemanticBarrier:DebugScope]：debug temp 是已保留的源码 binding；删除定义会抹掉其声明可见期。
                && !debug_temps.contains(&temp)
                // 候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot temp 可能已由精确
                // overwrite handoff 复用；删除其 GC-inert 写会丢失原 root 终止点。
                && !physical_root_temps.contains(&temp)
                // 候选拒绝[ProofIncomplete]：entry-nil 只证明旧值非资源；除 GC 惰性值和全函数稳定参数外，RHS 仍可能需要目标槽作为新 root。
                && (dead_write_value_is_gc_inert(stmt, safety)
                    || dead_write_copies_stable_param(stmt, stable_visible_params))
                // 候选拒绝[SemanticBarrier:Capture]：候选前后任一 closure 若捕获同槽，删除写入都会让它观察 nil 而非新值。
                && home.is_some_and(|home| !captured_homes.contains(&home))
        });
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
        HirStmt::GlobalDecl(_) => {
            // 分析停用[ProofIncomplete]：全局声明的种子与后续赋值共享源码 identity；
            // 当前证明只覆盖 temp 写，不能让扫描越过该 AST-owned 声明边界。
            false
        }
        HirStmt::If(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Block(_) => !stmt_contains_nested_nonlocal_control(stmt),
        HirStmt::Return(_) => {
            // 分析停用[LayerBoundary]：Return 后缀的不可达性属于 CFG/dead-code owner。
            false
        }
        HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_) => {
            // 分析停用[SemanticBarrier:ControlFlow]：非局部跳转或可重入 label 会破坏
            // 根前缀“每条语句至多执行一次且只能顺序进入后缀”的证明。
            false
        }
    }
}

fn dead_write_value_is_gc_inert(stmt: &HirStmt, safety: HirExprSafety) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return false;
    };
    safety.result_is_gc_inert(value)
}

fn dead_write_copies_stable_param(
    stmt: &HirStmt,
    stable_visible_params: &BTreeSet<ParamId>,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    matches!(assign.values.fixed.as_slice(), [HirExpr::ParamRef(param)] if stable_visible_params.contains(param))
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
    safety: HirExprSafety,
}

impl HirRewritePass for DeadTempPass<'_> {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let mut changed = false;
        block.stmts.retain_mut(|stmt| {
            let Some(temp) = dead_pure_temp_assignment(stmt, self.live_reads, self.safety) else {
                return true;
            };
            // 候选拒绝[SemanticBarrier:DebugScope]：debug temp 是已保留的源码 binding；删除定义会抹掉其声明可见期。
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
            if let Some(param) = self.parameter_by_temp.get(&temp).copied() {
                // 双方可信 home 证明该 SSA temp 实际覆盖参数槽；改回参数赋值才能维持 regress_342 中可观察的 GC root 释放时点。
                assign.targets[0] = HirLValue::Param(param);
                changed = true;
                return true;
            }
            if self.physical_home_temps.contains(&temp) {
                if expr_may_alias_overwritten_param(value, &self.overwritten_visible_params) {
                    // 候选拒绝[SemanticBarrier:Lifetime]：RHS 参数会在当前 slot 生命周期
                    // 结束前被同 home 写覆盖。把该 temp 标成 PhysicalRoot，防止 AST
                    // cleanup 再删除这个保活 alias；direct copy 的精确区间由后置
                    // copy-root owner 统一处理。
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

fn dead_pure_temp_assignment(
    stmt: &HirStmt,
    live_reads: &BTreeSet<TempId>,
    safety: HirExprSafety,
) -> Option<TempId> {
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
    // 候选拒绝[SemanticBarrier:ValueFlow]：仍被读取的 temp 定义决定后续值；删除
    // `t = 1; return t` 会把读取变成未定义槽。
    if live_reads.contains(temp) {
        return None;
    }
    // 候选拒绝[SemanticBarrier:EvalCount]：不可丢弃 RHS 必须求值一次；调用、
    // table/global lookup 或分配即使结果未读也可能执行用户代码、抛错或产生对象身份。
    safety.is_discard_safe(value).then_some(*temp)
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
