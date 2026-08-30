//! 这个文件负责清理 simplify 出口上已经没有任何读取者的无副作用 temp 赋值。
//!
//! 结构层在 block 入口会先把一批 phi/temp 物化出来，后续 branch/loop/readability pass
//! 再把真正活着的那部分折进源码结构。对大函数来说，最后常会留下"只赋值一次、后面从未
//! 再读"的机械 temp 壳；它们继续留在 HIR 里不仅会制造残余 unresolved warning，
//! 还会直接挡住 AST lowering。
//!
//! 清理范围：目标 temp 全局无读者，且 RHS 不含潜在副作用（调用、metamethod 触发、
//! table 构造等）的赋值语句。它依赖 promotion 保存的物理 home 与 entry-nil provenance：
//! 无物理 home 的纯死写可直接删除；参数同槽写改回参数赋值；不经过循环或非局部跳转的
//! 结构化前缀中，`entry nil -> GC-inert value` 的写入也可删除；复制无 capture-home
//! 别名、无后写且后缀仍读取的可见 binding 同样不需要建立第二个 root。其余有 home 的
//! 写入不在这里猜 reaching value，因为它仍可能决定旧对象或新对象的 GC root 生命周期。
//! RHS 的可删除性与 GC 惰性统一消费入口按目标方言构造的表达式安全上下文。
//!
//! 例子：根前缀里的机械 `t = false` 若 `t` 是非参数槽首个 fixed def，可删成空；
//! `t = stable_local` 若目标覆盖 entry nil 可删；`t = p; p = nil` 则必须保留 `t` 的 root。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirProto, HirStmt, LocalId, ParamId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::mention::{
    ReferenceCapturedBindings, stmts_protected_locals, stmts_reference_captured_bindings,
};
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
    let reference_captured_homes =
        trusted_reference_capture_home_slots(&reference_captured, promotion_facts);
    let protected_locals = stmts_protected_locals(&proto.body.stmts);
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
    let params = proto
        .params
        .iter()
        .filter(|param| {
            promotion_facts
                .trusted_param_home_slot(**param)
                .is_some_and(|home| {
                    reference_captured_homes
                        .as_ref()
                        .is_some_and(|captured| !captured.contains(&home))
                })
                && !overwritten_visible_params.contains(param)
        })
        .copied()
        .collect();
    let locals = proto
        .locals
        .iter()
        .filter(|local| {
            promotion_facts
                .trusted_local_home_slot(**local)
                .is_some_and(|home| {
                    reference_captured_homes
                        .as_ref()
                        .is_some_and(|captured| !captured.contains(&home))
                })
                // TBC/loop binding 有独立资源或迭代生命周期，不能只按普通 root 证明。
                && !protected_locals.contains(local)
                && !proto_may_write_visible_home(
                    proto,
                    VisibleBinding::Local(**local),
                    promotion_facts,
                )
        })
        .copied()
        .collect();
    let stable_visible_bindings = StableVisibleBindings {
        params,
        locals,
        reference_captured_homes,
    };
    let mut pass = DeadTempPass {
        live_reads: &live_reads,
        parameter_by_temp,
        physical_home_temps,
        debug_temps,
        facts: promotion_facts,
        stable_visible_bindings,
        overwritten_visible_params,
        physical_root_temps: BTreeSet::new(),
        safety,
    };
    let mut changed = rewrite_proto(proto, &mut pass);
    changed |= remove_dead_entry_nil_writes_from_acyclic_prefixes(
        &mut proto.body,
        &live_reads,
        &pass.debug_temps,
        &proto.physical_root_temps,
        &pass.stable_visible_bindings,
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

fn remove_dead_entry_nil_writes_from_acyclic_prefixes(
    block: &mut HirBlock,
    live_reads: &BTreeSet<TempId>,
    debug_temps: &BTreeSet<TempId>,
    physical_root_temps: &BTreeSet<TempId>,
    stable_visible_bindings: &StableVisibleBindings,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    let mut changed = remove_dead_entry_nil_writes_from_root_prefix(
        block,
        live_reads,
        debug_temps,
        physical_root_temps,
        stable_visible_bindings,
        facts,
        safety,
    );

    for stmt in &mut block.stmts {
        if stmt_contains_nested_nonlocal_control(stmt) {
            continue;
        }
        match stmt {
            HirStmt::If(if_stmt) => {
                changed |= remove_dead_entry_nil_writes_from_acyclic_prefixes(
                    &mut if_stmt.then_block,
                    live_reads,
                    debug_temps,
                    physical_root_temps,
                    stable_visible_bindings,
                    facts,
                    safety,
                );
                if let Some(else_block) = &mut if_stmt.else_block {
                    changed |= remove_dead_entry_nil_writes_from_acyclic_prefixes(
                        else_block,
                        live_reads,
                        debug_temps,
                        physical_root_temps,
                        stable_visible_bindings,
                        facts,
                        safety,
                    );
                }
            }
            HirStmt::Block(nested) => {
                changed |= remove_dead_entry_nil_writes_from_acyclic_prefixes(
                    nested,
                    live_reads,
                    debug_temps,
                    physical_root_temps,
                    stable_visible_bindings,
                    facts,
                    safety,
                );
            }
            HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_) => {}
        }
    }
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
            continue;
        };
        if safety.result_is_gc_inert(previous_value) {
            continue;
        }
        let Some(home) = facts.home_slot(previous) else {
            // 候选拒绝[LayerBoundary]：没有 raw target home 的 synthetic temp 不代表 VM
            // 物理写；它的死定义由普通 dead-temp 路径消费，不能充当 root overwrite owner。
            continue;
        };
        if current == previous {
            continue;
        }
        if facts.home_slot(current) != Some(home) {
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
    stable_visible_bindings: &StableVisibleBindings,
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    let mut changed = false;
    let mut in_single_pass_prefix = true;
    let adjacent_visible_handoffs = block
        .stmts
        .windows(2)
        .filter_map(|pair| adjacent_same_value_visible_handoff(pair, facts))
        .collect::<BTreeSet<_>>();
    let mut last_local_read = BTreeMap::new();
    for (index, stmt) in block.stmts.iter().enumerate() {
        let mut collector = LastLocalReadCollector {
            index,
            reads: &mut last_local_read,
        };
        visit::visit_stmts(std::slice::from_ref(stmt), &mut collector);
        if !root_prefix_stmt_preserves_single_pass_continuation(stmt) {
            break;
        }
    }
    let mut index = 0;
    block.stmts.retain(|stmt| {
        let current_index = index;
        index += 1;
        if !in_single_pass_prefix {
            return true;
        }
        if !root_prefix_stmt_preserves_single_pass_continuation(stmt) {
            in_single_pass_prefix = false;
            return true;
        }

        let removable = dead_pure_temp_assignment(stmt, live_reads, safety).is_some_and(|temp| {
            let home = facts.home_slot(temp);
            let has_adjacent_visible_handoff = adjacent_visible_handoffs.contains(&temp);
            let overwrites_entry_nil_with_nil =
                facts.overwrites_entry_nil(temp) && dead_write_value_is_nil(stmt);
            (facts.overwrites_entry_nil(temp) || has_adjacent_visible_handoff)
                // 候选拒绝[SemanticBarrier:DebugScope]：debug temp 是已保留的源码 binding；删除定义会抹掉其声明可见期。
                && !debug_temps.contains(&temp)
                // 候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot temp 可能已由精确
                // overwrite handoff 复用；删除其 GC-inert 写会丢失原 root 终止点。
                && (!physical_root_temps.contains(&temp) || has_adjacent_visible_handoff)
                // 候选拒绝[SemanticBarrier:Lifetime]：entry-nil 只证明旧值非资源；新 RHS
                // 若可持有 collectable value，删除目标槽写会丢失它的独立 GC root。
                // regress_431 的 overwritten/only_root/captured 三组分别覆盖来源后写、唯一
                // root 与 capture cell；只有下列不建立新 root 的证明分支可以删除。
                && (dead_write_value_is_gc_inert(stmt, safety)
                    // 候选接受[NoOpRootProof]：下一句把同一个 visible value 交给同一
                    // trusted home；两次写之间无求值、GC 或 capture 观察点，首写不建立
                    // 额外 root epoch。regress_36 覆盖该分支 handoff。
                    || has_adjacent_visible_handoff
                    || dead_write_copies_stable_binding(
                        stmt,
                        stable_visible_bindings,
                        current_index,
                        &last_local_read,
                    ))
                // 候选拒绝[SemanticBarrier:Capture]：候选前后任一 closure 若捕获同槽，删除写入都会让它观察 nil 而非新值。
                && stable_visible_bindings
                    .reference_captured_homes
                    .as_ref()
                    .is_some_and(|captured| {
                        has_adjacent_visible_handoff
                            // 候选接受[NoOpRootProof]：入口旧值与新值均为 nil；稍后创建
                            // 的同 home capture 观察不到这次无值、无 root 的写回。
                            || overwrites_entry_nil_with_nil
                            || home.is_some_and(|home| !captured.contains(&home))
                    })
        });
        changed |= removable;
        !removable
    });
    changed
}

fn adjacent_same_value_visible_handoff(
    pair: &[HirStmt],
    facts: &ProtoPromotionFacts,
) -> Option<TempId> {
    let [first, HirStmt::Assign(second)] = pair else {
        return None;
    };
    let (temp, first_value) = single_temp_assignment(first)?;
    let [second_value] = second.values.fixed.as_slice() else {
        return None;
    };
    if !matches!(first_value, HirExpr::ParamRef(_) | HirExpr::LocalRef(_))
        || second.values.tail.is_some()
        || second_value != first_value
    {
        return None;
    }
    let [target] = second.targets.as_slice() else {
        return None;
    };
    let target_home = match target {
        HirLValue::Param(param) => facts.trusted_param_home_slot(*param),
        HirLValue::Local(local) => facts.trusted_local_home_slot(*local),
        HirLValue::Temp(_)
        | HirLValue::Upvalue(_)
        | HirLValue::Global(_)
        | HirLValue::TableAccess(_) => None,
    };
    (facts.home_slot(temp).is_some() && facts.home_slot(temp) == target_home).then_some(temp)
}

fn root_prefix_stmt_preserves_single_pass_continuation(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::LocalDecl(_)
        | HirStmt::GlobalDecl(_)
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

fn dead_write_value_is_nil(stmt: &HirStmt) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    matches!(assign.values.fixed.as_slice(), [HirExpr::Nil])
}

fn dead_write_copies_stable_binding(
    stmt: &HirStmt,
    stable_visible_bindings: &StableVisibleBindings,
    current_index: usize,
    last_local_read: &BTreeMap<LocalId, usize>,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    match assign.values.fixed.as_slice() {
        [HirExpr::ParamRef(param)] => stable_visible_bindings.params.contains(param),
        [HirExpr::LocalRef(local)] => {
            stable_visible_bindings.locals.contains(local)
                && last_local_read
                    .get(local)
                    .is_some_and(|last| *last > current_index)
        }
        _ => false,
    }
}

struct StableVisibleBindings {
    params: BTreeSet<ParamId>,
    locals: BTreeSet<LocalId>,
    reference_captured_homes: Option<BTreeSet<HomeSlotKey>>,
}

struct LastLocalReadCollector<'a> {
    index: usize,
    reads: &'a mut BTreeMap<LocalId, usize>,
}

impl HirVisitor for LastLocalReadCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::LocalRef(local) = expr {
            self.reads.insert(*local, self.index);
        }
    }
}

struct DeadTempPass<'a> {
    live_reads: &'a BTreeSet<TempId>,
    parameter_by_temp: BTreeMap<TempId, ParamId>,
    physical_home_temps: BTreeSet<TempId>,
    debug_temps: BTreeSet<TempId>,
    facts: &'a ProtoPromotionFacts,
    stable_visible_bindings: StableVisibleBindings,
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
                // 候选拒绝[SemanticBarrier:Lifetime]：其余 raw-home 写不能删除；
                // regress_398 证明 inert/稳定副本写会在原点释放旧 root，regress_377
                // 证明不同 home 的副本会在源参数覆盖后成为唯一新 root。
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
    proto_may_write_visible_home(proto, VisibleBinding::Param(param), facts)
}

#[derive(Clone, Copy)]
enum VisibleBinding {
    Param(ParamId),
    Local(LocalId),
}

fn trusted_reference_capture_home_slots(
    captured: &ReferenceCapturedBindings,
    facts: &ProtoPromotionFacts,
) -> Option<BTreeSet<HomeSlotKey>> {
    let mut homes = BTreeSet::new();
    for param in &captured.params {
        homes.insert(facts.trusted_param_home_slot(*param)?);
    }
    for local in &captured.locals {
        if facts.local_has_no_physical_home(*local) {
            continue;
        }
        homes.insert(facts.trusted_local_home_slot(*local)?);
    }
    for temp in &captured.temps {
        homes.insert(facts.trusted_temp_home_slot(*temp)?);
    }
    Some(homes)
}

fn proto_may_write_visible_home(
    proto: &HirProto,
    binding: VisibleBinding,
    facts: &ProtoPromotionFacts,
) -> bool {
    let home = match binding {
        VisibleBinding::Param(param) => facts.trusted_param_home_slot(param),
        VisibleBinding::Local(local) => facts.trusted_local_home_slot(local),
    };
    let Some(home) = home else {
        return true;
    };
    let mut collector = VisibleHomeWriteCollector {
        facts,
        home,
        binding,
        written: false,
    };
    visit::visit_stmts(&proto.body.stmts, &mut collector);
    collector.written
}

struct VisibleHomeWriteCollector<'a> {
    facts: &'a ProtoPromotionFacts,
    home: HomeSlotKey,
    binding: VisibleBinding,
    written: bool,
}

impl HirVisitor for VisibleHomeWriteCollector<'_> {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.written |= match lvalue {
            HirLValue::Param(param) => {
                matches!(self.binding, VisibleBinding::Param(binding) if binding == *param)
                    || self
                        .facts
                        .trusted_param_home_slot(*param)
                        .is_none_or(|home| home == self.home)
            }
            HirLValue::Local(local) => {
                matches!(self.binding, VisibleBinding::Local(binding) if binding == *local)
                    || self
                        .facts
                        .trusted_local_home_slot(*local)
                        .is_none_or(|home| home == self.home)
            }
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
    use crate::decompile::DecompileDialect;
    use crate::hir::common::{
        HirAssign, HirGlobalDecl, HirGoto, HirIf, HirLabelId, HirReturn, HirValuePack, HirWhile,
    };

    fn block(stmts: Vec<HirStmt>) -> HirBlock {
        HirBlock { stmts }
    }

    #[test]
    fn reference_capture_homes_cover_all_physical_binding_kinds() {
        let home = HomeSlotKey::new(0, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_local_home_slot(LocalId(0), home);
        facts.record_local_home_slot(LocalId(1), home);
        facts.record_temp_home_slot_for_test(TempId(0), home);
        let mut captured = ReferenceCapturedBindings::default();
        captured.params.insert(ParamId(0));
        captured.locals.insert(LocalId(0));
        captured.temps.insert(TempId(0));

        let captured_homes = trusted_reference_capture_home_slots(&captured, &facts)
            .expect("all captured bindings have trusted homes");
        assert_eq!(captured_homes, BTreeSet::from([home]));
        assert!(
            captured_homes.contains(
                &facts
                    .trusted_local_home_slot(LocalId(1))
                    .expect("candidate has a trusted home")
            ),
            "a different LocalId sharing the captured home must be rejected"
        );
    }

    #[test]
    fn unknown_capture_home_blocks_the_complete_capture_proof() {
        let mut captured = ReferenceCapturedBindings::default();
        captured.temps.insert(TempId(0));

        assert_eq!(
            trusted_reference_capture_home_slots(&captured, &ProtoPromotionFacts::default()),
            None
        );
    }

    #[test]
    fn home_free_captured_local_cannot_alias_a_physical_home() {
        let mut facts = ProtoPromotionFacts::default();
        facts.record_home_free_local(LocalId(0));
        let mut captured = ReferenceCapturedBindings::default();
        captured.locals.insert(LocalId(0));

        assert_eq!(
            trusted_reference_capture_home_slots(&captured, &facts),
            Some(BTreeSet::new())
        );
    }

    #[test]
    fn adjacent_root_overwrite_uses_raw_target_home_after_value_provenance_invalidation() {
        let previous = TempId(0);
        let current = TempId(1);
        let home = HomeSlotKey::new(0, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(previous, home);
        facts.record_temp_home_slot_for_test(current, home);
        facts.invalidate_temp_home(previous);
        let assign = |temp, value| {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(temp)],
                values: HirValuePack::fixed(vec![value]),
            }))
        };
        let mut block = block(vec![
            assign(previous, HirExpr::ParamRef(ParamId(0))),
            assign(current, HirExpr::Nil),
        ]);
        let mut physical_roots = BTreeSet::new();

        assert!(preserve_adjacent_dead_physical_overwrites(
            &mut block,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &facts,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
            &mut physical_roots,
        ));
        let HirStmt::Assign(overwrite) = &block.stmts[1] else {
            panic!("overwrite must remain an assignment");
        };
        assert_eq!(overwrite.targets, vec![HirLValue::Temp(previous)]);
        assert_eq!(physical_roots, BTreeSet::from([previous]));
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
    fn root_prefix_crosses_global_declaration_without_rewriting_its_identity() {
        let global_decl = HirStmt::GlobalDecl(Box::new(HirGlobalDecl {
            names: vec!["value".to_owned()],
            values: HirValuePack::fixed(vec![HirExpr::Integer(1)]),
        }));

        // Prefix scanning only decides whether a later dead temp write is reached once. The
        // declaration remains in place; success continues linearly and failure never reaches the
        // candidate in either program.
        assert!(root_prefix_stmt_preserves_single_pass_continuation(
            &global_decl
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
