//! carried-local 收敛后的冗余赋值裁剪。
//!
//! handoff owner 在主模块里完成语义判断；这个模块只删除已经由 owner 或局部控制流证明
//! 无效的复制。除了单目标 `x = x`、空 assign、直接 binding 的整句 `x, y = x, y`，
//! 还收回分支 arm 中“支配初值之后没有任何 binding 写入”的 `target = temp` 快照：
//! `local target = temp; if cond then target = temp end` 变成只保留初值声明。
//! 分支规则在每个 arm 独立维护已证明的 `(local -> temp)` 状态，并让循环入口状态收敛到
//! 首轮入口与所有自然/continue 回边的交集；它不会跨未知 goto 或 reference capture 猜测。
//! 多目标赋值仍不拆分，因为其中的单个 `x = x` 可能承载其它 RHS 的并行快照。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirCallExpr, HirExpr, HirLValue, HirProto, HirStmt, HirUnaryOpKind,
    LocalId, TempId,
};

use super::super::mention::stmts_reference_captured_bindings;
use super::super::visit::{HirVisitor, visit_block, visit_expr, visit_stmts};
use super::super::walk::{HirRewritePass, rewrite_stmts};
use super::binding::{
    CarryBinding, carry_binding_from_expr, carry_binding_from_lvalue, single_binding_copy,
};

pub(super) struct RedundantSelfAssignPrunePass {
    prunable_bindings: BTreeSet<CarryBinding>,
}

impl RedundantSelfAssignPrunePass {
    pub(super) fn for_bindings(bindings: impl IntoIterator<Item = CarryBinding>) -> Self {
        Self {
            prunable_bindings: collect_prunable_bindings(bindings),
        }
    }
}

impl HirRewritePass for RedundantSelfAssignPrunePass {
    fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
        let original_len = block.stmts.len();
        block.stmts.retain(|stmt| !is_empty_assign_stmt(stmt));
        block.stmts.len() != original_len
    }

    fn rewrite_stmt(&mut self, stmt: &mut HirStmt) -> bool {
        prune_redundant_self_assign_stmt(stmt, &self.prunable_bindings)
    }
}

pub(super) fn prune_empty_assign_stmts(block: &mut HirBlock) -> bool {
    let original_len = block.stmts.len();
    block.stmts.retain(|stmt| !is_empty_assign_stmt(stmt));
    block.stmts.len() != original_len
}

pub(super) fn prune_redundant_copy_stmts(block: &mut HirBlock) -> bool {
    let original = std::mem::take(&mut block.stmts);
    let mut rewritten = Vec::<HirStmt>::with_capacity(original.len());
    let mut changed = false;

    for stmt in original {
        let copy = single_binding_copy(&stmt);
        let redundant_parallel = matches!(
            &stmt,
            HirStmt::Assign(assign) if redundant_parallel_self_copy(assign)
        );
        if copy.is_some_and(|(target, source)| target == source)
            || redundant_parallel
            || rewritten
                .last()
                .and_then(single_binding_copy)
                .zip(copy)
                .is_some_and(|((first_target, first_source), (target, source))| {
                    first_target != first_source && first_target == source && first_source == target
                })
        {
            changed = true;
        } else {
            rewritten.push(stmt);
        }
    }

    block.stmts = rewritten;
    changed
}

pub(super) fn prune_redundant_branch_state_copies(proto: &mut HirProto) -> bool {
    let reference_captured = stmts_reference_captured_bindings(&proto.body.stmts);
    let debug_locals = proto
        .locals
        .iter()
        .copied()
        .zip(&proto.local_debug_hints)
        .filter_map(|(local, hint)| hint.is_some().then_some(local))
        .collect();
    let facts = BranchStateCopyFacts {
        reference_captured_locals: &reference_captured.locals,
        reference_captured_temps: &reference_captured.temps,
        debug_locals: &debug_locals,
        debug_temps: &proto.temp_debug_locals,
    };
    let (changed, _) = rewrite_branch_state_block(&mut proto.body, &facts, BTreeMap::new(), false);
    changed
}

struct BranchStateCopyFacts<'a> {
    reference_captured_locals: &'a BTreeSet<LocalId>,
    reference_captured_temps: &'a BTreeSet<TempId>,
    debug_locals: &'a BTreeSet<LocalId>,
    debug_temps: &'a [Option<String>],
}

fn rewrite_branch_state_block(
    block: &mut HirBlock,
    facts: &BranchStateCopyFacts<'_>,
    mut known: BTreeMap<LocalId, TempId>,
    allow_prune: bool,
) -> (bool, BTreeMap<LocalId, TempId>) {
    let mut changed = false;
    let mut index = 0;
    while index < block.stmts.len() {
        match &mut block.stmts[index] {
            HirStmt::If(if_stmt) => {
                invalidate_capture_writes_from_expr(&mut known, &if_stmt.cond, facts);
                let incoming = known.clone();
                let (then_changed, then_known) = rewrite_branch_state_block(
                    &mut if_stmt.then_block,
                    facts,
                    incoming.clone(),
                    true,
                );
                let (else_changed, else_known) = if let Some(else_block) = &mut if_stmt.else_block {
                    rewrite_branch_state_block(else_block, facts, incoming, true)
                } else {
                    (false, incoming)
                };
                changed |= then_changed || else_changed;
                known = intersect_known_states(then_known, else_known);
            }
            HirStmt::Block(nested) => {
                let declared = declared_locals(nested);
                let (nested_changed, nested_known) =
                    rewrite_branch_state_block(nested, facts, known.clone(), allow_prune);
                changed |= nested_changed;
                known = nested_known;
                for local in declared {
                    known.remove(&local);
                }
            }
            HirStmt::While(while_stmt) => {
                invalidate_capture_writes_from_expr(&mut known, &while_stmt.cond, facts);
                let loop_entry = stable_loop_entry(
                    &while_stmt.body,
                    &known,
                    facts,
                    expr_may_execute_user_code(&while_stmt.cond),
                );
                let (body_changed, _) =
                    rewrite_branch_state_block(&mut while_stmt.body, facts, loop_entry, true);
                changed |= body_changed;
                invalidate_written_bindings(&mut known, &while_stmt.body);
                invalidate_capture_writes_from_block(&mut known, &while_stmt.body, facts);
                invalidate_capture_writes_from_expr(&mut known, &while_stmt.cond, facts);
            }
            HirStmt::Repeat(repeat_stmt) => {
                let loop_entry = stable_loop_entry(
                    &repeat_stmt.body,
                    &known,
                    facts,
                    expr_may_execute_user_code(&repeat_stmt.cond),
                );
                let (body_changed, _) =
                    rewrite_branch_state_block(&mut repeat_stmt.body, facts, loop_entry, true);
                changed |= body_changed;
                invalidate_written_bindings(&mut known, &repeat_stmt.body);
                invalidate_capture_writes_from_block(&mut known, &repeat_stmt.body, facts);
                invalidate_capture_writes_from_expr(&mut known, &repeat_stmt.cond, facts);
            }
            HirStmt::NumericFor(for_stmt) => {
                for expr in [&for_stmt.start, &for_stmt.limit, &for_stmt.step] {
                    invalidate_capture_writes_from_expr(&mut known, expr, facts);
                }
                let mut initial_entry = known.clone();
                initial_entry.remove(&for_stmt.binding);
                let loop_entry = stable_loop_entry(&for_stmt.body, &initial_entry, facts, false);
                let (body_changed, _) =
                    rewrite_branch_state_block(&mut for_stmt.body, facts, loop_entry, true);
                changed |= body_changed;
                invalidate_written_bindings(&mut known, &for_stmt.body);
                invalidate_capture_writes_from_block(&mut known, &for_stmt.body, facts);
                known.remove(&for_stmt.binding);
            }
            HirStmt::GenericFor(for_stmt) => {
                invalidate_reference_captured_state(&mut known, facts);
                let mut initial_entry = known.clone();
                for binding in &for_stmt.bindings {
                    initial_entry.remove(binding);
                }
                let loop_entry = stable_loop_entry(&for_stmt.body, &initial_entry, facts, true);
                let (body_changed, _) =
                    rewrite_branch_state_block(&mut for_stmt.body, facts, loop_entry, true);
                changed |= body_changed;
                invalidate_written_bindings(&mut known, &for_stmt.body);
                invalidate_reference_captured_state(&mut known, facts);
                for binding in &for_stmt.bindings {
                    known.remove(binding);
                }
            }
            stmt => {
                if allow_prune
                    && direct_local_temp_copy(stmt).is_some_and(|(local, temp)| {
                        known.get(&local) == Some(&temp) && facts.can_remove(local, temp)
                    })
                {
                    block.stmts.remove(index);
                    changed = true;
                    continue;
                }
                update_known_state(stmt, &mut known, facts);
                if matches!(
                    stmt,
                    HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_)
                ) {
                    known.clear();
                }
            }
        }
        index += 1;
    }
    (changed, known)
}

impl BranchStateCopyFacts<'_> {
    fn can_remove(&self, local: LocalId, temp: TempId) -> bool {
        // 候选拒绝[PolicyBoundary]：retain-debug 模式保留源码 local/temp 的显式写入位置与值 epoch，不把它压成支配声明（regress_336 retain-debug）。
        !self.debug_locals.contains(&local)
            && self
                .debug_temps
                .get(temp.index())
                .is_none_or(Option::is_none)
    }
}

fn direct_local_temp_copy(stmt: &HirStmt) -> Option<(LocalId, TempId)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([HirLValue::Local(local)], [HirExpr::TempRef(temp)], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    Some((*local, *temp))
}

fn direct_local_temp_decl(stmt: &HirStmt) -> Option<(LocalId, TempId)> {
    let HirStmt::LocalDecl(decl) = stmt else {
        return None;
    };
    let ([local], [HirExpr::TempRef(temp)], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    Some((*local, *temp))
}

fn update_known_state(
    stmt: &HirStmt,
    known: &mut BTreeMap<LocalId, TempId>,
    facts: &BranchStateCopyFacts<'_>,
) {
    invalidate_capture_writes_from_stmt(known, stmt, facts);
    if let Some((local, temp)) =
        direct_local_temp_copy(stmt).or_else(|| direct_local_temp_decl(stmt))
    {
        known.insert(local, temp);
        return;
    }
    let mut writes = BindingWriteCollector::default();
    visit_stmts(std::slice::from_ref(stmt), &mut writes);
    invalidate_known_state(known, &writes);
}

/// 循环体里的删除必须在首轮入口和每一条实际回边上都成立。这里对有限的
/// `(local -> temp)` must-state 做单调递减迭代；goto 会把回边降到 unknown，nested loop
/// 则只按其完整写集失效当前关系，不把内层 continue 错认成外层回边。
fn stable_loop_entry(
    body: &HirBlock,
    initial: &BTreeMap<LocalId, TempId>,
    facts: &BranchStateCopyFacts<'_>,
    backedge_may_execute_user_code: bool,
) -> BTreeMap<LocalId, TempId> {
    let mut entry = initial.clone();
    loop {
        let mut flow = analyze_loop_flow(body, entry.clone(), facts);
        if backedge_may_execute_user_code {
            invalidate_optional_reference_captured_state(&mut flow.fallthrough, facts);
            invalidate_optional_reference_captured_state(&mut flow.backedges, facts);
        }
        let Some(backedge) = merge_known_paths(flow.fallthrough, flow.backedges) else {
            return entry;
        };
        let next = intersect_known_states(initial.clone(), backedge);
        if next == entry {
            return entry;
        }
        entry = next;
    }
}

struct LoopFlow {
    fallthrough: Option<BTreeMap<LocalId, TempId>>,
    backedges: Option<BTreeMap<LocalId, TempId>>,
}

fn analyze_loop_flow(
    block: &HirBlock,
    initial: BTreeMap<LocalId, TempId>,
    facts: &BranchStateCopyFacts<'_>,
) -> LoopFlow {
    let mut flow = LoopFlow {
        fallthrough: Some(initial),
        backedges: None,
    };
    for stmt in &block.stmts {
        let Some(mut known) = flow.fallthrough.take() else {
            if matches!(stmt, HirStmt::Label(_)) {
                // 未解析 goto 可能从任意前驱进入 label；空集表示没有可复用的 must-state。
                flow.fallthrough = Some(BTreeMap::new());
            }
            continue;
        };
        match stmt {
            HirStmt::If(if_stmt) => {
                invalidate_capture_writes_from_expr(&mut known, &if_stmt.cond, facts);
                let then_flow = analyze_loop_flow(&if_stmt.then_block, known.clone(), facts);
                let else_flow = if let Some(else_block) = &if_stmt.else_block {
                    analyze_loop_flow(else_block, known, facts)
                } else {
                    LoopFlow {
                        fallthrough: Some(known),
                        backedges: None,
                    }
                };
                flow.fallthrough = merge_known_paths(then_flow.fallthrough, else_flow.fallthrough);
                flow.backedges = merge_known_paths(
                    flow.backedges,
                    merge_known_paths(then_flow.backedges, else_flow.backedges),
                );
            }
            HirStmt::Block(nested) => {
                let declared = declared_locals(nested);
                let mut nested_flow = analyze_loop_flow(nested, known, facts);
                remove_known_locals(&mut nested_flow.fallthrough, &declared);
                remove_known_locals(&mut nested_flow.backedges, &declared);
                flow.fallthrough = nested_flow.fallthrough;
                flow.backedges = merge_known_paths(flow.backedges, nested_flow.backedges);
            }
            HirStmt::While(while_stmt) => {
                invalidate_capture_writes_from_expr(&mut known, &while_stmt.cond, facts);
                invalidate_capture_writes_from_block(&mut known, &while_stmt.body, facts);
                invalidate_written_bindings(&mut known, &while_stmt.body);
                flow.fallthrough = Some(known);
            }
            HirStmt::Repeat(repeat_stmt) => {
                invalidate_capture_writes_from_block(&mut known, &repeat_stmt.body, facts);
                invalidate_capture_writes_from_expr(&mut known, &repeat_stmt.cond, facts);
                invalidate_written_bindings(&mut known, &repeat_stmt.body);
                flow.fallthrough = Some(known);
            }
            HirStmt::NumericFor(for_stmt) => {
                for expr in [&for_stmt.start, &for_stmt.limit, &for_stmt.step] {
                    invalidate_capture_writes_from_expr(&mut known, expr, facts);
                }
                invalidate_capture_writes_from_block(&mut known, &for_stmt.body, facts);
                invalidate_written_bindings(&mut known, &for_stmt.body);
                known.remove(&for_stmt.binding);
                flow.fallthrough = Some(known);
            }
            HirStmt::GenericFor(for_stmt) => {
                invalidate_reference_captured_state(&mut known, facts);
                invalidate_written_bindings(&mut known, &for_stmt.body);
                for binding in &for_stmt.bindings {
                    known.remove(binding);
                }
                flow.fallthrough = Some(known);
            }
            HirStmt::Continue => {
                flow.backedges = merge_known_paths(flow.backedges, Some(known));
            }
            HirStmt::Break | HirStmt::Return(_) => {}
            HirStmt::Goto(_) => {
                // 非结构跳转不携带当前树遍历的 must-state；清空关系后，label 后的复制会
                // 重新建立自己的状态，不会沿错误的词法前驱继承证明。
                flow.backedges = Some(BTreeMap::new());
            }
            HirStmt::Label(_) => {
                known.clear();
                flow.fallthrough = Some(known);
            }
            stmt => {
                update_known_state(stmt, &mut known, facts);
                flow.fallthrough = Some(known);
            }
        }
    }
    flow
}

fn merge_known_paths(
    left: Option<BTreeMap<LocalId, TempId>>,
    right: Option<BTreeMap<LocalId, TempId>>,
) -> Option<BTreeMap<LocalId, TempId>> {
    match (left, right) {
        (Some(left), Some(right)) => Some(intersect_known_states(left, right)),
        (Some(known), None) | (None, Some(known)) => Some(known),
        (None, None) => None,
    }
}

fn remove_known_locals(known: &mut Option<BTreeMap<LocalId, TempId>>, locals: &BTreeSet<LocalId>) {
    if let Some(known) = known {
        for local in locals {
            known.remove(local);
        }
    }
}

fn invalidate_known_state(known: &mut BTreeMap<LocalId, TempId>, writes: &BindingWriteCollector) {
    for local in &writes.locals {
        known.remove(local);
    }
    known.retain(|_, temp| !writes.temps.contains(temp));
}

fn invalidate_capture_writes_from_stmt(
    known: &mut BTreeMap<LocalId, TempId>,
    stmt: &HirStmt,
    facts: &BranchStateCopyFacts<'_>,
) {
    let mut effects = UserCodeEffectCollector::default();
    visit_stmts(std::slice::from_ref(stmt), &mut effects);
    if effects.found {
        invalidate_reference_captured_state(known, facts);
    }
}

fn invalidate_capture_writes_from_block(
    known: &mut BTreeMap<LocalId, TempId>,
    block: &HirBlock,
    facts: &BranchStateCopyFacts<'_>,
) {
    let mut effects = UserCodeEffectCollector::default();
    visit_block(block, &mut effects);
    if effects.found {
        invalidate_reference_captured_state(known, facts);
    }
}

fn invalidate_capture_writes_from_expr(
    known: &mut BTreeMap<LocalId, TempId>,
    expr: &HirExpr,
    facts: &BranchStateCopyFacts<'_>,
) {
    if expr_may_execute_user_code(expr) {
        invalidate_reference_captured_state(known, facts);
    }
}

fn expr_may_execute_user_code(expr: &HirExpr) -> bool {
    let mut effects = UserCodeEffectCollector::default();
    visit_expr(expr, &mut effects);
    effects.found
}

fn invalidate_reference_captured_state(
    known: &mut BTreeMap<LocalId, TempId>,
    facts: &BranchStateCopyFacts<'_>,
) {
    known.retain(|local, temp| {
        !facts.reference_captured_locals.contains(local)
            && !facts.reference_captured_temps.contains(temp)
    });
}

fn invalidate_optional_reference_captured_state(
    known: &mut Option<BTreeMap<LocalId, TempId>>,
    facts: &BranchStateCopyFacts<'_>,
) {
    if let Some(known) = known {
        invalidate_reference_captured_state(known, facts);
    }
}

fn invalidate_written_bindings(known: &mut BTreeMap<LocalId, TempId>, body: &HirBlock) {
    let mut writes = BindingWriteCollector::default();
    visit_stmts(&body.stmts, &mut writes);
    invalidate_known_state(known, &writes);
}

fn intersect_known_states(
    mut left: BTreeMap<LocalId, TempId>,
    right: BTreeMap<LocalId, TempId>,
) -> BTreeMap<LocalId, TempId> {
    left.retain(|local, temp| right.get(local) == Some(temp));
    left
}

fn declared_locals(block: &HirBlock) -> BTreeSet<LocalId> {
    let mut declarations = LocalDeclCollector::default();
    visit_stmts(&block.stmts, &mut declarations);
    declarations.locals
}

#[derive(Default)]
struct LocalDeclCollector {
    locals: BTreeSet<LocalId>,
}

impl HirVisitor for LocalDeclCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if let HirStmt::LocalDecl(decl) = stmt {
            self.locals.extend(decl.bindings.iter().copied());
        }
    }
}

#[derive(Default)]
struct BindingWriteCollector {
    locals: BTreeSet<LocalId>,
    temps: BTreeSet<TempId>,
}

impl HirVisitor for BindingWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        match lvalue {
            HirLValue::Local(local) => {
                self.locals.insert(*local);
            }
            HirLValue::Temp(temp) => {
                self.temps.insert(*temp);
            }
            HirLValue::Param(_)
            | HirLValue::Upvalue(_)
            | HirLValue::Global(_)
            | HirLValue::TableAccess(_) => {}
        }
    }
}

#[derive(Default)]
struct UserCodeEffectCollector {
    found: bool,
}

impl HirVisitor for UserCodeEffectCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.found |= matches!(stmt, HirStmt::Close(_));
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |= match expr {
            HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Binary(_)
            | HirExpr::Call(_)
            | HirExpr::Unresolved(_) => true,
            HirExpr::Unary(unary) => unary.op != HirUnaryOpKind::Not,
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Complex { .. }
            | HirExpr::Vector(_)
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
            | HirExpr::LogicalAnd(_)
            | HirExpr::LogicalOr(_)
            | HirExpr::Decision(_)
            | HirExpr::VarArg
            | HirExpr::TableConstructor(_)
            | HirExpr::Closure(_) => false,
        };
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.found |= matches!(lvalue, HirLValue::Global(_) | HirLValue::TableAccess(_));
    }

    fn visit_call(&mut self, _call: &HirCallExpr) {
        self.found = true;
    }
}

fn redundant_parallel_self_copy(assign: &HirAssign) -> bool {
    if assign.targets.len() < 2 {
        return false;
    }
    if assign.values.tail.is_some() || assign.targets.len() != assign.values.fixed.len() {
        return false;
    }
    assign
        .targets
        .iter()
        .zip(&assign.values.fixed)
        .all(|(target, value)| {
            let Some(target) = carry_binding_from_lvalue(target) else {
                return false;
            };
            let Some(value) = carry_binding_from_expr(value) else {
                return false;
            };
            target == value
        })
}

pub(super) fn prune_redundant_self_assigns_in_stmts(
    stmts: &mut [HirStmt],
    prunable_bindings: BTreeSet<CarryBinding>,
) -> bool {
    if prunable_bindings.is_empty() {
        return false;
    }
    let mut pass = RedundantSelfAssignPrunePass { prunable_bindings };
    rewrite_stmts(stmts, &mut pass)
}

pub(super) fn collect_prunable_bindings(
    bindings: impl IntoIterator<Item = CarryBinding>,
) -> BTreeSet<CarryBinding> {
    bindings.into_iter().collect()
}

fn prune_redundant_self_assign_stmt(
    stmt: &mut HirStmt,
    prunable_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let ([target], [value], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return false;
    };
    if !matches_redundant_self_assign_pair(target, value, prunable_bindings) {
        return false;
    }

    assign.targets.clear();
    assign.values.fixed.clear();
    true
}

fn matches_redundant_self_assign_pair(
    target: &HirLValue,
    value: &HirExpr,
    prunable_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    redundant_self_assign_binding(target, value)
        .is_some_and(|binding| prunable_bindings.contains(&binding))
}

fn redundant_self_assign_binding(target: &HirLValue, value: &HirExpr) -> Option<CarryBinding> {
    match (target, value) {
        (HirLValue::Param(target), HirExpr::ParamRef(value)) if target == value => {
            Some(CarryBinding::Param(*target))
        }
        (HirLValue::Temp(target), HirExpr::TempRef(value)) if target == value => {
            Some(CarryBinding::Temp(*target))
        }
        (HirLValue::Local(target), HirExpr::LocalRef(value)) if target == value => {
            Some(CarryBinding::Local(*target))
        }
        _ => None,
    }
}

fn is_empty_assign_stmt(stmt: &HirStmt) -> bool {
    matches!(stmt, HirStmt::Assign(assign) if assign.targets.is_empty())
}
