//! 稳定词法绑定的路径 truthiness 专门化。
//!
//! 本模块只服务 branch-control：它依赖已经结构化的 HIR block，并预先证明 Param/Local
//! 在整个 proto 内没有写入、for binder 或 ByReference capture，随后沿真实 fallthrough
//! 传播真假事实。事实只改写 `not/and/or` 条件骨架，不进入值表达式，也不把 truthy 原值
//! 替换成布尔结果。proto 若仍有活跃 goto/label 流，则只分析与它隔离的结构化子树与
//! 连续 clean fallthrough run；clean `If` arm 及其 tainted child 前缀可继承唯一入口的
//! header truthiness。当前 block 的 direct goto 与末端单臂 goto guard（允许 goto 前有 clean
//! prefix）会为前向 label 合流完整 predecessor facts；复杂嵌套或后向入边仍清空，出口事实
//! 也不会泄漏回污染父级。
//!
//! 例如 `if flag then break end; if flag then body end` 可删除第二个分支；若 flag 可能被
//! 赋值、闭包回写则仍保守停用。被引用 label 与任意 goto 会污染所在结构化祖先，未引用
//! label 不影响词法 fallthrough 证明。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirLabelId, HirLocalDecl, HirProto, HirStmt, HirUnaryOpKind,
    LocalId, ParamId,
};
use crate::hir::expr_safety::HirExprSafety;

use super::super::expr_facts::expr_truthiness;
use super::super::label_refs::count_label_references;
use super::super::logical_simplify::{
    simplify_condition_truthiness_shape_with_safety, simplify_logical_shape_with_safety,
};
use super::super::mention::stmts_reference_captured_bindings;
use super::super::visit::{HirVisitor, visit_proto};
use super::DiscardBoundaryFacts;

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum StableBinding {
    Param(ParamId),
    Local(LocalId),
}

fn stable_binding(expr: &HirExpr) -> Option<StableBinding> {
    match expr {
        HirExpr::ParamRef(param) => Some(StableBinding::Param(*param)),
        HirExpr::LocalRef(local) => Some(StableBinding::Local(*local)),
        _ => None,
    }
}

#[derive(Clone, Default)]
struct PathFacts(BTreeMap<StableBinding, bool>);

impl PathFacts {
    fn insert(&mut self, binding: StableBinding, truthy: bool) -> bool {
        match self.0.get(&binding) {
            Some(current) => *current == truthy,
            None => {
                self.0.insert(binding, truthy);
                true
            }
        }
    }

    fn get(&self, binding: StableBinding) -> Option<bool> {
        self.0.get(&binding).copied()
    }

    fn remove_local(&mut self, local: LocalId) {
        self.0.remove(&StableBinding::Local(local));
    }

    fn intersection(mut paths: Vec<Self>) -> Self {
        let Some(mut intersection) = paths.pop() else {
            return Self::default();
        };
        intersection
            .0
            .retain(|binding, truthy| paths.iter().all(|path| path.get(*binding) == Some(*truthy)));
        intersection
    }
}

struct StableBindingIndex {
    candidates: BTreeSet<StableBinding>,
    unstable: BTreeSet<StableBinding>,
    safety: HirExprSafety,
}

impl StableBindingIndex {
    fn new(proto: &HirProto, safety: HirExprSafety) -> Self {
        let mut index = Self {
            candidates: BTreeSet::new(),
            unstable: BTreeSet::new(),
            safety,
        };
        visit_proto(proto, &mut index);

        let captured = stmts_reference_captured_bindings(&proto.body.stmts);
        index
            .unstable
            .extend(captured.params.into_iter().map(StableBinding::Param));
        index
            .unstable
            .extend(captured.locals.into_iter().map(StableBinding::Local));
        index
    }

    fn contains(&self, binding: StableBinding) -> bool {
        self.candidates.contains(&binding) && !self.unstable.contains(&binding)
    }

    fn track_condition(&mut self, expr: &HirExpr) {
        if let Some(binding) = stable_binding(expr) {
            self.candidates.insert(binding);
            return;
        }

        match expr {
            HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
                self.track_condition(&unary.expr);
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.track_condition(&logical.lhs);
                self.track_condition(&logical.rhs);
            }
            _ => {}
        }
    }
}

impl HirVisitor for StableBindingIndex {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::If(if_stmt) => self.track_condition(&if_stmt.cond),
            HirStmt::While(while_stmt) => self.track_condition(&while_stmt.cond),
            HirStmt::Repeat(repeat_stmt) => self.track_condition(&repeat_stmt.cond),
            HirStmt::NumericFor(numeric_for) => {
                self.unstable
                    .insert(StableBinding::Local(numeric_for.binding));
            }
            HirStmt::GenericFor(generic_for) => {
                self.unstable.extend(
                    generic_for
                        .bindings
                        .iter()
                        .copied()
                        .map(StableBinding::Local),
                );
            }
            _ => {}
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        let binding = match lvalue {
            HirLValue::Param(param) => Some(StableBinding::Param(*param)),
            HirLValue::Local(local) => Some(StableBinding::Local(*local)),
            HirLValue::Temp(_)
            | HirLValue::Upvalue(_)
            | HirLValue::Global(_)
            | HirLValue::TableAccess(_) => None,
        };
        self.unstable.extend(binding);
    }
}

struct Flow {
    facts: PathFacts,
    falls_through: bool,
}

#[derive(Default)]
struct LabelPredecessors {
    accounted_refs: usize,
    reachable_facts: Vec<PathFacts>,
}

#[derive(Clone, Copy)]
struct TerminalIfExits {
    then_target: Option<HirLabelId>,
    else_target: Option<HirLabelId>,
}

pub(super) fn specialize_stable_path_conditions(
    proto: &mut HirProto,
    discard_facts: &DiscardBoundaryFacts,
    safety: HirExprSafety,
) -> bool {
    let stable = StableBindingIndex::new(proto, safety);
    let mut changed = false;
    if discard_facts
        .block_boundary(&proto.body)
        .has_live_label_flow()
    {
        rewrite_clean_islands_in_tainted_block(
            &mut proto.body,
            PathFacts::default(),
            &stable,
            discard_facts,
            &mut changed,
        );
    } else {
        rewrite_block(
            &mut proto.body,
            PathFacts::default(),
            &stable,
            discard_facts,
            &mut changed,
        );
    }
    changed
}

fn rewrite_clean_islands_in_tainted_block(
    block: &mut HirBlock,
    entry_facts: PathFacts,
    stable: &StableBindingIndex,
    discard_facts: &DiscardBoundaryFacts,
    changed: &mut bool,
) {
    let label_refs = count_label_references(&block.stmts);
    let mut label_predecessors = BTreeMap::<HirLabelId, LabelPredecessors>::new();
    let mut run_facts = Some(entry_facts);
    for stmt in &mut block.stmts {
        if !discard_facts.stmt_boundary(stmt).has_live_label_flow() {
            let run_is_reachable = run_facts.is_some();
            let flow = rewrite_stmt(
                stmt,
                run_facts.take().unwrap_or_default(),
                stable,
                discard_facts,
                changed,
            );
            run_facts = (run_is_reachable && flow.falls_through).then_some(flow.facts);
            continue;
        }

        if let HirStmt::Goto(goto) = stmt {
            let predecessor = label_predecessors.entry(goto.target).or_default();
            predecessor.accounted_refs += 1;
            predecessor.reachable_facts.extend(run_facts.take());
            continue;
        }

        if let Some(fallthrough_facts) = rewrite_terminal_if_exits(
            stmt,
            run_facts.clone(),
            stable,
            discard_facts,
            changed,
            &mut label_predecessors,
        ) {
            run_facts = fallthrough_facts;
            continue;
        }

        if let HirStmt::Label(label) = stmt {
            let mut predecessor = label_predecessors.remove(&label.id).unwrap_or_default();
            let all_refs = label_refs.get(&label.id).copied().unwrap_or_default();
            if predecessor.accounted_refs == all_refs {
                predecessor.reachable_facts.extend(run_facts.take());
                run_facts = (!predecessor.reachable_facts.is_empty())
                    .then(|| PathFacts::intersection(predecessor.reachable_facts));
            } else {
                // 候选拒绝[ProofIncomplete]：已越过该 label 的后向 goto，或嵌套在非末端/循环
                // child 内的 goto，尚未在此单向扫描点产出逐出口 facts；只合流已见入边会在
                // 真假 predecessor 并存时误专门化（regress_374 #2）。owner 是本模块的递归
                // child-exit summary；后向边还需要 predecessor fixed point。
                run_facts = Some(PathFacts::default());
            }
            continue;
        }

        // 候选拒绝[ProofIncomplete]：goto 位于循环、嵌套非末端 child 或其后仍有语句时，
        // 当前 HIR island scanner 尚无递归 child-exit summary（循环/后向边还需要 fixed
        // point）；不能把任一 child path 的 truthiness 泄漏到污染父级。clean fallthrough
        // 与双臂 terminal goto 已由 `rewrite_terminal_if_exits` 完整枚举。
        rewrite_clean_child_blocks(stmt, stable, discard_facts, changed);
        run_facts = Some(PathFacts::default());
    }
}

fn rewrite_terminal_if_exits(
    stmt: &mut HirStmt,
    entry_facts: Option<PathFacts>,
    stable: &StableBindingIndex,
    discard_facts: &DiscardBoundaryFacts,
    changed: &mut bool,
    label_predecessors: &mut BTreeMap<HirLabelId, LabelPredecessors>,
) -> Option<Option<PathFacts>> {
    let exits = terminal_if_exits(stmt, discard_facts)?;
    let HirStmt::If(if_stmt) = stmt else {
        unreachable!("terminal if exits must belong to an if")
    };
    let reachable = entry_facts.is_some();
    let entry_facts = entry_facts.unwrap_or_default();
    if reachable {
        *changed |= specialize_condition(&mut if_stmt.cond, &entry_facts, stable);
    }
    let then_facts = reachable
        .then(|| facts_for_condition(&entry_facts, &if_stmt.cond, true, stable))
        .flatten();
    let else_facts = reachable
        .then(|| facts_for_condition(&entry_facts, &if_stmt.cond, false, stable))
        .flatten();

    let then_fallthrough = rewrite_terminal_if_arm(
        &mut if_stmt.then_block,
        exits.then_target,
        then_facts,
        stable,
        discard_facts,
        changed,
        label_predecessors,
    );
    let else_fallthrough = if let Some(else_block) = &mut if_stmt.else_block {
        rewrite_terminal_if_arm(
            else_block,
            exits.else_target,
            else_facts,
            stable,
            discard_facts,
            changed,
            label_predecessors,
        )
    } else {
        debug_assert!(exits.else_target.is_none());
        else_facts
    };
    let fallthroughs = [then_fallthrough, else_fallthrough]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    Some((!fallthroughs.is_empty()).then(|| PathFacts::intersection(fallthroughs)))
}

fn rewrite_terminal_if_arm(
    block: &mut HirBlock,
    target: Option<HirLabelId>,
    facts: Option<PathFacts>,
    stable: &StableBindingIndex,
    discard_facts: &DiscardBoundaryFacts,
    changed: &mut bool,
    label_predecessors: &mut BTreeMap<HirLabelId, LabelPredecessors>,
) -> Option<PathFacts> {
    let reachable = facts.is_some();
    let flow = if target.is_some() {
        rewrite_terminal_goto_prefix(
            block,
            facts.unwrap_or_default(),
            stable,
            discard_facts,
            changed,
        )
    } else {
        rewrite_block(
            block,
            facts.unwrap_or_default(),
            stable,
            discard_facts,
            changed,
        )
    };
    if let Some(target) = target {
        let predecessor = label_predecessors.entry(target).or_default();
        predecessor.accounted_refs += 1;
        if reachable && flow.falls_through {
            predecessor.reachable_facts.push(flow.facts);
        }
        None
    } else {
        (reachable && flow.falls_through).then_some(flow.facts)
    }
}

fn terminal_if_exits(
    stmt: &HirStmt,
    discard_facts: &DiscardBoundaryFacts,
) -> Option<TerminalIfExits> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let then_target = terminal_or_clean_arm(&if_stmt.then_block, discard_facts)?;
    let else_target = if let Some(else_block) = &if_stmt.else_block {
        terminal_or_clean_arm(else_block, discard_facts)?
    } else {
        None
    };
    (then_target.is_some() || else_target.is_some()).then_some(TerminalIfExits {
        then_target,
        else_target,
    })
}

fn terminal_or_clean_arm(
    block: &HirBlock,
    discard_facts: &DiscardBoundaryFacts,
) -> Option<Option<HirLabelId>> {
    if !discard_facts.block_boundary(block).has_live_label_flow() {
        Some(None)
    } else {
        terminal_clean_goto(block, discard_facts).map(Some)
    }
}

fn terminal_clean_goto(
    block: &HirBlock,
    discard_facts: &DiscardBoundaryFacts,
) -> Option<HirLabelId> {
    let (HirStmt::Goto(goto), prefix) = block.stmts.split_last()? else {
        return None;
    };
    (!discard_facts.stmts_boundary(prefix).has_live_label_flow()).then_some(goto.target)
}

fn rewrite_terminal_goto_prefix(
    block: &mut HirBlock,
    facts: PathFacts,
    stable: &StableBindingIndex,
    discard_facts: &DiscardBoundaryFacts,
    changed: &mut bool,
) -> Flow {
    let goto = block
        .stmts
        .pop()
        .expect("terminal guarded goto block must end in goto");
    debug_assert!(matches!(goto, HirStmt::Goto(_)));
    let flow = rewrite_block(block, facts, stable, discard_facts, changed);
    block.stmts.push(goto);
    flow
}

fn rewrite_clean_child_blocks(
    stmt: &mut HirStmt,
    stable: &StableBindingIndex,
    discard_facts: &DiscardBoundaryFacts,
    changed: &mut bool,
) {
    let mut rewrite_child = |block: &mut HirBlock, facts: PathFacts| {
        if discard_facts.block_boundary(block).has_live_label_flow() {
            rewrite_clean_islands_in_tainted_block(block, facts, stable, discard_facts, changed);
        } else {
            let _ = rewrite_block(block, facts, stable, discard_facts, changed);
        }
    };

    match stmt {
        HirStmt::If(if_stmt) => {
            let empty = PathFacts::default();
            let then_facts = facts_for_condition(&empty, &if_stmt.cond, true, stable)
                .unwrap_or_else(|| empty.clone());
            let else_facts = facts_for_condition(&empty, &if_stmt.cond, false, stable)
                .unwrap_or_else(|| empty.clone());
            rewrite_child(&mut if_stmt.then_block, then_facts);
            if let Some(else_block) = &mut if_stmt.else_block {
                rewrite_child(else_block, else_facts);
            }
        }
        HirStmt::While(while_stmt) => rewrite_child(&mut while_stmt.body, PathFacts::default()),
        HirStmt::Repeat(repeat_stmt) => rewrite_child(&mut repeat_stmt.body, PathFacts::default()),
        HirStmt::NumericFor(numeric_for) => {
            rewrite_child(&mut numeric_for.body, PathFacts::default());
        }
        HirStmt::GenericFor(generic_for) => {
            rewrite_child(&mut generic_for.body, PathFacts::default());
        }
        HirStmt::Block(block) => rewrite_child(block, PathFacts::default()),
        HirStmt::LocalDecl(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
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

fn rewrite_block(
    block: &mut HirBlock,
    mut facts: PathFacts,
    stable: &StableBindingIndex,
    discard_facts: &DiscardBoundaryFacts,
    changed: &mut bool,
) -> Flow {
    let mut scoped_locals = Vec::new();
    let mut falls_through = true;
    let mut retained_len = block.stmts.len();

    for (index, stmt) in block.stmts.iter_mut().enumerate() {
        if let HirStmt::LocalDecl(local_decl) = stmt {
            scoped_locals.extend(local_decl.bindings.iter().copied());
        }
        let flow = rewrite_stmt(stmt, facts, stable, discard_facts, changed);
        facts = flow.facts;
        falls_through = flow.falls_through;
        if !falls_through {
            retained_len = index + 1;
            break;
        }
    }
    if retained_len != block.stmts.len() {
        let boundary = discard_facts.stmts_boundary(&block.stmts[retained_len..]);
        if boundary.has_control_entry() {
            // 候选拒绝[SemanticBarrier:ControlFlow]：全局 label 引用数大于尾部内部引用数，如前缀 `goto L` 指向被截尾的 `::L::`；删除尾部会丢失确定入边。
        } else if boundary.has_identity() {
            // 候选拒绝[PolicyBoundary]：尾部 debug/PhysicalRoot/TBC 身份按源码证据策略保留（regress339 retain-debug）。
        } else if boundary.has_diagnostic() {
            // 候选拒绝[LayerBoundary]：ErrNil/Unresolved 显式诊断由其 owner 保留，路径专门化不吞掉该尾部（regress339 Lua 5.5 ERRNNIL）。
        } else {
            block.stmts.truncate(retained_len);
            *changed = true;
        }
    }

    for local in scoped_locals {
        facts.remove_local(local);
    }
    Flow {
        facts,
        falls_through,
    }
}

fn rewrite_stmt(
    stmt: &mut HirStmt,
    mut facts: PathFacts,
    stable: &StableBindingIndex,
    discard_facts: &DiscardBoundaryFacts,
    changed: &mut bool,
) -> Flow {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            record_local_declaration(local_decl, &mut facts, stable);
        }
        HirStmt::If(if_stmt) => {
            *changed |= specialize_condition(&mut if_stmt.cond, &facts, stable);
            let condition_truthiness = expr_truthiness(&if_stmt.cond, stable.safety);
            let then_facts = facts_for_condition(&facts, &if_stmt.cond, true, stable);
            let else_facts = facts_for_condition(&facts, &if_stmt.cond, false, stable);
            let then_reachable = condition_truthiness != Some(false) && then_facts.is_some();
            let else_reachable = condition_truthiness != Some(true) && else_facts.is_some();

            let then_flow = rewrite_block(
                &mut if_stmt.then_block,
                then_facts.unwrap_or_else(|| facts.clone()),
                stable,
                discard_facts,
                changed,
            );
            let else_flow = if_stmt.else_block.as_mut().map(|else_block| {
                rewrite_block(
                    else_block,
                    else_facts.clone().unwrap_or_else(|| facts.clone()),
                    stable,
                    discard_facts,
                    changed,
                )
            });
            let then_falls_through = then_reachable && then_flow.falls_through;
            let else_falls_through =
                else_reachable && else_flow.as_ref().is_none_or(|flow| flow.falls_through);

            let mut exits = Vec::new();
            if then_falls_through {
                exits.push(then_flow.facts);
            }
            if else_reachable {
                if let Some(else_flow) = else_flow {
                    if else_flow.falls_through {
                        exits.push(else_flow.facts);
                    }
                } else if let Some(else_facts) = else_facts {
                    exits.push(else_facts);
                }
            }
            return Flow {
                facts: PathFacts::intersection(exits),
                falls_through: then_falls_through || else_falls_through,
            };
        }
        HirStmt::While(while_stmt) => {
            *changed |= specialize_condition(&mut while_stmt.cond, &facts, stable);
            let body_facts = facts_for_condition(&facts, &while_stmt.cond, true, stable)
                .unwrap_or_else(|| facts.clone());
            rewrite_block(
                &mut while_stmt.body,
                body_facts,
                stable,
                discard_facts,
                changed,
            );
        }
        HirStmt::Repeat(repeat_stmt) => {
            rewrite_block(
                &mut repeat_stmt.body,
                facts.clone(),
                stable,
                discard_facts,
                changed,
            );
            *changed |= specialize_condition(&mut repeat_stmt.cond, &facts, stable);
        }
        HirStmt::NumericFor(numeric_for) => {
            rewrite_block(
                &mut numeric_for.body,
                facts.clone(),
                stable,
                discard_facts,
                changed,
            );
        }
        HirStmt::GenericFor(generic_for) => {
            rewrite_block(
                &mut generic_for.body,
                facts.clone(),
                stable,
                discard_facts,
                changed,
            );
        }
        HirStmt::Block(block) => {
            return rewrite_block(block, facts, stable, discard_facts, changed);
        }
        HirStmt::Return(_) | HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) => {
            return Flow {
                facts,
                falls_through: false,
            };
        }
        HirStmt::Assign(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Label(_) => {}
    }

    Flow {
        facts,
        falls_through: true,
    }
}

fn record_local_declaration(
    local_decl: &HirLocalDecl,
    facts: &mut PathFacts,
    stable: &StableBindingIndex,
) {
    for local in &local_decl.bindings {
        facts.remove_local(*local);
    }
    let ([local], [value], None) = (
        local_decl.bindings.as_slice(),
        local_decl.values.fixed.as_slice(),
        &local_decl.values.tail,
    ) else {
        return;
    };
    let binding = StableBinding::Local(*local);
    if stable.contains(binding)
        && let Some(truthy) = expr_truthiness(value, stable.safety)
    {
        let inserted = facts.insert(binding, truthy);
        assert!(
            inserted,
            "new local declaration cannot contradict prior facts"
        );
    }
}

fn specialize_condition(
    expr: &mut HirExpr,
    facts: &PathFacts,
    stable: &StableBindingIndex,
) -> bool {
    if let Some(truthy) = stable_binding(expr)
        .filter(|binding| stable.contains(*binding))
        .and_then(|binding| facts.get(binding))
    {
        *expr = HirExpr::Boolean(truthy);
        return true;
    }

    let mut changed = match expr {
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            specialize_condition(&mut unary.expr, facts, stable)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            specialize_condition(&mut logical.lhs, facts, stable)
                | specialize_condition(&mut logical.rhs, facts, stable)
        }
        _ => false,
    };
    loop {
        let replacement = simplify_logical_shape_with_safety(expr, stable.safety)
            .or_else(|| simplify_condition_truthiness_shape_with_safety(expr, stable.safety));
        let Some(replacement) = replacement.filter(|replacement| replacement != expr) else {
            break;
        };
        *expr = replacement;
        changed = true;
    }
    changed
}

fn facts_for_condition(
    facts: &PathFacts,
    expr: &HirExpr,
    truthy: bool,
    stable: &StableBindingIndex,
) -> Option<PathFacts> {
    let mut extended = facts.clone();
    extend_condition_facts(&mut extended, expr, truthy, stable).then_some(extended)
}

fn extend_condition_facts(
    facts: &mut PathFacts,
    expr: &HirExpr,
    truthy: bool,
    stable: &StableBindingIndex,
) -> bool {
    if let Some(known) = expr_truthiness(expr, stable.safety) {
        return known == truthy;
    }

    if let Some(binding) = stable_binding(expr).filter(|binding| stable.contains(*binding)) {
        return facts.insert(binding, truthy);
    }

    match expr {
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            extend_condition_facts(facts, &unary.expr, !truthy, stable)
        }
        HirExpr::LogicalAnd(logical) if truthy => {
            extend_condition_facts(facts, &logical.lhs, true, stable)
                && extend_condition_facts(facts, &logical.rhs, true, stable)
        }
        HirExpr::LogicalOr(logical) if !truthy => {
            extend_condition_facts(facts, &logical.lhs, false, stable)
                && extend_condition_facts(facts, &logical.rhs, false, stable)
        }
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use super::super::DiscardBoundaryFacts;
    use super::*;
    use crate::decompile::DecompileDialect;
    use crate::hir::common::{HirGoto, HirIf, HirLabel, HirReturn, HirValuePack, ParamId};
    use crate::hir::expr_safety::HirExprSafety;

    fn stable_params(params: impl IntoIterator<Item = ParamId>) -> StableBindingIndex {
        StableBindingIndex {
            candidates: params.into_iter().map(StableBinding::Param).collect(),
            unstable: BTreeSet::new(),
            safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
        }
    }

    fn discard_facts(block: &HirBlock) -> DiscardBoundaryFacts {
        DiscardBoundaryFacts {
            protected_locals: BTreeSet::new(),
            protected_temps: BTreeSet::new(),
            label_refs: count_label_references(&block.stmts),
        }
    }

    fn goto(target: HirLabelId) -> HirStmt {
        HirStmt::Goto(Box::new(HirGoto { target }))
    }

    fn label(id: HirLabelId) -> HirStmt {
        HirStmt::Label(Box::new(HirLabel {
            id,
            tbc_barriers: Vec::new(),
        }))
    }

    fn if_stmt(
        cond: HirExpr,
        then_stmts: Vec<HirStmt>,
        else_stmts: Option<Vec<HirStmt>>,
    ) -> HirStmt {
        HirStmt::If(Box::new(HirIf {
            cond,
            then_block: HirBlock { stmts: then_stmts },
            else_block: else_stmts.map(|stmts| HirBlock { stmts }),
        }))
    }

    fn return_stmt() -> HirStmt {
        HirStmt::Return(Box::new(HirReturn {
            values: HirValuePack::default(),
        }))
    }

    fn condition_at(block: &HirBlock, index: usize) -> &HirExpr {
        let HirStmt::If(if_stmt) = &block.stmts[index] else {
            panic!("expected if statement at index {index}")
        };
        &if_stmt.cond
    }

    #[test]
    fn tracks_every_condition_binding() {
        let safety = HirExprSafety::for_dialect(DecompileDialect::Lua54);
        let mut index = StableBindingIndex {
            candidates: Default::default(),
            unstable: Default::default(),
            safety,
        };
        for param in 0..=256 {
            index.track_condition(&HirExpr::ParamRef(ParamId(param)));
        }

        assert_eq!(index.candidates.len(), 257);
        assert!(index.contains(StableBinding::Param(ParamId(0))));
        assert!(index.contains(StableBinding::Param(ParamId(256))));
    }

    #[test]
    fn double_terminal_goto_propagates_each_arm_fact_to_its_label() {
        let flag = ParamId(0);
        let truthy = HirLabelId(0);
        let falsy = HirLabelId(1);
        let mut block = HirBlock {
            stmts: vec![
                if_stmt(
                    HirExpr::ParamRef(flag),
                    vec![goto(truthy)],
                    Some(vec![goto(falsy)]),
                ),
                label(truthy),
                if_stmt(HirExpr::ParamRef(flag), Vec::new(), None),
                return_stmt(),
                label(falsy),
                if_stmt(HirExpr::ParamRef(flag), Vec::new(), None),
            ],
        };
        let stable = stable_params([flag]);
        let discard_facts = discard_facts(&block);
        let mut changed = false;

        rewrite_clean_islands_in_tainted_block(
            &mut block,
            PathFacts::default(),
            &stable,
            &discard_facts,
            &mut changed,
        );

        assert!(changed);
        assert_eq!(condition_at(&block, 2), &HirExpr::Boolean(true));
        assert_eq!(condition_at(&block, 5), &HirExpr::Boolean(false));
    }

    #[test]
    fn backward_goto_prevents_using_only_the_seen_forward_predecessor() {
        let flag = ParamId(0);
        let loop_label = HirLabelId(0);
        let mut block = HirBlock {
            stmts: vec![
                if_stmt(HirExpr::ParamRef(flag), vec![goto(loop_label)], None),
                return_stmt(),
                label(loop_label),
                if_stmt(HirExpr::ParamRef(flag), Vec::new(), None),
                if_stmt(
                    HirExpr::ParamRef(flag).negate(),
                    vec![goto(loop_label)],
                    None,
                ),
            ],
        };
        let stable = stable_params([flag]);
        let discard_facts = discard_facts(&block);
        let mut changed = false;

        rewrite_clean_islands_in_tainted_block(
            &mut block,
            PathFacts::default(),
            &stable,
            &discard_facts,
            &mut changed,
        );

        assert_eq!(condition_at(&block, 3), &HirExpr::ParamRef(flag));
    }
}
