//! 稳定词法绑定的路径 truthiness 专门化。
//!
//! 本模块只服务 branch-control：它依赖已经结构化的 HIR block，并预先证明 Param/Local
//! 在整个 proto 内没有写入、for binder 或 ByReference capture，随后沿真实 fallthrough
//! 传播真假事实。事实只改写 `not/and/or` 条件骨架，不进入值表达式，也不把 truthy 原值
//! 替换成布尔结果。proto 若仍有活跃 goto/label 流，则只分析与它隔离的结构化子树与
//! 连续 clean fallthrough run；clean `If` arm 及其 tainted child 前缀可继承唯一入口的
//! header truthiness。tainted block 内只从 entry 与已可达 label 传播事实；direct、嵌套与
//! 后向 goto 都进入 label 的 must-fact 固定点，结构上不可达或与已知条件矛盾的边不参与
//! 合流，出口事实也不会泄漏回污染父级。
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
use super::super::logical_simplify::{
    simplify_condition_truthiness_shape_with_safety, simplify_logical_shape_with_safety,
};
use super::super::mention::stmts_reference_captured_bindings;
use super::DiscardBoundaryFacts;
use crate::hir::visit::{HirVisitor, visit_proto};

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

#[derive(Clone, Default, Eq, PartialEq)]
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

#[derive(Clone, Copy)]
struct TerminalIfExits {
    then_target: Option<HirLabelId>,
    else_target: Option<HirLabelId>,
}

fn fixed_point_label_facts(
    block: &HirBlock,
    entry_facts: PathFacts,
    stable: &StableBindingIndex,
) -> BTreeMap<HirLabelId, PathFacts> {
    let mut label_facts = BTreeMap::new();
    loop {
        let mut incoming = BTreeMap::<HirLabelId, Vec<PathFacts>>::new();
        let _ = analyze_tainted_block(
            block,
            AnalysisState::reachable(entry_facts.clone()),
            &label_facts,
            stable,
            &mut incoming,
        );
        let next = incoming
            .into_iter()
            .filter_map(|(label, facts)| {
                (!facts.is_empty()).then(|| (label, PathFacts::intersection(facts)))
            })
            .collect::<BTreeMap<_, _>>();
        if next == label_facts {
            return next;
        }
        label_facts = next;
    }
}

#[derive(Clone)]
enum AnalysisState {
    Reachable(PathFacts),
    Dead,
}

impl AnalysisState {
    fn reachable(facts: PathFacts) -> Self {
        Self::Reachable(facts)
    }

    fn facts(&self) -> Option<&PathFacts> {
        match self {
            Self::Reachable(facts) => Some(facts),
            Self::Dead => None,
        }
    }

    fn into_rewrite_facts(self) -> Option<PathFacts> {
        match self {
            Self::Reachable(facts) => Some(facts),
            Self::Dead => None,
        }
    }
}

fn analyze_tainted_block(
    block: &HirBlock,
    mut state: AnalysisState,
    label_facts: &BTreeMap<HirLabelId, PathFacts>,
    stable: &StableBindingIndex,
    incoming: &mut BTreeMap<HirLabelId, Vec<PathFacts>>,
) -> AnalysisState {
    let mut scoped_locals = Vec::new();
    for stmt in &block.stmts {
        if let HirStmt::Label(label) = stmt {
            if let Some(fallthrough) = state.facts().cloned() {
                incoming.entry(label.id).or_default().push(fallthrough);
            }
            let mut predecessors = incoming.get(&label.id).cloned().unwrap_or_default();
            predecessors.extend(label_facts.get(&label.id).cloned());
            state = if predecessors.is_empty() {
                AnalysisState::Dead
            } else {
                AnalysisState::reachable(PathFacts::intersection(predecessors))
            };
            continue;
        }
        if let HirStmt::LocalDecl(local_decl) = stmt {
            scoped_locals.extend(local_decl.bindings.iter().copied());
        }
        state = analyze_tainted_stmt(stmt, state, label_facts, stable, incoming);
    }
    if let AnalysisState::Reachable(facts) = &mut state {
        for local in scoped_locals {
            facts.remove_local(local);
        }
    }
    state
}

fn analyze_tainted_stmt(
    stmt: &HirStmt,
    state: AnalysisState,
    label_facts: &BTreeMap<HirLabelId, PathFacts>,
    stable: &StableBindingIndex,
    incoming: &mut BTreeMap<HirLabelId, Vec<PathFacts>>,
) -> AnalysisState {
    let AnalysisState::Reachable(mut facts) = state else {
        return AnalysisState::Dead;
    };
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            record_local_declaration(local_decl, &mut facts, stable);
            AnalysisState::reachable(facts)
        }
        HirStmt::If(if_stmt) => {
            let then_state = conditional_state(&facts, &if_stmt.cond, true, stable);
            let else_state = conditional_state(&facts, &if_stmt.cond, false, stable);
            let then_exit = analyze_tainted_block(
                &if_stmt.then_block,
                then_state,
                label_facts,
                stable,
                incoming,
            );
            let else_exit = if let Some(else_block) = &if_stmt.else_block {
                analyze_tainted_block(else_block, else_state, label_facts, stable, incoming)
            } else {
                else_state
            };
            merge_analysis_states([then_exit, else_exit])
        }
        HirStmt::Block(block) => analyze_tainted_block(
            block,
            AnalysisState::reachable(facts),
            label_facts,
            stable,
            incoming,
        ),
        HirStmt::While(while_stmt) => {
            let body_state = conditional_state(&facts, &while_stmt.cond, true, stable);
            let _ =
                analyze_tainted_block(&while_stmt.body, body_state, label_facts, stable, incoming);
            AnalysisState::reachable(facts)
        }
        HirStmt::Repeat(repeat_stmt) => {
            let _ = analyze_tainted_block(
                &repeat_stmt.body,
                AnalysisState::reachable(facts.clone()),
                label_facts,
                stable,
                incoming,
            );
            AnalysisState::reachable(facts)
        }
        HirStmt::NumericFor(numeric_for) => {
            let _ = analyze_tainted_block(
                &numeric_for.body,
                AnalysisState::reachable(facts.clone()),
                label_facts,
                stable,
                incoming,
            );
            AnalysisState::reachable(facts)
        }
        HirStmt::GenericFor(generic_for) => {
            let _ = analyze_tainted_block(
                &generic_for.body,
                AnalysisState::reachable(facts.clone()),
                label_facts,
                stable,
                incoming,
            );
            AnalysisState::reachable(facts)
        }
        HirStmt::Goto(goto) => {
            incoming.entry(goto.target).or_default().push(facts);
            AnalysisState::Dead
        }
        HirStmt::Return(_) | HirStmt::Break | HirStmt::Continue => AnalysisState::Dead,
        HirStmt::Assign(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Label(_) => AnalysisState::reachable(facts),
    }
}

fn conditional_state(
    facts: &PathFacts,
    condition: &HirExpr,
    truthy: bool,
    stable: &StableBindingIndex,
) -> AnalysisState {
    if expr_truthiness(condition, stable.safety).is_some_and(|known| known != truthy) {
        return AnalysisState::Dead;
    }
    facts_for_condition(facts, condition, truthy, stable)
        .map_or(AnalysisState::Dead, AnalysisState::reachable)
}

fn merge_analysis_states(states: impl IntoIterator<Item = AnalysisState>) -> AnalysisState {
    let facts = states
        .into_iter()
        .filter_map(|state| match state {
            AnalysisState::Reachable(facts) => Some(facts),
            AnalysisState::Dead => None,
        })
        .collect::<Vec<_>>();
    if facts.is_empty() {
        AnalysisState::Dead
    } else {
        AnalysisState::reachable(PathFacts::intersection(facts))
    }
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
    let complete_label_facts = fixed_point_label_facts(block, entry_facts.clone(), stable);
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

        if matches!(stmt, HirStmt::Goto(_)) {
            run_facts = None;
            continue;
        }

        if let Some(fallthrough_facts) =
            rewrite_terminal_if_exits(stmt, run_facts.clone(), stable, discard_facts, changed)
        {
            run_facts = fallthrough_facts;
            continue;
        }

        if let HirStmt::Label(label) = stmt {
            run_facts = complete_label_facts.get(&label.id).cloned();
            continue;
        }

        let mut ignored_incoming = BTreeMap::new();
        let exit_facts = analyze_tainted_stmt(
            stmt,
            run_facts
                .clone()
                .map_or(AnalysisState::Dead, AnalysisState::reachable),
            &complete_label_facts,
            stable,
            &mut ignored_incoming,
        )
        .into_rewrite_facts();
        rewrite_clean_child_blocks(
            stmt,
            run_facts.clone().unwrap_or_default(),
            stable,
            discard_facts,
            changed,
        );
        run_facts = exit_facts;
    }
}

fn rewrite_terminal_if_exits(
    stmt: &mut HirStmt,
    entry_facts: Option<PathFacts>,
    stable: &StableBindingIndex,
    discard_facts: &DiscardBoundaryFacts,
    changed: &mut bool,
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
    );
    let else_fallthrough = if let Some(else_block) = &mut if_stmt.else_block {
        rewrite_terminal_if_arm(
            else_block,
            exits.else_target,
            else_facts,
            stable,
            discard_facts,
            changed,
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
    if target.is_some() {
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
    entry_facts: PathFacts,
    stable: &StableBindingIndex,
    discard_facts: &DiscardBoundaryFacts,
    changed: &mut bool,
) {
    match stmt {
        HirStmt::If(if_stmt) => {
            *changed |= specialize_condition(&mut if_stmt.cond, &entry_facts, stable);
        }
        HirStmt::While(while_stmt) => {
            *changed |= specialize_condition(&mut while_stmt.cond, &entry_facts, stable);
        }
        HirStmt::Repeat(repeat_stmt) => {
            *changed |= specialize_condition(&mut repeat_stmt.cond, &entry_facts, stable);
        }
        _ => {}
    }
    let mut rewrite_child = |block: &mut HirBlock, facts: PathFacts| {
        if discard_facts.block_boundary(block).has_live_label_flow() {
            rewrite_clean_islands_in_tainted_block(block, facts, stable, discard_facts, changed);
        } else {
            let _ = rewrite_block(block, facts, stable, discard_facts, changed);
        }
    };

    match stmt {
        HirStmt::If(if_stmt) => {
            let then_facts = facts_for_condition(&entry_facts, &if_stmt.cond, true, stable)
                .unwrap_or_else(|| entry_facts.clone());
            let else_facts = facts_for_condition(&entry_facts, &if_stmt.cond, false, stable)
                .unwrap_or_else(|| entry_facts.clone());
            rewrite_child(&mut if_stmt.then_block, then_facts);
            if let Some(else_block) = &mut if_stmt.else_block {
                rewrite_child(else_block, else_facts);
            }
        }
        HirStmt::While(while_stmt) => {
            let body_facts = facts_for_condition(&entry_facts, &while_stmt.cond, true, stable)
                .unwrap_or_else(|| entry_facts.clone());
            rewrite_child(&mut while_stmt.body, body_facts);
        }
        HirStmt::Repeat(repeat_stmt) => {
            rewrite_child(&mut repeat_stmt.body, entry_facts);
        }
        HirStmt::NumericFor(numeric_for) => {
            rewrite_child(&mut numeric_for.body, entry_facts);
        }
        HirStmt::GenericFor(generic_for) => {
            rewrite_child(&mut generic_for.body, entry_facts);
        }
        HirStmt::Block(block) => rewrite_child(block, entry_facts),
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
            // 候选拒绝[PolicyBoundary]：项目保留不可达尾部中的 ErrNil/Unresolved
            // permissive 诊断，路径专门化不吞掉失败证据（regress339 Lua 5.5 ERRNNIL）。
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
    use crate::hir::common::{
        HirGoto, HirIf, HirLabel, HirReturn, HirValuePack, HirWhile, ParamId,
    };
    use crate::hir::expr_safety::HirExprSafety;
    use crate::hir::simplify::label_refs::count_label_references;

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
    fn nonterminal_child_goto_propagates_header_fact_to_label() {
        let flag = ParamId(0);
        let gate = ParamId(1);
        let target = HirLabelId(0);
        let mut block = HirBlock {
            stmts: vec![
                if_stmt(
                    HirExpr::ParamRef(flag),
                    vec![
                        if_stmt(HirExpr::ParamRef(gate), vec![goto(target)], None),
                        return_stmt(),
                    ],
                    None,
                ),
                return_stmt(),
                label(target),
                if_stmt(HirExpr::ParamRef(flag), Vec::new(), None),
            ],
        };
        let stable = stable_params([flag, gate]);
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
        assert_eq!(condition_at(&block, 3), &HirExpr::Boolean(true));
    }

    #[test]
    fn structurally_dead_gotos_do_not_pollute_label_facts() {
        let flag = ParamId(0);
        let target = HirLabelId(0);
        let mut block = HirBlock {
            stmts: vec![
                if_stmt(HirExpr::ParamRef(flag), vec![goto(target)], None),
                if_stmt(HirExpr::Boolean(false), vec![goto(target)], None),
                HirStmt::While(Box::new(HirWhile {
                    cond: HirExpr::Boolean(false),
                    body: HirBlock {
                        stmts: vec![goto(target)],
                    },
                })),
                return_stmt(),
                goto(target),
                label(target),
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
        assert_eq!(condition_at(&block, 6), &HirExpr::Boolean(true));
    }

    #[test]
    fn contradictory_nested_guard_does_not_create_label_predecessor() {
        let flag = ParamId(0);
        let target = HirLabelId(0);
        let mut block = HirBlock {
            stmts: vec![
                if_stmt(
                    HirExpr::ParamRef(flag),
                    vec![
                        if_stmt(HirExpr::ParamRef(flag).negate(), vec![goto(target)], None),
                        goto(target),
                    ],
                    None,
                ),
                return_stmt(),
                label(target),
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
        assert_eq!(condition_at(&block, 3), &HirExpr::Boolean(true));
    }

    #[test]
    fn self_supporting_contradictory_backedge_is_unreachable() {
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

        assert!(changed);
        assert_eq!(condition_at(&block, 3), &HirExpr::Boolean(true));
    }

    #[test]
    fn backward_graph_keeps_real_unknown_predecessor() {
        let flag = ParamId(0);
        let jump_right = ParamId(1);
        let cycle = ParamId(2);
        let left = HirLabelId(0);
        let right = HirLabelId(1);
        let mut block = HirBlock {
            stmts: vec![
                if_stmt(HirExpr::ParamRef(jump_right), vec![goto(right)], None),
                if_stmt(HirExpr::ParamRef(flag), vec![return_stmt()], None),
                label(left),
                if_stmt(HirExpr::ParamRef(cycle), vec![goto(right)], None),
                return_stmt(),
                label(right),
                if_stmt(HirExpr::ParamRef(flag), Vec::new(), None),
                if_stmt(HirExpr::ParamRef(cycle), vec![goto(left)], None),
            ],
        };
        let stable = stable_params([flag, jump_right, cycle]);
        let discard_facts = discard_facts(&block);
        let mut changed = false;

        rewrite_clean_islands_in_tainted_block(
            &mut block,
            PathFacts::default(),
            &stable,
            &discard_facts,
            &mut changed,
        );

        assert_eq!(condition_at(&block, 6), &HirExpr::ParamRef(flag));
    }
}
