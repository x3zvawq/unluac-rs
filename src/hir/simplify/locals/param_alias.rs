//! 参数 alias 收敛是 locals pass 的后置步骤。
//!
//! locals pass 把跨语句存活的 temp 提升成 local 后，函数入口处可能出现机械别名：
//! `local L = P` 或 `local L; L = P`。如果后续代码只通过这个别名继续读写参数槽位，
//! 保留新 local 会把同一个源码身份拆成两个 binding，并把修复压力推给 AST/Naming。
//!
//! 输入形状 -> 输出形状：
//! ```text
//! local l0 = p0             if p0 > 0 then
//! if p0 > 0 then      =>      p0 = p0 + 1
//!   l0 = p0 + 1             end
//! end                       return p0
//! return l0
//! ```
//!
//! 这里不重新推断前层 phi，也不处理任意 local 对；它只沿结构化语句证明参数与 alias
//! 从入口相同值开始不会被分别观察。分析逐路径记录最后写入的一侧以及已经逃逸的 reference
//! capture；`return/break/continue` 不参与错误的普通合流，循环则对回边状态求有限不动点。
//! 残留 goto/label 仍交给持有 CFG owner 的 Structure island/branch-control 收敛。
//! alias 后续写入会提前覆盖参数，因此还要求两者属于同一可信物理 home；仅有显式读写
//! 等价不足以排除弱表、`__gc` 或异常 cleanup 对旧参数存活期的观察。
//! 实际发生的 `Local -> Param` 引用改写还会把失效的 home provenance 传播到参数，避免
//! deferred carried-local 的下一轮把换壳后的参数重新当作可信物理槽。

use std::collections::BTreeSet;

use crate::hir::common::{
    HirBlock, HirCaptureMode, HirExpr, HirLValue, HirLocalDecl, HirProto, HirStmt, LocalId, ParamId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::expr_facts::expr_truthiness;
use super::super::mention::expr_mentions_local;
use super::super::visit::{self, HirVisitor};
use super::super::walk::{self, HirRewritePass};

pub(super) fn coalesce_param_aliases_in_proto(
    proto: &mut HirProto,
    promotion_facts: &mut ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    let Some(alias) = match_param_alias_prefix(&proto.body) else {
        return false;
    };
    let shares_exact_home = promotion_facts
        .trusted_local_home_slot(alias.local)
        .zip(promotion_facts.trusted_param_home_slot(alias.param))
        .is_some_and(|(local, param)| local == param);
    let rest = &proto.body.stmts[alias.consumed..];
    if !shares_exact_home {
        // 候选拒绝[SemanticBarrier:Lifetime]：`local l=p; weak[p]=true; l={}; GC` 中跨槽合并会覆盖 p 并让原对象提前回收，原程序的参数槽仍应持有它。
        return false;
    }
    if proto
        .local_debug_hints
        .get(alias.local.index())
        .is_some_and(Option::is_some)
    {
        // 候选拒绝[PolicyBoundary]：带 source debug identity 的 alias local 保留独立声明，不把其名称与词法范围折入参数。
        return false;
    }
    if let Err(error) =
        validate_alias_flow(rest, alias.local, alias.param, AliasStates::entry(), safety)
    {
        match error {
            AliasFlowError::ValueFlow => {
                // 候选拒绝[SemanticBarrier:ValueFlow]：同一路径写一侧后读取另一侧会区分两个 binding；如 `l=1; return p` 或 `p=2; return l`，合并后返回新值而非旧值。
            }
            AliasFlowError::Capture => {
                // 候选拒绝[SemanticBarrier:Capture]：reference capture 暴露一侧 cell 后再写另一侧时，逃逸 closure 可观察原 cell；合并会让它观察后续写入。
            }
            AliasFlowError::Resource => {
                // 候选拒绝[SemanticBarrier:Resource]：`local l=p; <TBC l>; l=q` 若改为参数，会更换 close owner，并可能关闭错误值或改变关闭时点。
            }
            AliasFlowError::UnstructuredControl => {
                // 候选拒绝[LayerBoundary]：残留 label/goto 的 predecessor 与目标边由 Structure island/branch-control owner 维护；locals 不在线性 HIR 上重建 CFG。
            }
            AliasFlowError::BindingInvariant => {
                // 候选拒绝[ConvergenceGuard]：alias LocalId 在后缀再次充当声明或 for binder 违反唯一 binding 身份；删除入口声明会改变异常 HIR 的作用域。
            }
        }
        return false;
    }

    let mut tail = proto.body.stmts.split_off(alias.consumed);
    let rewritten = walk::rewrite_stmts(
        &mut tail,
        &mut LocalToParamRewrite {
            local: alias.local,
            param: alias.param,
        },
    );
    if rewritten {
        promotion_facts.record_local_to_param_merge(alias.local, alias.param);
    }
    proto.body.stmts.append(&mut tail);
    proto.body.stmts.drain(..alias.consumed);
    true
}

#[derive(Clone, Copy)]
struct ParamAliasPrefix {
    local: LocalId,
    param: ParamId,
    consumed: usize,
}

fn match_param_alias_prefix(block: &HirBlock) -> Option<ParamAliasPrefix> {
    match_param_alias_local_decl(block).or_else(|| match_param_alias_decl_assign(block))
}

fn match_param_alias_local_decl(block: &HirBlock) -> Option<ParamAliasPrefix> {
    let HirStmt::LocalDecl(local_decl) = block.stmts.first()? else {
        return None;
    };
    let local = single_local_binding(local_decl)?;
    let [value] = local_decl.values.fixed.as_slice() else {
        return None;
    };
    if local_decl.values.tail.is_some() {
        return None;
    }
    let HirExpr::ParamRef(param) = value else {
        return None;
    };
    Some(ParamAliasPrefix {
        local,
        param: *param,
        consumed: 1,
    })
}

fn match_param_alias_decl_assign(block: &HirBlock) -> Option<ParamAliasPrefix> {
    let [HirStmt::LocalDecl(local_decl), HirStmt::Assign(assign), ..] = block.stmts.as_slice()
    else {
        return None;
    };
    if !local_decl.values.is_empty() {
        return None;
    }
    let local = single_local_binding(local_decl)?;
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    if !matches!(target, HirLValue::Local(target) if *target == local) {
        return None;
    }
    let HirExpr::ParamRef(param) = value else {
        return None;
    };
    Some(ParamAliasPrefix {
        local,
        param: *param,
        consumed: 2,
    })
}

fn single_local_binding(local_decl: &HirLocalDecl) -> Option<LocalId> {
    let [local] = local_decl.bindings.as_slice() else {
        return None;
    };
    Some(*local)
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Divergence {
    Equal,
    LocalWritten,
    ParamWritten,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct AliasState {
    divergence: Divergence,
    local_reference_exposed: bool,
    param_reference_exposed: bool,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct AliasStates(BTreeSet<AliasState>);

impl AliasStates {
    fn entry() -> Self {
        Self(BTreeSet::from([AliasState {
            divergence: Divergence::Equal,
            local_reference_exposed: false,
            param_reference_exposed: false,
        }]))
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn union(mut self, other: Self) -> Self {
        self.0.extend(other.0);
        self
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct AliasFlow {
    fallthrough: AliasStates,
    breaks: AliasStates,
    continues: AliasStates,
}

impl AliasFlow {
    fn fallthrough(states: AliasStates) -> Self {
        Self {
            fallthrough: states,
            ..Self::default()
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AliasFlowError {
    ValueFlow,
    Capture,
    Resource,
    UnstructuredControl,
    BindingInvariant,
}

fn validate_alias_flow(
    stmts: &[HirStmt],
    local: LocalId,
    param: ParamId,
    mut states: AliasStates,
    safety: HirExprSafety,
) -> Result<AliasFlow, AliasFlowError> {
    let mut breaks = AliasStates::default();
    let mut continues = AliasStates::default();
    for stmt in stmts {
        if states.is_empty() {
            break;
        }
        let flow = validate_alias_stmt(stmt, local, param, states, safety)?;
        states = flow.fallthrough;
        breaks = breaks.union(flow.breaks);
        continues = continues.union(flow.continues);
    }
    Ok(AliasFlow {
        fallthrough: states,
        breaks,
        continues,
    })
}

fn validate_alias_stmt(
    stmt: &HirStmt,
    local: LocalId,
    param: ParamId,
    states: AliasStates,
    safety: HirExprSafety,
) -> Result<AliasFlow, AliasFlowError> {
    match stmt {
        HirStmt::If(if_stmt) => {
            let states = evaluate_expr(&if_stmt.cond, local, param, states)?;
            let then_flow = if expr_truthiness(&if_stmt.cond, safety) == Some(false) {
                AliasFlow::fallthrough(AliasStates::default())
            } else {
                validate_alias_flow(
                    &if_stmt.then_block.stmts,
                    local,
                    param,
                    states.clone(),
                    safety,
                )?
            };
            let else_flow = if expr_truthiness(&if_stmt.cond, safety) == Some(true) {
                AliasFlow::fallthrough(AliasStates::default())
            } else if let Some(else_block) = &if_stmt.else_block {
                validate_alias_flow(&else_block.stmts, local, param, states, safety)?
            } else {
                AliasFlow::fallthrough(states)
            };
            Ok(union_alias_flows(then_flow, else_flow))
        }
        HirStmt::While(while_stmt) => validate_while_alias(
            &while_stmt.body,
            &while_stmt.cond,
            local,
            param,
            states,
            safety,
        ),
        HirStmt::Repeat(repeat_stmt) => validate_repeat_alias(
            &repeat_stmt.body,
            &repeat_stmt.cond,
            local,
            param,
            states,
            safety,
        ),
        HirStmt::NumericFor(numeric_for) => {
            if numeric_for.binding == local {
                return Err(AliasFlowError::BindingInvariant);
            }
            let mut evaluated = states;
            for expr in [&numeric_for.start, &numeric_for.limit, &numeric_for.step] {
                evaluated = evaluate_expr(expr, local, param, evaluated)?;
            }
            validate_zero_or_more_alias(
                &numeric_for.body,
                local,
                param,
                evaluated.clone(),
                evaluated,
                false,
                safety,
            )
        }
        HirStmt::GenericFor(generic_for) => {
            if generic_for.bindings.contains(&local) {
                return Err(AliasFlowError::BindingInvariant);
            }
            let mut evaluated = states;
            for expr in &generic_for.iterator {
                evaluated = evaluate_expr(expr, local, param, evaluated)?;
            }
            // Generic-for invokes the iterator once even on the zero-iteration path and once
            // after every completed body iteration. The iterator may observe or mutate either
            // side through a reference capture that escaped while constructing the iterator.
            let zero_exit = evaluate_opaque_callback(local, param, evaluated)?;
            validate_zero_or_more_alias(
                &generic_for.body,
                local,
                param,
                zero_exit.clone(),
                zero_exit,
                true,
                safety,
            )
        }
        HirStmt::Block(block) => validate_alias_flow(&block.stmts, local, param, states, safety),
        HirStmt::ToBeClosed(to_be_closed) if expr_mentions_local(&to_be_closed.value, local) => {
            Err(AliasFlowError::Resource)
        }
        HirStmt::Goto(_) | HirStmt::Label(_) => Err(AliasFlowError::UnstructuredControl),
        HirStmt::LocalDecl(local_decl) if local_decl.bindings.contains(&local) => {
            Err(AliasFlowError::BindingInvariant)
        }
        HirStmt::Return(_) => {
            evaluate_leaf_stmt(stmt, local, param, states)?;
            Ok(AliasFlow::default())
        }
        HirStmt::Break => Ok(AliasFlow {
            breaks: states,
            ..AliasFlow::default()
        }),
        HirStmt::Continue => Ok(AliasFlow {
            continues: states,
            ..AliasFlow::default()
        }),
        HirStmt::LocalDecl(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Close(_) => Ok(AliasFlow::fallthrough(evaluate_leaf_stmt(
            stmt, local, param, states,
        )?)),
    }
}

fn validate_while_alias(
    body: &HirBlock,
    condition: &HirExpr,
    local: LocalId,
    param: ParamId,
    incoming: AliasStates,
    safety: HirExprSafety,
) -> Result<AliasFlow, AliasFlowError> {
    let truthiness = expr_truthiness(condition, safety);
    let mut entries = incoming.clone();
    let mut break_exits = AliasStates::default();
    loop {
        let condition_states = evaluate_expr(condition, local, param, entries.clone())?;
        let body_flow = if truthiness == Some(false) {
            AliasFlow::default()
        } else {
            validate_alias_flow(&body.stmts, local, param, condition_states.clone(), safety)?
        };
        let next_entries = incoming
            .clone()
            .union(body_flow.fallthrough)
            .union(body_flow.continues);
        let next_break_exits = break_exits.clone().union(body_flow.breaks);
        if next_entries == entries && next_break_exits == break_exits {
            let normal_exits = if truthiness == Some(true) {
                AliasStates::default()
            } else {
                condition_states
            };
            return Ok(AliasFlow::fallthrough(normal_exits.union(break_exits)));
        }
        entries = next_entries;
        break_exits = next_break_exits;
    }
}

fn validate_repeat_alias(
    body: &HirBlock,
    condition: &HirExpr,
    local: LocalId,
    param: ParamId,
    incoming: AliasStates,
    safety: HirExprSafety,
) -> Result<AliasFlow, AliasFlowError> {
    let truthiness = expr_truthiness(condition, safety);
    let mut entries = incoming.clone();
    let mut break_exits = AliasStates::default();
    loop {
        let body_flow = validate_alias_flow(&body.stmts, local, param, entries.clone(), safety)?;
        let condition_states = evaluate_expr(
            condition,
            local,
            param,
            body_flow.fallthrough.union(body_flow.continues),
        )?;
        let back_edges = if truthiness == Some(true) {
            AliasStates::default()
        } else {
            condition_states.clone()
        };
        let next_entries = incoming.clone().union(back_edges);
        let next_break_exits = break_exits.clone().union(body_flow.breaks);
        if next_entries == entries && next_break_exits == break_exits {
            let normal_exits = if truthiness == Some(false) {
                AliasStates::default()
            } else {
                condition_states
            };
            return Ok(AliasFlow::fallthrough(normal_exits.union(break_exits)));
        }
        entries = next_entries;
        break_exits = next_break_exits;
    }
}

fn validate_zero_or_more_alias(
    body: &HirBlock,
    local: LocalId,
    param: ParamId,
    zero_exit: AliasStates,
    initial_body_entry: AliasStates,
    opaque_each_iteration: bool,
    safety: HirExprSafety,
) -> Result<AliasFlow, AliasFlowError> {
    let mut entries = initial_body_entry.clone();
    let mut break_exits = AliasStates::default();
    loop {
        let body_flow = validate_alias_flow(&body.stmts, local, param, entries.clone(), safety)?;
        let iteration_exits = body_flow.fallthrough.union(body_flow.continues);
        let callback_exits = if opaque_each_iteration {
            evaluate_opaque_callback(local, param, iteration_exits)?
        } else {
            iteration_exits
        };
        let next_entries = initial_body_entry.clone().union(callback_exits.clone());
        let next_break_exits = break_exits.clone().union(body_flow.breaks);
        if next_entries == entries && next_break_exits == break_exits {
            return Ok(AliasFlow::fallthrough(
                zero_exit.union(callback_exits).union(break_exits),
            ));
        }
        entries = next_entries;
        break_exits = next_break_exits;
    }
}

fn union_alias_flows(left: AliasFlow, right: AliasFlow) -> AliasFlow {
    AliasFlow {
        fallthrough: left.fallthrough.union(right.fallthrough),
        breaks: left.breaks.union(right.breaks),
        continues: left.continues.union(right.continues),
    }
}

fn evaluate_expr(
    expr: &HirExpr,
    local: LocalId,
    param: ParamId,
    states: AliasStates,
) -> Result<AliasStates, AliasFlowError> {
    let mut facts = AliasEvaluationFacts::new(local, param);
    visit::visit_expr(expr, &mut facts);
    apply_evaluation_facts(facts, false, false, states)
}

fn evaluate_opaque_callback(
    local: LocalId,
    param: ParamId,
    states: AliasStates,
) -> Result<AliasStates, AliasFlowError> {
    let mut facts = AliasEvaluationFacts::new(local, param);
    facts.has_opaque_callback = true;
    apply_evaluation_facts(facts, false, false, states)
}

fn evaluate_leaf_stmt(
    stmt: &HirStmt,
    local: LocalId,
    param: ParamId,
    states: AliasStates,
) -> Result<AliasStates, AliasFlowError> {
    let mut facts = AliasEvaluationFacts::new(local, param);
    visit::visit_stmts(std::slice::from_ref(stmt), &mut facts);
    facts.has_opaque_callback |= matches!(stmt, HirStmt::Close(_));
    let writes_local = stmt_writes_local(stmt, local);
    let writes_param = stmt_writes_param(stmt, param);
    apply_evaluation_facts(facts, writes_local, writes_param, states)
}

fn apply_evaluation_facts(
    facts: AliasEvaluationFacts,
    writes_local: bool,
    writes_param: bool,
    states: AliasStates,
) -> Result<AliasStates, AliasFlowError> {
    if writes_local && writes_param {
        return Err(AliasFlowError::ValueFlow);
    }
    let mut after_callbacks = BTreeSet::new();
    for mut state in states.0 {
        if (state.divergence == Divergence::LocalWritten && facts.reads_param)
            || (state.divergence == Divergence::ParamWritten && facts.reads_local)
        {
            return Err(AliasFlowError::ValueFlow);
        }
        state.local_reference_exposed |= facts.reference_captures_local;
        state.param_reference_exposed |= facts.reference_captures_param;
        if facts.has_opaque_callback
            && ((state.divergence == Divergence::LocalWritten && state.param_reference_exposed)
                || (state.divergence == Divergence::ParamWritten && state.local_reference_exposed))
        {
            return Err(AliasFlowError::ValueFlow);
        }
        after_callbacks.insert(state);
        if facts.has_opaque_callback {
            if state.local_reference_exposed {
                after_callbacks.insert(AliasState {
                    divergence: Divergence::LocalWritten,
                    ..state
                });
            }
            if state.param_reference_exposed {
                after_callbacks.insert(AliasState {
                    divergence: Divergence::ParamWritten,
                    ..state
                });
            }
        }
    }

    let mut next = BTreeSet::new();
    for mut state in after_callbacks {
        if writes_local {
            if state.param_reference_exposed {
                return Err(AliasFlowError::Capture);
            }
            state.divergence = Divergence::LocalWritten;
        } else if writes_param {
            if state.local_reference_exposed {
                return Err(AliasFlowError::Capture);
            }
            state.divergence = Divergence::ParamWritten;
        }
        next.insert(state);
    }
    Ok(AliasStates(next))
}

struct AliasEvaluationFacts {
    local: LocalId,
    param: ParamId,
    reads_local: bool,
    reads_param: bool,
    reference_captures_local: bool,
    reference_captures_param: bool,
    has_opaque_callback: bool,
}

impl AliasEvaluationFacts {
    fn new(local: LocalId, param: ParamId) -> Self {
        Self {
            local,
            param,
            reads_local: false,
            reads_param: false,
            reference_captures_local: false,
            reference_captures_param: false,
            has_opaque_callback: false,
        }
    }
}

impl HirVisitor for AliasEvaluationFacts {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.has_opaque_callback |= matches!(stmt, HirStmt::GlobalDecl(_));
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::LocalRef(local) if *local == self.local => self.reads_local = true,
            HirExpr::ParamRef(param) if *param == self.param => self.reads_param = true,
            HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Unary(_)
            | HirExpr::Binary(_)
            | HirExpr::Call(_) => self.has_opaque_callback = true,
            HirExpr::Closure(closure) => {
                for capture in &closure.captures {
                    if capture.mode != HirCaptureMode::ByReference {
                        continue;
                    }
                    self.reference_captures_local |=
                        expr_mentions_local(&capture.value, self.local);
                    self.reference_captures_param |=
                        expr_mentions_param(&capture.value, self.param);
                }
            }
            _ => {}
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.has_opaque_callback |=
            matches!(lvalue, HirLValue::Global(_) | HirLValue::TableAccess(_));
    }

    fn visit_call(&mut self, _call: &crate::hir::common::HirCallExpr) {
        self.has_opaque_callback = true;
    }
}

fn stmt_writes_local(stmt: &HirStmt, local: LocalId) -> bool {
    let mut collector = LocalWriteCollector {
        local,
        written: false,
    };
    visit::visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.written
}

struct LocalWriteCollector {
    local: LocalId,
    written: bool,
}

fn stmt_writes_param(stmt: &HirStmt, param: ParamId) -> bool {
    let mut collector = ParamWriteCollector {
        param,
        written: false,
    };
    visit::visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.written
}

struct ParamWriteCollector {
    param: ParamId,
    written: bool,
}

impl HirVisitor for ParamWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.written |= matches!(lvalue, HirLValue::Param(param) if *param == self.param);
    }
}

impl HirVisitor for LocalWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.written |= matches!(lvalue, HirLValue::Local(local) if *local == self.local);
    }
}

fn expr_mentions_param(expr: &HirExpr, param: ParamId) -> bool {
    let mut collector = ParamReadCollector { param, read: false };
    visit::visit_expr(expr, &mut collector);
    collector.read
}

struct ParamReadCollector {
    param: ParamId,
    read: bool,
}

impl HirVisitor for ParamReadCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.read |= matches!(expr, HirExpr::ParamRef(param) if *param == self.param);
    }
}

struct LocalToParamRewrite {
    local: LocalId,
    param: ParamId,
}

impl HirRewritePass for LocalToParamRewrite {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        if matches!(expr, HirExpr::LocalRef(local) if *local == self.local) {
            *expr = HirExpr::ParamRef(self.param);
            return true;
        }
        false
    }

    fn rewrite_lvalue(&mut self, lvalue: &mut HirLValue) -> bool {
        if matches!(lvalue, HirLValue::Local(local) if *local == self.local) {
            *lvalue = HirLValue::Param(self.param);
            return true;
        }
        false
    }
}
