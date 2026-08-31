//! 相邻 seed/carried local handoff 收敛。
//!
//! 这个规则只处理结构化后暴露出的窄形状：
//! `local state = init; local next; ... next = state ...`。主模块负责调度不同
//! handoff owner；这里只在 seed 不再可观察、carried 没有闭包捕获、且后续写回形状
//! 明确时，把 carried 的使用点认回 seed。相邻 owner 只接受单目标 `carried = seed`
//! 复制；`seed = carried` 尤其是多目标并行写回会保守保留两个 binding。
//! capture/TBC direct 身份及 raw-home may-alias 由父模块统一保护，不在这里改写资源 cell。
//! 接受相邻 local 合并前，本 owner 还在结构化 HIR 上计算 `Unwritten/Written` 路径事实：
//! 分支合并可能状态，循环通过有限状态不动点消费自然/continue 回边和 break 出口，赋值按
//! “先读 RHS/左值地址、再同时写 targets”转移。goto/label 的额外入口仍属于 CFG dominance
//! owner，本文件不会从线性位置猜测它们是否绕过写入。
//!
//! - 接受：`local s=1; local c; c=s; print(c)` -> `local s=1; print(s)`
//! - 拒绝：`local s=1; local c; print(c); c=s`，因为 nil 读取不受 handoff 写支配

use std::collections::BTreeMap;

use crate::hir::common::{HirAssign, HirBlock, HirCallExpr, HirExpr, HirLValue, HirStmt, LocalId};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::expr_facts::expr_truthiness;
use super::super::local_shapes::{
    empty_single_local_decl_binding, initialized_single_local_decl_binding,
};
use super::super::mention::{expr_mentions_local, stmt_captures_local, stmts_mention_local};
use super::super::walk::rewrite_stmts;
use super::HandoffIdentityFacts;
use super::binding::{
    BindingClassRewritePass, BindingProtection, CarryBinding, bindings_share_exact_home_slot,
};
use super::prune::{
    collect_prunable_bindings, prune_empty_assign_stmts, prune_redundant_self_assigns_in_stmts,
};
use super::reads::{collect_binding_mentions_by_stmt, collect_binding_mentions_in_expr};

pub(super) fn try_collapse_guarded_local_update(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    captured_bindings: &std::collections::BTreeSet<CarryBinding>,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
) -> bool {
    let Some((next, value)) = block.stmts.get(index).and_then(initialized_local) else {
        return false;
    };
    let next_binding = CarryBinding::Local(next);
    let Some(HirStmt::If(if_stmt)) = block.stmts.get(index + 1) else {
        return false;
    };
    if if_stmt.cond != HirExpr::LocalRef(next) {
        return false;
    }
    let Some(state) = exact_binding_copy(&if_stmt.then_block.stmts, next) else {
        return false;
    };
    // 候选拒绝[ProofIncomplete]：temp state 尚未接入 local/param 的可用性与声明 owner 证明。
    // 候选拒绝[SemanticBarrier:Lifetime]：外层仍活跃的 state 或 next 被合并后会让 false-return 路径提前覆盖旧 state。
    // 候选拒绝[SemanticBarrier:Capture]：捕获任一 binding 时，false path 上 closure 可区分“只写 next”和“已写 state”。
    // 候选拒绝[LayerBoundary]：debug/TBC/for/raw-home identity 由 identity facts owner 保留。
    // 候选拒绝[SemanticBarrier:Scope]：initializer 自读 next 时，删除其 local 声明会把读取改指另一 lexical identity。
    if !matches!(state, CarryBinding::Param(_) | CarryBinding::Local(_))
        || state == next_binding
        || matches!(state, CarryBinding::Local(_)) && outer_bindings.contains(&state)
        || captured_bindings.contains(&state)
        || captured_bindings.contains(&next_binding)
        || !identity_facts.binding_merge_preserves_identity(next_binding, state, promotion_facts)
        || collect_binding_mentions_in_expr(value).contains(&next_binding)
    {
        return false;
    }
    // 候选拒绝[SemanticBarrier:ControlFlow]：无 else 时 next=false 会继续执行后缀；提前写 state 会令后缀观察 false 而非旧 state。
    let Some(else_block) = if_stmt.else_block.as_ref() else {
        return false;
    };
    // 候选拒绝[SemanticBarrier:Lifetime]：return/后缀仍读 state 或 next 时，可观察 false-path 上 state 是否被提前覆盖或 next 是否被删除。
    if !block_is_return_shell(else_block)
        || collect_binding_mentions_by_stmt(&else_block.stmts)
            .iter()
            .flatten()
            .any(|binding| *binding == state || *binding == next_binding)
        || collect_binding_mentions_by_stmt(&block.stmts[index + 2..])
            .iter()
            .any(|mentions| mentions.contains(&next_binding))
    {
        return false;
    }

    let values = match &mut block.stmts[index] {
        HirStmt::LocalDecl(local_decl) => std::mem::take(&mut local_decl.values),
        _ => return false,
    };
    block.stmts[index] = HirStmt::Assign(Box::new(HirAssign {
        targets: vec![binding_lvalue(state)],
        values,
    }));

    let mut rewrites = BTreeMap::new();
    rewrites.insert(next_binding, state);
    rewrite_stmts(
        &mut block.stmts[index + 1..index + 2],
        &mut BindingClassRewritePass {
            rewrites,
            promotion_facts,
        },
    );
    prune_redundant_self_assigns_in_stmts(
        &mut block.stmts[index + 1..index + 2],
        collect_prunable_bindings([state]),
    );
    true
}

/// 只接受结构本身保证离开当前函数的单节点壳。
///
/// `break`、`continue` 和 `goto` 虽然终结当前 block，仍可能进入函数内 continuation，
/// 因而不能证明 guarded update 的 false path 不再观察旧 state。
fn block_is_return_shell(block: &HirBlock) -> bool {
    matches!(block.stmts.as_slice(), [stmt] if stmt_is_return_shell(stmt))
}

fn stmt_is_return_shell(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Return(_) => true,
        HirStmt::Block(block) => block_is_return_shell(block),
        HirStmt::If(if_stmt) => if_stmt.else_block.as_ref().is_some_and(|else_block| {
            block_is_return_shell(&if_stmt.then_block) && block_is_return_shell(else_block)
        }),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

pub(super) fn try_collapse_adjacent_local_seed_handoff(
    block: &mut HirBlock,
    index: usize,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
    safety: HirExprSafety,
) -> bool {
    let Some(seed) = initialized_single_local_decl_binding(&block.stmts[index]) else {
        return false;
    };
    let Some(carried) = block
        .stmts
        .get(index + 1)
        .and_then(empty_single_local_decl_binding)
    else {
        return false;
    };

    let tail = &block.stmts[index + 2..];
    // 候选拒绝[SemanticBarrier:Lifetime]：异槽/compaction 时合并两个 root 会改变弱表、finalizer 或 cleanup 可见的存活期。
    // 候选拒绝[LayerBoundary]：debug/capture/TBC/for identity 由 proto identity owner 保留。
    // 候选拒绝[SemanticBarrier:Lifetime]：tail 仍读取旧 seed 时，carried 写入改名为 seed 会让该读取看到新 epoch。
    if promotion_facts.compacts_home_slots()
        || !bindings_share_exact_home_slot(
            CarryBinding::Local(carried),
            CarryBinding::Local(seed),
            promotion_facts,
        )
        || !identity_facts.binding_merge_preserves_identity(
            CarryBinding::Local(carried),
            CarryBinding::Local(seed),
            promotion_facts,
        )
        || tail.is_empty()
        || !stmts_mention_local(tail, carried)
        || tail.iter().any(|stmt| {
            stmt_captures_local(stmt, seed)
                || stmt_captures_local(stmt, carried)
                || !stmt_allows_seed_to_absorb_carried(stmt, seed, carried)
        })
    {
        return false;
    }

    match carried_write_dominance(tail, carried, safety) {
        CarriedWriteDominance::Proven => {}
        CarriedWriteDominance::ReadBeforeWrite => {
            // 候选拒绝[SemanticBarrier:Lifetime]：carried 在 handoff 写前可读时，改名会把 nil/旧 epoch 改成 seed；`local s=1; local c; print(c); c=s` 可观察 nil 变为 1。
            return false;
        }
        CarriedWriteDominance::UnstructuredControl => {
            // 候选拒绝[LayerBoundary]：goto/label 的额外入口需要 CFG dominance owner 证明不会绕过 handoff 写。
            return false;
        }
    }

    let mut tail = block.stmts.split_off(index + 2);
    rewrite_carried_local_in_stmts(&mut tail, carried, seed, promotion_facts);
    block.stmts.append(&mut tail);
    block.stmts.remove(index + 1);
    prune_empty_assign_stmts(block);
    true
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum CarriedWriteDominance {
    Proven,
    ReadBeforeWrite,
    UnstructuredControl,
}

#[derive(Clone, Copy, Eq, PartialEq)]
struct WriteStates(u8);

impl WriteStates {
    const EMPTY: Self = Self(0);
    const UNWRITTEN: Self = Self(1);
    const WRITTEN: Self = Self(2);

    const fn contains_unwritten(self) -> bool {
        self.0 & Self::UNWRITTEN.0 != 0
    }

    const fn is_empty(self) -> bool {
        self.0 == 0
    }

    const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    const fn after_write(self) -> Self {
        if self.is_empty() {
            Self::EMPTY
        } else {
            Self::WRITTEN
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
struct DominanceFlow {
    fallthrough: WriteStates,
    breaks: WriteStates,
    continues: WriteStates,
}

impl DominanceFlow {
    const fn fallthrough(states: WriteStates) -> Self {
        Self {
            fallthrough: states,
            breaks: WriteStates::EMPTY,
            continues: WriteStates::EMPTY,
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum DominanceError {
    ReadBeforeWrite,
    UnstructuredControl,
}

fn carried_write_dominance(
    stmts: &[HirStmt],
    carried: LocalId,
    safety: HirExprSafety,
) -> CarriedWriteDominance {
    if stmts.iter().any(stmt_has_unstructured_control) {
        return CarriedWriteDominance::UnstructuredControl;
    }
    match analyze_dominance_stmts(stmts, WriteStates::UNWRITTEN, carried, safety) {
        Ok(_) => CarriedWriteDominance::Proven,
        Err(DominanceError::ReadBeforeWrite) => CarriedWriteDominance::ReadBeforeWrite,
        Err(DominanceError::UnstructuredControl) => CarriedWriteDominance::UnstructuredControl,
    }
}

fn analyze_dominance_stmts(
    stmts: &[HirStmt],
    mut states: WriteStates,
    carried: LocalId,
    safety: HirExprSafety,
) -> Result<DominanceFlow, DominanceError> {
    let mut breaks = WriteStates::EMPTY;
    let mut continues = WriteStates::EMPTY;
    for stmt in stmts {
        if states.is_empty() {
            break;
        }
        let flow = analyze_dominance_stmt(stmt, states, carried, safety)?;
        states = flow.fallthrough;
        breaks = breaks.union(flow.breaks);
        continues = continues.union(flow.continues);
    }
    Ok(DominanceFlow {
        fallthrough: states,
        breaks,
        continues,
    })
}

fn analyze_dominance_stmt(
    stmt: &HirStmt,
    states: WriteStates,
    carried: LocalId,
    safety: HirExprSafety,
) -> Result<DominanceFlow, DominanceError> {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            ensure_pack_is_initialized(&local_decl.values, states, carried)?;
            Ok(DominanceFlow::fallthrough(states))
        }
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                ensure_lvalue_address_is_initialized(target, states, carried)?;
            }
            ensure_pack_is_initialized(&assign.values, states, carried)?;
            let writes_carried = assign
                .targets
                .iter()
                .any(|target| matches!(target, HirLValue::Local(local) if *local == carried));
            Ok(DominanceFlow::fallthrough(if writes_carried {
                states.after_write()
            } else {
                states
            }))
        }
        HirStmt::TableSetList(set_list) => {
            ensure_expr_is_initialized(&set_list.base, states, carried)?;
            ensure_pack_is_initialized(&set_list.values, states, carried)?;
            Ok(DominanceFlow::fallthrough(states))
        }
        HirStmt::ErrNil(err_nil) => {
            ensure_expr_is_initialized(&err_nil.value, states, carried)?;
            Ok(DominanceFlow::fallthrough(states))
        }
        HirStmt::ToBeClosed(to_be_closed) => {
            ensure_expr_is_initialized(&to_be_closed.value, states, carried)?;
            Ok(DominanceFlow::fallthrough(states))
        }
        HirStmt::CallStmt(call_stmt) => {
            ensure_call_is_initialized(&call_stmt.call, states, carried)?;
            Ok(DominanceFlow::fallthrough(states))
        }
        HirStmt::Return(return_stmt) => {
            ensure_pack_is_initialized(&return_stmt.values, states, carried)?;
            Ok(DominanceFlow::fallthrough(WriteStates::EMPTY))
        }
        HirStmt::If(if_stmt) => {
            ensure_expr_is_initialized(&if_stmt.cond, states, carried)?;
            let then_flow = if expr_truthiness(&if_stmt.cond, safety) == Some(false) {
                DominanceFlow::fallthrough(WriteStates::EMPTY)
            } else {
                analyze_dominance_stmts(&if_stmt.then_block.stmts, states, carried, safety)?
            };
            let else_flow = if expr_truthiness(&if_stmt.cond, safety) == Some(true) {
                DominanceFlow::fallthrough(WriteStates::EMPTY)
            } else if let Some(else_block) = &if_stmt.else_block {
                analyze_dominance_stmts(&else_block.stmts, states, carried, safety)?
            } else {
                DominanceFlow::fallthrough(states)
            };
            Ok(union_dominance_flows(then_flow, else_flow))
        }
        HirStmt::While(while_stmt) => {
            analyze_while_dominance(&while_stmt.body, &while_stmt.cond, states, carried, safety)
        }
        HirStmt::Repeat(repeat_stmt) => analyze_repeat_dominance(
            &repeat_stmt.body,
            &repeat_stmt.cond,
            states,
            carried,
            safety,
        ),
        HirStmt::NumericFor(numeric_for) => {
            ensure_expr_is_initialized(&numeric_for.start, states, carried)?;
            ensure_expr_is_initialized(&numeric_for.limit, states, carried)?;
            ensure_expr_is_initialized(&numeric_for.step, states, carried)?;
            analyze_zero_or_more_dominance(&numeric_for.body, states, carried, safety)
        }
        HirStmt::GenericFor(generic_for) => {
            ensure_pack_is_initialized(&generic_for.iterator, states, carried)?;
            analyze_zero_or_more_dominance(&generic_for.body, states, carried, safety)
        }
        HirStmt::Block(block) => analyze_dominance_stmts(&block.stmts, states, carried, safety),
        HirStmt::Break => Ok(DominanceFlow {
            fallthrough: WriteStates::EMPTY,
            breaks: states,
            continues: WriteStates::EMPTY,
        }),
        HirStmt::Continue => Ok(DominanceFlow {
            fallthrough: WriteStates::EMPTY,
            breaks: WriteStates::EMPTY,
            continues: states,
        }),
        HirStmt::Goto(_) | HirStmt::Label(_) => Err(DominanceError::UnstructuredControl),
        HirStmt::Close(_) => Ok(DominanceFlow::fallthrough(states)),
    }
}

fn analyze_while_dominance(
    body: &HirBlock,
    condition: &HirExpr,
    incoming: WriteStates,
    carried: LocalId,
    safety: HirExprSafety,
) -> Result<DominanceFlow, DominanceError> {
    let truthiness = expr_truthiness(condition, safety);
    let mut entries = incoming;
    let mut break_exits = WriteStates::EMPTY;
    loop {
        ensure_expr_is_initialized(condition, entries, carried)?;
        let body_flow = if truthiness == Some(false) {
            DominanceFlow::fallthrough(WriteStates::EMPTY)
        } else {
            analyze_dominance_stmts(&body.stmts, entries, carried, safety)?
        };
        let next_entries = incoming
            .union(body_flow.fallthrough)
            .union(body_flow.continues);
        let next_break_exits = break_exits.union(body_flow.breaks);
        if next_entries == entries && next_break_exits == break_exits {
            let normal_exits = if truthiness == Some(true) {
                WriteStates::EMPTY
            } else {
                entries
            };
            return Ok(DominanceFlow::fallthrough(normal_exits.union(break_exits)));
        }
        entries = next_entries;
        break_exits = next_break_exits;
    }
}

fn analyze_repeat_dominance(
    body: &HirBlock,
    condition: &HirExpr,
    incoming: WriteStates,
    carried: LocalId,
    safety: HirExprSafety,
) -> Result<DominanceFlow, DominanceError> {
    let truthiness = expr_truthiness(condition, safety);
    let mut entries = incoming;
    let mut break_exits = WriteStates::EMPTY;
    loop {
        let body_flow = analyze_dominance_stmts(&body.stmts, entries, carried, safety)?;
        let condition_states = body_flow.fallthrough.union(body_flow.continues);
        ensure_expr_is_initialized(condition, condition_states, carried)?;
        let back_edges = if truthiness == Some(true) {
            WriteStates::EMPTY
        } else {
            condition_states
        };
        let next_entries = incoming.union(back_edges);
        let next_break_exits = break_exits.union(body_flow.breaks);
        if next_entries == entries && next_break_exits == break_exits {
            let normal_exits = if truthiness == Some(false) {
                WriteStates::EMPTY
            } else {
                condition_states
            };
            return Ok(DominanceFlow::fallthrough(normal_exits.union(break_exits)));
        }
        entries = next_entries;
        break_exits = next_break_exits;
    }
}

fn analyze_zero_or_more_dominance(
    body: &HirBlock,
    incoming: WriteStates,
    carried: LocalId,
    safety: HirExprSafety,
) -> Result<DominanceFlow, DominanceError> {
    let mut entries = incoming;
    let mut break_exits = WriteStates::EMPTY;
    loop {
        let body_flow = analyze_dominance_stmts(&body.stmts, entries, carried, safety)?;
        let next_entries = incoming
            .union(body_flow.fallthrough)
            .union(body_flow.continues);
        let next_break_exits = break_exits.union(body_flow.breaks);
        if next_entries == entries && next_break_exits == break_exits {
            return Ok(DominanceFlow::fallthrough(entries.union(break_exits)));
        }
        entries = next_entries;
        break_exits = next_break_exits;
    }
}

fn union_dominance_flows(left: DominanceFlow, right: DominanceFlow) -> DominanceFlow {
    DominanceFlow {
        fallthrough: left.fallthrough.union(right.fallthrough),
        breaks: left.breaks.union(right.breaks),
        continues: left.continues.union(right.continues),
    }
}

fn ensure_pack_is_initialized(
    pack: &crate::hir::common::HirValuePack,
    states: WriteStates,
    carried: LocalId,
) -> Result<(), DominanceError> {
    for expr in pack {
        ensure_expr_is_initialized(expr, states, carried)?;
    }
    Ok(())
}

fn ensure_call_is_initialized(
    call: &HirCallExpr,
    states: WriteStates,
    carried: LocalId,
) -> Result<(), DominanceError> {
    ensure_expr_is_initialized(&call.callee, states, carried)?;
    ensure_pack_is_initialized(&call.args, states, carried)
}

fn ensure_lvalue_address_is_initialized(
    lvalue: &HirLValue,
    states: WriteStates,
    carried: LocalId,
) -> Result<(), DominanceError> {
    let HirLValue::TableAccess(access) = lvalue else {
        return Ok(());
    };
    ensure_expr_is_initialized(&access.base, states, carried)?;
    ensure_expr_is_initialized(&access.key, states, carried)
}

fn ensure_expr_is_initialized(
    expr: &HirExpr,
    states: WriteStates,
    carried: LocalId,
) -> Result<(), DominanceError> {
    if states.contains_unwritten() && expr_mentions_local(expr, carried) {
        Err(DominanceError::ReadBeforeWrite)
    } else {
        Ok(())
    }
}

fn stmt_has_unstructured_control(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Goto(_) | HirStmt::Label(_) => true,
        HirStmt::If(if_stmt) => {
            if_stmt
                .then_block
                .stmts
                .iter()
                .any(stmt_has_unstructured_control)
                || if_stmt.else_block.as_ref().is_some_and(|else_block| {
                    else_block.stmts.iter().any(stmt_has_unstructured_control)
                })
        }
        HirStmt::While(while_stmt) => while_stmt
            .body
            .stmts
            .iter()
            .any(stmt_has_unstructured_control),
        HirStmt::Repeat(repeat_stmt) => repeat_stmt
            .body
            .stmts
            .iter()
            .any(stmt_has_unstructured_control),
        HirStmt::NumericFor(numeric_for) => numeric_for
            .body
            .stmts
            .iter()
            .any(stmt_has_unstructured_control),
        HirStmt::GenericFor(generic_for) => generic_for
            .body
            .stmts
            .iter()
            .any(stmt_has_unstructured_control),
        HirStmt::Block(block) => block.stmts.iter().any(stmt_has_unstructured_control),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue => false,
    }
}

fn rewrite_carried_local_in_stmts(
    stmts: &mut [HirStmt],
    carried: LocalId,
    seed: LocalId,
    promotion_facts: &mut ProtoPromotionFacts,
) {
    let mut rewrites = BTreeMap::new();
    rewrites.insert(CarryBinding::Local(carried), CarryBinding::Local(seed));
    let mut pass = BindingClassRewritePass {
        rewrites,
        promotion_facts,
    };
    rewrite_stmts(stmts, &mut pass);
    prune_redundant_self_assigns_in_stmts(
        stmts,
        collect_prunable_bindings([CarryBinding::Local(seed)]),
    );
}

fn stmt_allows_seed_to_absorb_carried(stmt: &HirStmt, seed: LocalId, carried: LocalId) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            local_decl
                .bindings
                .iter()
                .all(|binding| *binding != seed && *binding != carried)
                && local_decl
                    .values
                    .iter()
                    .all(|value| !expr_mentions_local(value, seed))
        }
        HirStmt::Assign(assign) => {
            if is_exact_local_copy_assign(assign, carried, seed) {
                true
            } else {
                !assign_targets_local(assign, seed)
                    && assign
                        .targets
                        .iter()
                        .all(|target| !lvalue_mentions_local(target, seed))
                    && assign
                        .values
                        .iter()
                        .all(|value| !expr_mentions_local(value, seed))
            }
        }
        HirStmt::TableSetList(set_list) => {
            !expr_mentions_local(&set_list.base, seed)
                && set_list
                    .values
                    .iter()
                    .all(|value| !expr_mentions_local(value, seed))
        }
        HirStmt::ErrNil(err_nil) => !expr_mentions_local(&err_nil.value, seed),
        HirStmt::ToBeClosed(to_be_closed) => !expr_mentions_local(&to_be_closed.value, seed),
        HirStmt::CallStmt(call_stmt) => !call_mentions_local(&call_stmt.call, seed),
        HirStmt::Return(ret) => ret
            .values
            .iter()
            .all(|value| !expr_mentions_local(value, seed)),
        HirStmt::If(if_stmt) => {
            !expr_mentions_local(&if_stmt.cond, seed)
                && stmts_allow_seed_to_absorb_carried(&if_stmt.then_block.stmts, seed, carried)
                && if_stmt.else_block.as_ref().is_none_or(|else_block| {
                    stmts_allow_seed_to_absorb_carried(&else_block.stmts, seed, carried)
                })
        }
        HirStmt::While(while_stmt) => {
            !expr_mentions_local(&while_stmt.cond, seed)
                && stmts_allow_seed_to_absorb_carried(&while_stmt.body.stmts, seed, carried)
        }
        HirStmt::Repeat(repeat_stmt) => {
            stmts_allow_seed_to_absorb_carried(&repeat_stmt.body.stmts, seed, carried)
                && !expr_mentions_local(&repeat_stmt.cond, seed)
        }
        HirStmt::NumericFor(numeric_for) => {
            numeric_for.binding != seed
                && numeric_for.binding != carried
                && !expr_mentions_local(&numeric_for.start, seed)
                && !expr_mentions_local(&numeric_for.limit, seed)
                && !expr_mentions_local(&numeric_for.step, seed)
                && stmts_allow_seed_to_absorb_carried(&numeric_for.body.stmts, seed, carried)
        }
        HirStmt::GenericFor(generic_for) => {
            !generic_for
                .bindings
                .iter()
                .any(|binding| *binding == seed || *binding == carried)
                && generic_for
                    .iterator
                    .iter()
                    .all(|value| !expr_mentions_local(value, seed))
                && stmts_allow_seed_to_absorb_carried(&generic_for.body.stmts, seed, carried)
        }
        HirStmt::Block(block) => stmts_allow_seed_to_absorb_carried(&block.stmts, seed, carried),
        HirStmt::Close(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => true,
    }
}

fn stmts_allow_seed_to_absorb_carried(stmts: &[HirStmt], seed: LocalId, carried: LocalId) -> bool {
    stmts
        .iter()
        .all(|stmt| stmt_allows_seed_to_absorb_carried(stmt, seed, carried))
}

fn is_exact_local_copy_assign(assign: &HirAssign, carried: LocalId, seed: LocalId) -> bool {
    let [HirLValue::Local(target)] = assign.targets.as_slice() else {
        return false;
    };
    let [HirExpr::LocalRef(value)] = assign.values.fixed.as_slice() else {
        return false;
    };
    if assign.values.tail.is_some() {
        return false;
    }
    *target == carried && *value == seed
}

fn assign_targets_local(assign: &HirAssign, local: LocalId) -> bool {
    assign
        .targets
        .iter()
        .any(|target| matches!(target, HirLValue::Local(target) if *target == local))
}

fn lvalue_mentions_local(lvalue: &HirLValue, local: LocalId) -> bool {
    match lvalue {
        HirLValue::Local(target) => *target == local,
        HirLValue::TableAccess(access) => {
            expr_mentions_local(&access.base, local) || expr_mentions_local(&access.key, local)
        }
        HirLValue::Param(_) | HirLValue::Temp(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => {
            false
        }
    }
}

fn call_mentions_local(call: &HirCallExpr, local: LocalId) -> bool {
    expr_mentions_local(&call.callee, local)
        || call.args.iter().any(|arg| expr_mentions_local(arg, local))
}

fn initialized_local(stmt: &HirStmt) -> Option<(LocalId, &HirExpr)> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.fixed.as_slice() else {
        return None;
    };
    local_decl
        .values
        .tail
        .is_none()
        .then_some((*binding, value))
}

fn exact_binding_copy(stmts: &[HirStmt], value: LocalId) -> Option<CarryBinding> {
    let [HirStmt::Assign(assign)] = stmts else {
        return None;
    };
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [HirExpr::LocalRef(source)] = assign.values.fixed.as_slice() else {
        return None;
    };
    (assign.values.tail.is_none() && *source == value)
        .then(|| super::binding::carry_binding_from_lvalue(target))
        .flatten()
}

fn binding_lvalue(binding: CarryBinding) -> HirLValue {
    match binding {
        CarryBinding::Param(param) => HirLValue::Param(param),
        CarryBinding::Local(local) => HirLValue::Local(local),
        CarryBinding::Temp(temp) => HirLValue::Temp(temp),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::common::{HirGoto, HirIf, HirLabelId, HirReturn, HirValuePack};

    fn empty_return() -> HirStmt {
        HirStmt::Return(Box::new(HirReturn {
            values: HirValuePack::default(),
        }))
    }

    fn block(stmt: HirStmt) -> HirBlock {
        HirBlock { stmts: vec![stmt] }
    }

    #[test]
    fn return_shell_accepts_nested_block_and_complete_if() {
        let nested_return = HirStmt::Block(Box::new(block(HirStmt::Block(Box::new(block(
            empty_return(),
        ))))));
        assert!(stmt_is_return_shell(&nested_return));

        let complete_if = HirStmt::If(Box::new(HirIf {
            cond: HirExpr::Boolean(true),
            then_block: block(empty_return()),
            else_block: Some(block(HirStmt::Block(Box::new(block(empty_return()))))),
        }));
        assert!(stmt_is_return_shell(&complete_if));
    }

    #[test]
    fn return_shell_rejects_function_local_control_and_prefixes() {
        let incomplete_if = HirStmt::If(Box::new(HirIf {
            cond: HirExpr::Boolean(true),
            then_block: block(empty_return()),
            else_block: None,
        }));
        let prefixed_return = HirStmt::Block(Box::new(HirBlock {
            stmts: vec![empty_return(), empty_return()],
        }));

        assert!(!stmt_is_return_shell(&HirStmt::Break));
        assert!(!stmt_is_return_shell(&HirStmt::Continue));
        assert!(!stmt_is_return_shell(&HirStmt::Goto(Box::new(HirGoto {
            target: HirLabelId(0),
        }))));
        assert!(!stmt_is_return_shell(&incomplete_if));
        assert!(!stmt_is_return_shell(&prefixed_return));
    }
}
