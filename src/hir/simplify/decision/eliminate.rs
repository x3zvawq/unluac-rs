//! 残余 `Decision` 线性化 pass 的 block / stmt 遍历入口。
//!
//! `Decision` 适合作为 HIR 内部恢复共享短路子图时的过渡表示，但不应该继续流到 AST。
//! 这个文件只负责按语句顺序遍历 block，并把表达式抽取、值物化和条件消除委托给
//! `eliminate_materialize.rs`；它不重新识别 Decision DAG。If/While 条件无法纯表达式化时，
//! 这里用短作用域物化 truthiness，确保原值根在 branch/body 前释放。
//!
//! 例子：
//! - 输入：`local x = Decision(...)`
//! - 输出：`local x; if ... then x = ... else x = ... end`

use std::mem;

use crate::hir::common::{
    HirBlock, HirCallStmt, HirErrNil, HirExpr, HirLValue, HirLocalDecl, HirProto, HirReturn,
    HirStmt, HirTableSetList, HirToBeClosed, LocalId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::walk::rewrite_nested_blocks_in_stmt;
use super::eliminate_materialize::{
    assign_target_supports_direct_materialization, eliminate_condition_expr, empty_local_decl,
    expr_contains_eliminable_decision, extract_assign, extract_call_expr, extract_generic_for,
    extract_numeric_for, extract_value_expr, extract_value_pack, extract_value_pack_with_leading,
    materialize_expr_for_assignment, materialize_expr_into_target,
};
use super::eliminate_state::EliminationState;

pub(crate) fn eliminate_remaining_decisions_in_proto(
    proto: &mut HirProto,
    promotion_facts: &mut ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    let first_new_local = proto.local_count;
    let changed = eliminate_block(&mut proto.body, &mut proto.local_count, safety);
    for local in (first_new_local..proto.local_count).map(LocalId) {
        promotion_facts.record_home_free_local(local);
    }
    proto.local_debug_hints.resize(proto.local_count, None);
    proto.local_debug_scopes.resize(proto.local_count, None);
    changed
}

fn eliminate_block(
    block: &mut HirBlock,
    next_local_index: &mut usize,
    safety: HirExprSafety,
) -> bool {
    let mut changed = false;
    let mut rewritten = Vec::with_capacity(block.stmts.len());
    let original = mem::take(&mut block.stmts);
    let mut state = EliminationState { next_local_index };

    for stmt in original {
        let (mut lowered, stmt_changed) = eliminate_stmt(stmt, &mut state, safety);
        changed |= stmt_changed;
        rewritten.append(&mut lowered);
    }

    block.stmts = rewritten;
    changed
}

fn eliminate_stmt(
    stmt: HirStmt,
    state: &mut EliminationState<'_>,
    safety: HirExprSafety,
) -> (Vec<HirStmt>, bool) {
    match stmt {
        HirStmt::LocalRootRelease(_) => (vec![stmt], false),
        HirStmt::LocalDecl(local_decl)
            if local_decl.bindings.len() == 1
                && local_decl.values.tail.is_none()
                && local_decl.values.fixed.len() == 1
                && expr_contains_eliminable_decision(&local_decl.values.fixed[0]) =>
        {
            let binding = local_decl.bindings[0];
            let value = local_decl
                .values
                .fixed
                .into_iter()
                .next()
                .expect("single-value local decl should stay non-empty");
            let mut stmts = vec![empty_local_decl(binding)];
            stmts.extend(materialize_expr_into_target(
                value,
                HirLValue::Local(binding),
                state,
                safety,
            ));
            (stmts, true)
        }
        HirStmt::Assign(assign)
            if assign.targets.len() == 1
                && assign.values.tail.is_none()
                && assign.values.fixed.len() == 1
                && assign_target_supports_direct_materialization(&assign.targets[0])
                && expr_contains_eliminable_decision(&assign.values.fixed[0]) =>
        {
            let target = assign
                .targets
                .into_iter()
                .next()
                .expect("single-target assign should stay non-empty");
            let value = assign
                .values
                .fixed
                .into_iter()
                .next()
                .expect("single-value assign should stay non-empty");
            (
                materialize_expr_for_assignment(value, target, state, safety),
                true,
            )
        }
        HirStmt::LocalDecl(local_decl) => {
            let initializer_merge_transaction = local_decl.initializer_merge_transaction;
            let (mut prefix, values, changed) =
                extract_value_pack(local_decl.values, state, safety);
            prefix.push(HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: local_decl.bindings,
                values,
                initializer_merge_transaction: (!changed)
                    .then_some(initializer_merge_transaction)
                    .flatten(),
            })));
            (prefix, changed)
        }
        HirStmt::GlobalDecl(global_decl) => {
            let (mut prefix, values, changed) =
                extract_value_pack(global_decl.values, state, safety);
            prefix.push(HirStmt::GlobalDecl(Box::new(crate::hir::HirGlobalDecl {
                names: global_decl.names,
                values,
            })));
            (prefix, changed)
        }
        HirStmt::Assign(assign) => {
            let (mut prefix, assign, changed) = extract_assign(*assign, state, safety);
            prefix.push(HirStmt::Assign(Box::new(assign)));
            (prefix, changed)
        }
        HirStmt::TableSetList(set_list) => {
            let (mut prefix, mut leading, values, changed) = extract_value_pack_with_leading(
                vec![set_list.base],
                set_list.values,
                state,
                safety,
            );
            let base = leading
                .pop()
                .expect("table-set-list extraction should preserve its base");
            prefix.push(HirStmt::TableSetList(Box::new(HirTableSetList {
                base,
                start_index: set_list.start_index,
                values,
            })));
            (prefix, changed)
        }
        HirStmt::ErrNil(err_nil) => {
            let (mut prefix, value, changed) = extract_value_expr(err_nil.value, state, safety);
            prefix.push(HirStmt::ErrNil(Box::new(HirErrNil {
                value,
                name: err_nil.name,
            })));
            (prefix, changed)
        }
        HirStmt::ToBeClosed(to_be_closed) => {
            let (mut prefix, value, changed) =
                extract_value_expr(to_be_closed.value, state, safety);
            prefix.push(HirStmt::ToBeClosed(Box::new(HirToBeClosed {
                origin: to_be_closed.origin,
                reg_index: to_be_closed.reg_index,
                value,
            })));
            (prefix, changed)
        }
        HirStmt::CallStmt(call_stmt) => {
            let (mut prefix, call, changed) = extract_call_expr(call_stmt.call, state, safety);
            prefix.push(HirStmt::CallStmt(Box::new(HirCallStmt { call })));
            (prefix, changed)
        }
        HirStmt::Return(ret) => {
            let (mut prefix, values, changed) = extract_value_pack(ret.values, state, safety);
            prefix.push(HirStmt::Return(Box::new(HirReturn {
                source_instr: ret.source_instr,
                values,
            })));
            (prefix, changed)
        }
        HirStmt::If(mut if_stmt) => {
            let mut cond_changed = eliminate_condition_expr(&mut if_stmt.cond, safety);
            if expr_contains_eliminable_decision(&if_stmt.cond) {
                let condition = mem::replace(&mut if_stmt.cond, HirExpr::Nil);
                let (flag, condition_scope) = materialize_condition_flag(condition, state, safety);
                if_stmt.cond = HirExpr::LocalRef(flag);
                cond_changed = true;
                let mut stmt = HirStmt::Block(Box::new(HirBlock {
                    stmts: vec![
                        empty_local_decl(flag),
                        condition_scope,
                        HirStmt::If(if_stmt),
                    ],
                }));
                let nested_changed = eliminate_nested_blocks_in_stmt(&mut stmt, state, safety);
                return (vec![stmt], cond_changed || nested_changed);
            }
            let mut stmt = HirStmt::If(if_stmt);
            let nested_changed = eliminate_nested_blocks_in_stmt(&mut stmt, state, safety);
            (vec![stmt], cond_changed || nested_changed)
        }
        HirStmt::While(mut while_stmt) => {
            let mut cond_changed = eliminate_condition_expr(&mut while_stmt.cond, safety);
            if expr_contains_eliminable_decision(&while_stmt.cond) {
                let condition = mem::replace(&mut while_stmt.cond, HirExpr::Boolean(true));
                let (flag, condition_scope) = materialize_condition_flag(condition, state, safety);
                let exit_guard = HirStmt::If(Box::new(crate::hir::common::HirIf {
                    cond: HirExpr::LocalRef(flag).negate(),
                    then_block: HirBlock {
                        stmts: vec![HirStmt::Break],
                    },
                    else_block: None,
                }));
                while_stmt.body.stmts.insert(
                    0,
                    HirStmt::Block(Box::new(HirBlock {
                        stmts: vec![empty_local_decl(flag), condition_scope, exit_guard],
                    })),
                );
                cond_changed = true;
            }
            let mut stmt = HirStmt::While(while_stmt);
            let nested_changed = eliminate_nested_blocks_in_stmt(&mut stmt, state, safety);
            (vec![stmt], cond_changed || nested_changed)
        }
        HirStmt::Repeat(mut repeat_stmt) => {
            let mut cond_changed = eliminate_condition_expr(&mut repeat_stmt.cond, safety);
            let mut prefix = Vec::new();
            if expr_contains_eliminable_decision(&repeat_stmt.cond) {
                if repeat_continue_precedes_condition_local(&repeat_stmt.body, &repeat_stmt.cond) {
                    // 候选拒绝[SemanticBarrier:Scope]：continue 若位于 condition 读取的
                    // repeat-body local 声明之前，提前物化会生成越界读取并观察错误 epoch。
                } else if repeat_continue_crosses_live_nested_scope(&repeat_stmt.body, false, true)
                {
                    // 候选拒绝[SemanticBarrier:Lifetime]：嵌套 scope 中已声明的 local/TBC
                    // 原本会在 continue 到达 repeat latch 前退出；把条件物化到 continue
                    // 前会让条件观察仍存活的根/未关闭资源（见下面的 lifetime 回归）。
                } else {
                    let condition = mem::replace(&mut repeat_stmt.cond, HirExpr::Boolean(false));
                    let flag = state.alloc_local();
                    prefix.push(empty_local_decl(flag));
                    materialize_repeat_continues(
                        &mut repeat_stmt.body,
                        &condition,
                        flag,
                        state,
                        safety,
                    );
                    repeat_stmt.body.stmts.push(materialize_condition_into_flag(
                        condition, flag, state, safety,
                    ));
                    repeat_stmt.cond = HirExpr::LocalRef(flag);
                    cond_changed = true;
                }
            }
            let mut stmt = HirStmt::Repeat(repeat_stmt);
            let nested_changed = eliminate_nested_blocks_in_stmt(&mut stmt, state, safety);
            prefix.push(stmt);
            (prefix, nested_changed || cond_changed)
        }
        HirStmt::NumericFor(numeric_for) => {
            let (mut prefix, numeric_for, changed) =
                extract_numeric_for(numeric_for, state, safety);
            let mut stmt = HirStmt::NumericFor(numeric_for);
            let nested_changed = eliminate_nested_blocks_in_stmt(&mut stmt, state, safety);
            prefix.push(stmt);
            (prefix, changed || nested_changed)
        }
        HirStmt::GenericFor(generic_for) => {
            let (mut prefix, generic_for, changed) =
                extract_generic_for(generic_for, state, safety);
            let mut stmt = HirStmt::GenericFor(generic_for);
            let nested_changed = eliminate_nested_blocks_in_stmt(&mut stmt, state, safety);
            prefix.push(stmt);
            (prefix, changed || nested_changed)
        }
        HirStmt::Block(block) => {
            let mut stmt = HirStmt::Block(block);
            let changed = eliminate_nested_blocks_in_stmt(&mut stmt, state, safety);
            (vec![stmt], changed)
        }
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => (vec![stmt], false),
    }
}

fn repeat_continue_precedes_condition_local(block: &HirBlock, condition: &HirExpr) -> bool {
    let condition_locals = block
        .stmts
        .iter()
        .filter_map(|stmt| match stmt {
            HirStmt::LocalDecl(decl) => Some(decl.bindings.as_slice()),
            _ => None,
        })
        .flatten()
        .copied()
        .filter(|local| super::super::mention::expr_mentions_local(condition, *local))
        .collect::<Vec<_>>();
    if condition_locals.is_empty() {
        return false;
    }

    let mut declared = Vec::new();
    for stmt in &block.stmts {
        if stmt_has_current_owner_continue(stmt)
            && condition_locals
                .iter()
                .any(|local| !declared.contains(local))
        {
            return true;
        }
        if let HirStmt::LocalDecl(decl) = stmt {
            declared.extend(decl.bindings.iter().copied());
        }
    }
    false
}

fn stmt_has_current_owner_continue(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::LocalRootRelease(_) => false,
        HirStmt::Continue => true,
        HirStmt::If(if_stmt) => {
            if_stmt
                .then_block
                .stmts
                .iter()
                .any(stmt_has_current_owner_continue)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block.stmts.iter().any(stmt_has_current_owner_continue))
        }
        HirStmt::Block(block) => block.stmts.iter().any(stmt_has_current_owner_continue),
        HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_)
        | HirStmt::LocalDecl(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn repeat_continue_crosses_live_nested_scope(
    block: &HirBlock,
    inherited_live_scope: bool,
    repeat_body: bool,
) -> bool {
    let mut local_root_is_live = false;
    for stmt in &block.stmts {
        match stmt {
            HirStmt::LocalRootRelease(_) => {}
            HirStmt::Continue if inherited_live_scope || (!repeat_body && local_root_is_live) => {
                return true;
            }
            HirStmt::If(if_stmt) => {
                let inherited = inherited_live_scope || (!repeat_body && local_root_is_live);
                if repeat_continue_crosses_live_nested_scope(&if_stmt.then_block, inherited, false)
                    || if_stmt.else_block.as_ref().is_some_and(|block| {
                        repeat_continue_crosses_live_nested_scope(block, inherited, false)
                    })
                {
                    return true;
                }
            }
            HirStmt::Block(block)
                if repeat_continue_crosses_live_nested_scope(
                    block,
                    inherited_live_scope || (!repeat_body && local_root_is_live),
                    false,
                ) =>
            {
                return true;
            }
            HirStmt::LocalDecl(_) | HirStmt::ToBeClosed(_) => local_root_is_live = true,
            HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_) => {}
            HirStmt::GlobalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_)
            | HirStmt::Block(_) => {}
        }
    }
    false
}

fn materialize_repeat_continues(
    block: &mut HirBlock,
    condition: &HirExpr,
    flag: LocalId,
    state: &mut EliminationState<'_>,
    safety: HirExprSafety,
) {
    for stmt in &mut block.stmts {
        match stmt {
            HirStmt::LocalRootRelease(_) => {}
            HirStmt::Continue => {
                let condition_scope =
                    materialize_condition_into_flag(condition.clone(), flag, state, safety);
                *stmt = HirStmt::Block(Box::new(HirBlock {
                    stmts: vec![condition_scope, HirStmt::Continue],
                }));
            }
            HirStmt::If(if_stmt) => {
                materialize_repeat_continues(
                    &mut if_stmt.then_block,
                    condition,
                    flag,
                    state,
                    safety,
                );
                if let Some(else_block) = &mut if_stmt.else_block {
                    materialize_repeat_continues(else_block, condition, flag, state, safety);
                }
            }
            HirStmt::Block(block) => {
                materialize_repeat_continues(block, condition, flag, state, safety);
            }
            HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_)
            | HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => {}
        }
    }
}

fn eliminate_nested_blocks_in_stmt(
    stmt: &mut HirStmt,
    state: &mut EliminationState<'_>,
    safety: HirExprSafety,
) -> bool {
    rewrite_nested_blocks_in_stmt(stmt, &mut |block| {
        eliminate_block(block, state.next_local_index, safety)
    })
}

fn materialize_condition_flag(
    condition: HirExpr,
    state: &mut EliminationState<'_>,
    safety: HirExprSafety,
) -> (LocalId, HirStmt) {
    let flag = state.alloc_local();
    let scope = materialize_condition_into_flag(condition, flag, state, safety);
    (flag, scope)
}

fn materialize_condition_into_flag(
    condition: HirExpr,
    flag: LocalId,
    state: &mut EliminationState<'_>,
    safety: HirExprSafety,
) -> HirStmt {
    let (mut prefix, value, extracted) = extract_value_expr(condition, state, safety);
    assert!(
        extracted && !expr_contains_eliminable_decision(&value),
        "condition extraction must eliminate every Decision"
    );
    prefix.push(HirStmt::Assign(Box::new(crate::hir::common::HirAssign {
        targets: vec![HirLValue::Local(flag)],
        values: crate::hir::common::HirValuePack::fixed(vec![value.negate().negate()]),
        initializer_merge_transaction: None,
        generic_for_initializer_producer: None,
        method_rewrite_transaction: None,
    })));
    HirStmt::Block(Box::new(HirBlock { stmts: prefix }))
}

#[cfg(test)]
mod tests {
    use crate::decompile::DecompileDialect;
    use crate::hir::common::{
        HirBlock, HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr,
        HirGlobalRef, HirIf, HirLocalDecl, HirStmt, HirToBeClosed, HirValuePack, LocalId,
    };
    use crate::hir::expr_safety::HirExprSafety;
    use crate::transformer::InstrRef;

    use super::{EliminationState, eliminate_stmt};

    #[test]
    fn nonstable_if_decision_is_materialized_before_the_condition() {
        let decision = HirExpr::Decision(Box::new(HirDecisionExpr {
            entry: HirDecisionNodeRef(0),
            nodes: vec![HirDecisionNode {
                id: HirDecisionNodeRef(0),
                test: global("guard"),
                truthy: HirDecisionTarget::Expr(global("truthy")),
                falsy: HirDecisionTarget::Expr(global("falsy")),
            }],
        }));
        let stmt = HirStmt::If(Box::new(HirIf {
            cond: decision,
            then_block: HirBlock::default(),
            else_block: None,
        }));
        let mut next_local_index = 0;
        let mut state = EliminationState {
            next_local_index: &mut next_local_index,
        };

        let (lowered, changed) = eliminate_stmt(
            stmt,
            &mut state,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        );

        assert!(changed);
        let [HirStmt::Block(scope)] = lowered.as_slice() else {
            panic!("nonstable if Decision must use one guard scope");
        };
        let [
            HirStmt::LocalDecl(flag),
            HirStmt::Block(condition_scope),
            HirStmt::If(consumer),
        ] = scope.stmts.as_slice()
        else {
            panic!("if guard scope must contain flag, condition scope, and consumer");
        };
        let [flag_local] = flag.bindings.as_slice() else {
            panic!("condition flag must use one synthetic local");
        };
        assert!(flag.values.fixed.is_empty() && flag.values.tail.is_none());
        assert!(matches!(condition_scope.stmts[1], HirStmt::If(_)));
        assert!(matches!(consumer.cond, HirExpr::LocalRef(local) if local == *flag_local));
        assert_eq!(next_local_index, 2);
    }

    #[test]
    fn nonstable_while_decision_runs_before_each_continue_iteration() {
        let decision = HirExpr::Decision(Box::new(HirDecisionExpr {
            entry: HirDecisionNodeRef(0),
            nodes: vec![HirDecisionNode {
                id: HirDecisionNodeRef(0),
                test: global("guard"),
                truthy: HirDecisionTarget::Expr(global("truthy")),
                falsy: HirDecisionTarget::Expr(global("falsy")),
            }],
        }));
        let stmt = HirStmt::While(Box::new(crate::hir::common::HirWhile {
            cond: decision,
            body: HirBlock {
                stmts: vec![HirStmt::Continue],
            },
        }));
        let mut next_local_index = 0;
        let mut state = EliminationState {
            next_local_index: &mut next_local_index,
        };

        let (lowered, changed) = eliminate_stmt(
            stmt,
            &mut state,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        );

        assert!(changed);
        let [HirStmt::While(while_stmt)] = lowered.as_slice() else {
            panic!("nonstable while Decision must remain a while");
        };
        assert_eq!(while_stmt.cond, HirExpr::Boolean(true));
        assert!(matches!(while_stmt.body.stmts[0], HirStmt::Block(_)));
        assert!(matches!(while_stmt.body.stmts[1], HirStmt::Continue));
        let HirStmt::Block(guard_scope) = &while_stmt.body.stmts[0] else {
            unreachable!();
        };
        assert!(matches!(guard_scope.stmts[2], HirStmt::If(_)));
    }

    #[test]
    fn nonstable_repeat_decision_runs_at_the_body_tail() {
        let stmt = HirStmt::Repeat(Box::new(crate::hir::common::HirRepeat {
            body: HirBlock {
                stmts: vec![HirStmt::CallStmt(Box::new(
                    crate::hir::common::HirCallStmt {
                        call: crate::hir::common::HirCallExpr {
                            argument_roots: Vec::new(),
                            frame_root_ends: Vec::new(),
                            callee: global("body"),
                            args: crate::hir::common::HirValuePack::default(),
                            method: false,
                            fastcall: None,
                            method_key: None,
                            callee_root_handoff: None,
                            method_rewrite_transaction: None,
                        },
                    },
                ))],
            },
            cond: nonstable_decision(),
            lifetime: Default::default(),
        }));
        let mut next_local_index = 0;
        let mut state = EliminationState {
            next_local_index: &mut next_local_index,
        };

        let (lowered, changed) = eliminate_stmt(
            stmt,
            &mut state,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        );

        assert!(changed);
        let [HirStmt::LocalDecl(flag), HirStmt::Repeat(repeat)] = lowered.as_slice() else {
            panic!("repeat condition flag must be declared outside the loop");
        };
        let [flag] = flag.bindings.as_slice() else {
            panic!("repeat condition must use one boolean flag");
        };
        assert!(matches!(repeat.body.stmts[0], HirStmt::CallStmt(_)));
        assert!(matches!(repeat.body.stmts[1], HirStmt::Block(_)));
        assert!(matches!(repeat.cond, HirExpr::LocalRef(local) if local == *flag));
        assert!(
            !super::super::eliminate_materialize::expr_contains_eliminable_decision(&repeat.cond)
        );
    }

    #[test]
    fn top_level_repeat_continue_materializes_at_each_latch_path() {
        let stmt = HirStmt::Repeat(Box::new(crate::hir::common::HirRepeat {
            body: HirBlock {
                stmts: vec![HirStmt::Continue],
            },
            cond: nonstable_decision(),
            lifetime: Default::default(),
        }));
        let mut next_local_index = 0;
        let mut state = EliminationState {
            next_local_index: &mut next_local_index,
        };

        let (lowered, changed) = eliminate_stmt(
            stmt,
            &mut state,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        );

        assert!(changed);
        let [HirStmt::LocalDecl(flag), HirStmt::Repeat(repeat)] = lowered.as_slice() else {
            panic!("repeat continue materialization must declare one outer flag");
        };
        let [flag] = flag.bindings.as_slice() else {
            panic!("repeat condition must use one boolean flag");
        };
        let [HirStmt::Block(continue_route), HirStmt::Block(_tail)] = repeat.body.stmts.as_slice()
        else {
            panic!("continue and fallthrough must each materialize the latch condition");
        };
        assert!(matches!(continue_route.stmts[0], HirStmt::Block(_)));
        assert!(matches!(continue_route.stmts[1], HirStmt::Continue));
        assert!(matches!(repeat.cond, HirExpr::LocalRef(local) if local == *flag));
        assert!(next_local_index > 0);
    }

    #[test]
    fn root_free_nested_repeat_continue_materializes_in_its_branch() {
        let body_root = LocalId(0);
        let stmt = HirStmt::Repeat(Box::new(crate::hir::common::HirRepeat {
            body: HirBlock {
                stmts: vec![
                    HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: vec![body_root],
                        values: HirValuePack::fixed(vec![global("body_root")]),
                        initializer_merge_transaction: None,
                    })),
                    HirStmt::If(Box::new(HirIf {
                        cond: HirExpr::Boolean(true),
                        then_block: HirBlock {
                            stmts: vec![HirStmt::Continue],
                        },
                        else_block: None,
                    })),
                ],
            },
            cond: nonstable_decision(),
            lifetime: Default::default(),
        }));
        let mut next_local_index = 1;
        let mut state = EliminationState {
            next_local_index: &mut next_local_index,
        };

        let (lowered, changed) = eliminate_stmt(
            stmt,
            &mut state,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        );

        assert!(changed);
        let [HirStmt::LocalDecl(flag), HirStmt::Repeat(repeat)] = lowered.as_slice() else {
            panic!("root-free nested continue must share one latch flag");
        };
        let [flag] = flag.bindings.as_slice() else {
            panic!("repeat condition must use one boolean flag");
        };
        assert!(matches!(repeat.body.stmts[0], HirStmt::LocalDecl(_)));
        let HirStmt::If(if_stmt) = &repeat.body.stmts[1] else {
            panic!("nested continue must remain in its original branch");
        };
        let [HirStmt::Block(continue_route)] = if_stmt.then_block.stmts.as_slice() else {
            panic!("nested continue path must materialize the condition before transfer");
        };
        assert!(matches!(continue_route.stmts[0], HirStmt::Block(_)));
        assert!(matches!(continue_route.stmts[1], HirStmt::Continue));
        assert!(matches!(repeat.cond, HirExpr::LocalRef(local) if local == *flag));
    }

    #[test]
    fn nested_repeat_continue_with_live_tbc_keeps_original_latch() {
        let resource = LocalId(0);
        let stmt = HirStmt::Repeat(Box::new(crate::hir::common::HirRepeat {
            body: HirBlock {
                stmts: vec![HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::Boolean(true),
                    then_block: HirBlock {
                        stmts: vec![
                            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                                bindings: vec![resource],
                                values: HirValuePack::fixed(vec![global("resource")]),
                                initializer_merge_transaction: None,
                            })),
                            HirStmt::ToBeClosed(Box::new(HirToBeClosed {
                                origin: InstrRef(0),
                                reg_index: 0,
                                value: HirExpr::LocalRef(resource),
                            })),
                            HirStmt::Continue,
                        ],
                    },
                    else_block: None,
                }))],
            },
            cond: nonstable_decision(),
            lifetime: Default::default(),
        }));
        let mut next_local_index = 1;
        let mut state = EliminationState {
            next_local_index: &mut next_local_index,
        };

        let (lowered, changed) = eliminate_stmt(
            stmt,
            &mut state,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        );

        assert!(!changed);
        let [HirStmt::Repeat(repeat)] = lowered.as_slice() else {
            panic!("live TBC path must keep the condition at the real repeat latch");
        };
        assert!(matches!(repeat.cond, HirExpr::Decision(_)));
        assert_eq!(next_local_index, 1);
    }

    #[test]
    fn repeat_continue_before_condition_local_keeps_original_latch() {
        let future = LocalId(0);
        let stmt = HirStmt::Repeat(Box::new(crate::hir::common::HirRepeat {
            body: HirBlock {
                stmts: vec![
                    HirStmt::Continue,
                    HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: vec![future],
                        values: HirValuePack::fixed(vec![global("future")]),
                        initializer_merge_transaction: None,
                    })),
                ],
            },
            cond: nonstable_decision_with_local(future),
            lifetime: Default::default(),
        }));
        let mut next_local_index = 1;
        let mut state = EliminationState {
            next_local_index: &mut next_local_index,
        };

        let (lowered, changed) = eliminate_stmt(
            stmt,
            &mut state,
            HirExprSafety::for_dialect(DecompileDialect::Lua54),
        );

        assert!(!changed);
        let [HirStmt::Repeat(repeat)] = lowered.as_slice() else {
            panic!("future condition local must keep the condition at the real repeat latch");
        };
        assert!(matches!(repeat.cond, HirExpr::Decision(_)));
        assert_eq!(next_local_index, 1);
    }

    fn nonstable_decision() -> HirExpr {
        HirExpr::Decision(Box::new(HirDecisionExpr {
            entry: HirDecisionNodeRef(0),
            nodes: vec![HirDecisionNode {
                id: HirDecisionNodeRef(0),
                test: global("guard"),
                truthy: HirDecisionTarget::Expr(global("truthy")),
                falsy: HirDecisionTarget::Expr(global("falsy")),
            }],
        }))
    }

    fn nonstable_decision_with_local(local: LocalId) -> HirExpr {
        HirExpr::Decision(Box::new(HirDecisionExpr {
            entry: HirDecisionNodeRef(0),
            nodes: vec![HirDecisionNode {
                id: HirDecisionNodeRef(0),
                test: global("guard"),
                truthy: HirDecisionTarget::Expr(HirExpr::LocalRef(local)),
                falsy: HirDecisionTarget::Expr(global("falsy")),
            }],
        }))
    }

    fn global(name: &str) -> HirExpr {
        HirExpr::GlobalRef(HirGlobalRef { key: name.into() })
    }
}
