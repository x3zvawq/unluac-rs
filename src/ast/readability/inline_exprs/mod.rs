//! 受阈值约束的保守表达式内联。
//!
//! 这里只处理非常窄的一类模式：
//! - 单值 local 别名；原生 temp 的语义内联归 HIR
//! - 后续只使用一次
//! - 使用点出现在 return / 调用参数 / 索引位 / 调用目标
//! - 被内联表达式必须是我们能证明“纯且无元方法副作用”的安全子集
//! - 相邻调用准备 run 中的简单表构造参数，可以随同 receiver/callee 一起收回调用位
//! - 相邻 recovered local run 里，只有末尾 local 仍会跨语句存活的机械链
//! - generic-for 的 method receiver 允许收回一个紧邻的 recovered binding 别名
//! - repeat body 的 use index 把 until 条件计作尾随表达式，不删除仍对条件可见的 local
//! - 多值 return 顶层只收回 context-safe 的唯一引用 alias；可变快照仍通过求值前缀证明
//! - 稳定 local copy 可跨越无关语句收回到唯一后续 use；只替换名字读取，不搬动 RHS

mod candidate;
mod eval_order;
mod use_sites;

use std::collections::BTreeMap;

use crate::ast::ReadabilityOptions;

use self::candidate::{
    InlineCandidate, InlinePolicy, inline_candidate, stmt_is_adjacent_call_result_sink,
    stmt_is_alias_initializer_sink, stmt_is_direct_return_value_sink,
};
use self::use_sites::rewrite_stmt_use_sites_with_policy;
use super::super::common::{
    AstBindingRef, AstBlock, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue, AstLocalAttr,
    AstLocalOrigin, AstModule, AstNameRef, AstStmt,
};
use super::ReadabilityContext;
use super::binding_flow::{
    BindingUseIndex, MutableSnapshotNames, binding_mentions_in_expr,
    mutable_snapshot_names_in_block,
};
use super::binding_ref::binding_from_name_ref;
use super::binding_tree::{
    expr_references_binding, stmt_has_access_base_binding_use, stmt_has_call_callee_binding_use,
    stmt_has_direct_call_arg_binding_use, stmt_has_index_binding_use, stmt_has_nested_binding_use,
    stmt_has_nested_binding_value_use, stmt_stores_binding_in_table,
};
use super::stmt_plan::{PlannedStmt, materialize_stmt_plan};
use super::visit::AstVisitor;
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let _ = context.target;
    let root_mutable_snapshots = mutable_snapshot_names_in_block(&module.body);
    walk::rewrite_module(
        module,
        &mut InlineExprsPass {
            options: context.options,
            mutable_snapshot_stack: vec![root_mutable_snapshots],
        },
    )
}

struct InlineExprsPass {
    options: ReadabilityOptions,
    mutable_snapshot_stack: Vec<MutableSnapshotNames>,
}

#[derive(Default)]
struct BindingWriteIndex {
    write_bounds_by_binding: BTreeMap<AstBindingRef, (usize, usize)>,
}

impl BindingWriteIndex {
    fn for_stmts(stmts: &[AstStmt]) -> Self {
        let mut index = Self::default();
        for (stmt_index, stmt) in stmts.iter().enumerate() {
            let mut collector = BindingWriteCollector {
                stmt_index,
                index: &mut index,
            };
            super::visit::visit_stmt(stmt, &mut collector);
        }
        index
    }

    fn record(&mut self, stmt_index: usize, binding: AstBindingRef) {
        self.write_bounds_by_binding
            .entry(binding)
            .and_modify(|bounds| bounds.1 = stmt_index)
            .or_insert((stmt_index, stmt_index));
    }

    fn has_write_after(&self, stmt_index: usize, binding: AstBindingRef) -> bool {
        self.write_bounds_by_binding
            .get(&binding)
            .is_some_and(|(_, last_write)| *last_write > stmt_index)
    }

    fn writes_start_after(&self, stmt_index: usize, binding: AstBindingRef) -> bool {
        self.write_bounds_by_binding
            .get(&binding)
            .is_some_and(|(first_write, _)| *first_write > stmt_index)
    }
}

fn removable_inline_candidate<'a>(
    stmts: &'a [AstStmt],
    stmt_index: usize,
    write_index: &BindingWriteIndex,
) -> Option<(InlineCandidate, &'a AstExpr)> {
    let (candidate, value) = inline_candidate(stmts.get(stmt_index)?)?;
    (!write_index.has_write_after(stmt_index, candidate.binding())).then_some((candidate, value))
}

struct BindingWriteCollector<'a> {
    stmt_index: usize,
    index: &'a mut BindingWriteIndex,
}

impl AstVisitor for BindingWriteCollector<'_> {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        let AstStmt::FunctionDecl(function) = stmt else {
            return;
        };
        let AstFunctionName::Plain(path) = &function.target else {
            return;
        };
        if path.fields.is_empty()
            && let Some(binding) = binding_from_name_ref(&path.root)
        {
            self.index.record(self.stmt_index, binding);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &AstLValue) {
        let AstLValue::Name(name) = lvalue else {
            return;
        };
        if let Some(binding) = binding_from_name_ref(name) {
            self.index.record(self.stmt_index, binding);
        }
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}

impl AstRewritePass for InlineExprsPass {
    fn enter_function(&mut self, function: &AstFunctionExpr) {
        self.mutable_snapshot_stack
            .push(mutable_snapshot_names_in_block(&function.body));
    }

    fn leave_function(&mut self, _function: &AstFunctionExpr) {
        self.mutable_snapshot_stack.pop();
    }

    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        rewrite_current_block(
            block,
            self.options,
            self.mutable_snapshot_stack
                .last()
                .expect("module scope must remain active"),
            None,
        )
    }

    fn rewrite_repeat_body(&mut self, block: &mut AstBlock, condition: &AstExpr) -> bool {
        rewrite_current_block(
            block,
            self.options,
            self.mutable_snapshot_stack
                .last()
                .expect("module scope must remain active"),
            Some(condition),
        )
    }
}

fn rewrite_current_block(
    block: &mut AstBlock,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let mut changed = collapse_adjacent_self_call_updates(block, trailing_condition);

    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&old_stmts, trailing_condition);
    let write_index = BindingWriteIndex::for_stmts(&old_stmts);
    let mut stmt_plan = Vec::with_capacity(old_stmts.len());
    let mut index = 0;
    while index < old_stmts.len() {
        let Some(next_stmt) = old_stmts.get(index + 1) else {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        };

        let Some((candidate, value)) = removable_inline_candidate(&old_stmts, index, &write_index)
        else {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        };
        if index.checked_sub(1).is_some_and(|run_start| {
            super::function_sugar::run_belongs_to_method_alias_owner(
                &old_stmts,
                run_start,
                index + 1,
                &use_index,
                mutable_snapshots,
            )
        }) {
            // Preserve the field alias until function-sugar can consume the receiver snapshot,
            // lookup, and call atomically. Inlining only the lookup loses the method proof.
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if matches!(value, AstExpr::Call(_) | AstExpr::MethodCall(_))
            && stmt_stores_binding_in_table(next_stmt, candidate.binding())
        {
            // Keep a call result local while it is the table's only strong root.  A later
            // rawset/clear may otherwise make the generated expression collectable earlier.
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        let policy = if stmt_is_alias_initializer_sink(next_stmt) {
            InlinePolicy::AliasInitializerChain
        } else if stmt_is_adjacent_call_result_sink(next_stmt) {
            InlinePolicy::AdjacentCallResultCallee
        } else if stmt_is_direct_return_value_sink(next_stmt) {
            InlinePolicy::DirectReturnConstructor
        } else {
            InlinePolicy::Conservative
        };
        if matches!(policy, InlinePolicy::AliasInitializerChain)
            && candidate::is_lookup_inline_expr(value)
            && stmt_starts_lookup_mechanical_run(&old_stmts, index, candidate.binding())
        {
            // 这里故意不提前把 lookup 链压成“下一条 local 的初始化式”：
            // `local item = items[i]; local weight = item.weight; sum = sum + weight`
            // 如果太早收成 `local weight = items[i].weight`，后面的机械 run 就只剩一层，
            // 无法再判断“整条链都只是脚手架”。让它留到 run-collapse 一次性处理，
            // 才能既收回 for-loop 里的机械局部，又保住 return 场景下的阶段 local。
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        let is_recovered = candidate.origin() == super::super::common::AstLocalOrigin::Recovered;
        let allows_special_lookup_access_base = is_recovered
            && matches!(policy, InlinePolicy::Conservative)
            && matches!(next_stmt, AstStmt::Assign(_))
            && candidate::is_lookup_inline_expr(value)
            && stmt_has_access_base_binding_use(next_stmt, candidate.binding());
        let allows_special_index_sink = is_recovered
            && matches!(policy, InlinePolicy::Conservative)
            && matches!(next_stmt, AstStmt::Assign(_))
            && super::expr_analysis::is_mechanical_run_inline_expr(value)
            && stmt_has_index_binding_use(next_stmt, candidate.binding());
        let allows_special_adjacent_value_sink = is_recovered
            && matches!(
                policy,
                InlinePolicy::Conservative | InlinePolicy::AliasInitializerChain
            )
            && matches!(next_stmt, AstStmt::Assign(_) | AstStmt::LocalDecl(_))
            && stmt_sink_binding_allows_adjacent_value_inline(&old_stmts, index + 1)
            && ((candidate::is_raw_global_alias_expr(value)
                && stmt_has_direct_call_arg_binding_use(next_stmt, candidate.binding()))
                || (stmt_has_nested_binding_value_use(next_stmt, candidate.binding())
                    && (candidate::is_recallable_inline_expr(value)
                        || (candidate::is_lookup_inline_expr(value)
                            && assign_targets_same_lookup_expr(next_stmt, value)))));
        let effective_policy = if allows_special_index_sink {
            InlinePolicy::MechanicalRun
        } else if allows_special_adjacent_value_sink {
            InlinePolicy::AdjacentValueSink
        } else {
            policy
        };
        if !candidate.allows_expr_with_policy(value, effective_policy)
            && !allows_special_lookup_access_base
        {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if use_index.count_uses_in_suffix(index + 1, candidate.binding()) != 1 {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }
        if inline_crosses_evaluation_boundary(
            value,
            next_stmt,
            candidate.binding(),
            mutable_snapshots,
        ) {
            stmt_plan.push(PlannedStmt::Original(index));
            index += 1;
            continue;
        }

        let mut rewritten_next = next_stmt.clone();
        let mut rewrite_policy = effective_policy;
        if !rewrite_stmt_use_sites_with_policy(
            &mut rewritten_next,
            candidate,
            value,
            options,
            rewrite_policy,
        ) {
            if matches!(policy, InlinePolicy::AliasInitializerChain)
                && candidate::is_recallable_inline_expr(value)
                && stmt_has_direct_call_arg_binding_use(next_stmt, candidate.binding())
            {
                rewritten_next = next_stmt.clone();
                rewrite_policy = InlinePolicy::ExtendedCallChain;
                if !rewrite_stmt_use_sites_with_policy(
                    &mut rewritten_next,
                    candidate,
                    value,
                    options,
                    rewrite_policy,
                ) {
                    stmt_plan.push(PlannedStmt::Original(index));
                    index += 1;
                    continue;
                }
            } else {
                stmt_plan.push(PlannedStmt::Original(index));
                index += 1;
                continue;
            }
        }

        stmt_plan.push(PlannedStmt::Rewritten(rewritten_next));
        changed = true;
        index += 2;
    }

    block.stmts = materialize_stmt_plan(old_stmts, stmt_plan);
    changed |= collapse_stable_copy_aliases(block, options, mutable_snapshots, trailing_condition);
    changed |=
        collapse_adjacent_call_alias_runs(block, options, mutable_snapshots, trailing_condition);
    changed |= collapse_terminal_call_result_alias_runs(
        block,
        options,
        mutable_snapshots,
        trailing_condition,
    );
    changed |= collapse_terminal_local_mechanical_runs(
        block,
        options,
        mutable_snapshots,
        trailing_condition,
    );
    changed |= collapse_adjacent_mechanical_alias_runs(
        block,
        options,
        mutable_snapshots,
        trailing_condition,
    );
    changed
}

/// 收回跨越无关语句的直接 local copy。
///
/// 这条规则与相邻表达式内联故意分开：相邻规则可以凭 sink 形状证明调用/lookup 的
/// 求值前缀，而这里只接受 `local alias = source`。source 在候选声明之前已经声明、
/// 候选之后没有任何 direct write，也没有 closure capture；因此把唯一后续读取改回
/// source 只改变 binding 名；primitive literal 则没有求值事件且只替换一次读取。
/// repeat 的精确 trailing handoff 允许 source 在 use 后写入，因为 target 会接管 root
/// 直到 `until` 条件；两条路径都不改变调用顺序或对象存活期。
fn collapse_stable_copy_aliases(
    block: &mut AstBlock,
    options: ReadabilityOptions,
    mutable_snapshots: &MutableSnapshotNames,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let mut stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts_with_trailing_expr(&stmts, trailing_condition);
    let write_index = BindingWriteIndex::for_stmts(&stmts);
    let mut removed = vec![false; stmts.len()];

    for (candidate_index, is_removed) in removed.iter_mut().enumerate() {
        let Some((candidate, value)) =
            removable_inline_candidate(&stmts, candidate_index, &write_index)
        else {
            continue;
        };
        if candidate.origin() != super::super::common::AstLocalOrigin::Recovered
            || !candidate.allows_expr_with_policy(value, InlinePolicy::StableCopy)
            || mutable_snapshots.contains(&candidate.binding().to_name_ref())
        {
            continue;
        }

        let Some(use_stmt_index) = use_index
            .unique_use_stmt_in_suffix(candidate_index + 1, candidate.binding())
            .filter(|use_stmt_index| *use_stmt_index < stmts.len())
        else {
            // A repeat's trailing condition is outside this block's statement rewrite boundary.
            continue;
        };

        if let AstExpr::Var(source_name) = value {
            let Some(source_binding) = binding_from_name_ref(source_name) else {
                // Parameters are intentionally owned by HIR local convergence; globals,
                // upvalues and temps have no stable copy proof at this AST stage.
                continue;
            };
            // A bound local/synthetic name can only appear while its lexical declaration is
            // active, so the AST binding identity itself supplies the dominance proof.
            if !matches!(
                source_binding,
                AstBindingRef::Local(_) | AstBindingRef::SyntheticLocal(_)
            ) || mutable_snapshots.contains(source_name)
            {
                continue;
            }
            if write_index.has_write_after(candidate_index, source_binding)
                && !stable_copy_has_trailing_root_handoff(
                    &stmts,
                    trailing_condition,
                    &write_index,
                    mutable_snapshots,
                    use_stmt_index,
                    candidate.binding(),
                    source_binding,
                )
            {
                continue;
            }
        }

        let replacement = value.clone();
        if rewrite_stmt_use_sites_with_policy(
            &mut stmts[use_stmt_index],
            candidate,
            &replacement,
            options,
            InlinePolicy::StableCopy,
        ) {
            *is_removed = true;
        }
    }

    let changed = removed.contains(&true);
    block.stmts = stmts
        .into_iter()
        .enumerate()
        .filter_map(|(index, stmt)| (!removed[index]).then_some(stmt))
        .collect();
    changed
}

fn stable_copy_has_trailing_root_handoff(
    stmts: &[AstStmt],
    trailing_condition: Option<&AstExpr>,
    write_index: &BindingWriteIndex,
    mutable_snapshots: &MutableSnapshotNames,
    use_stmt_index: usize,
    candidate: AstBindingRef,
    source: AstBindingRef,
) -> bool {
    if stmts
        .iter()
        .any(super::control_flow::stmt_contains_label_or_goto)
        || !write_index.writes_start_after(use_stmt_index, source)
    {
        return false;
    }
    let AstStmt::Assign(assign) = &stmts[use_stmt_index] else {
        return false;
    };
    let ([AstLValue::Name(target)], [AstExpr::Var(value)]) =
        (assign.targets.as_slice(), assign.values.as_slice())
    else {
        return false;
    };
    let Some(target) = binding_from_name_ref(target).filter(|_| candidate.matches_name_ref(value))
    else {
        return false;
    };
    target != source
        && !mutable_snapshots.contains(&target.to_name_ref())
        && !write_index.has_write_after(use_stmt_index, target)
        && trailing_condition.is_some_and(|condition| expr_references_binding(condition, target))
}

fn inline_crosses_evaluation_boundary(
    value: &AstExpr,
    next_stmt: &AstStmt,
    binding: AstBindingRef,
    mutable_snapshots: &MutableSnapshotNames,
) -> bool {
    (matches!(next_stmt, AstStmt::While(_) | AstStmt::Repeat(_))
        && !super::expr_analysis::is_stable_inline_value(value))
        || (super::expr_analysis::expr_requires_ordered_snapshot(value, mutable_snapshots)
            && !eval_order::preserves_adjacent_eval_order(
                next_stmt,
                binding,
                value,
                mutable_snapshots,
            ))
}

mod runs;
use runs::*;

#[cfg(test)]
mod tests {
    use crate::ast::common::{
        AstAssign, AstCallExpr, AstCallKind, AstCallStmt, AstGlobalName, AstLocalAttr,
        AstLocalBinding, AstLocalDecl, AstLocalOrigin, AstNameRef,
    };
    use crate::hir::LocalId;

    use super::*;

    #[test]
    fn keeps_local_declaration_before_later_direct_write() {
        let binding = AstBindingRef::Local(LocalId(0));
        let global = |text: &str| {
            AstExpr::Var(AstNameRef::Global(AstGlobalName {
                text: text.to_owned(),
            }))
        };
        let mut block = AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: binding,
                        attr: AstLocalAttr::None,
                        origin: AstLocalOrigin::Recovered,
                    }],
                    values: vec![global("factory")],
                })),
                AstStmt::CallStmt(Box::new(AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(binding.to_name_ref()),
                        args: Vec::new(),
                    })),
                })),
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(binding.to_name_ref())],
                    values: vec![global("replacement")],
                })),
            ],
        };
        let expected = block.clone();

        assert!(!rewrite_current_block(
            &mut block,
            ReadabilityOptions::default(),
            &MutableSnapshotNames::new(),
            None,
        ));
        assert_eq!(block, expected);
    }

    #[test]
    fn inlines_global_callee_when_the_call_is_adjacent() {
        for origin in [AstLocalOrigin::Recovered, AstLocalOrigin::PhysicalRoot] {
            let binding = AstBindingRef::Local(LocalId(0));
            let global = AstExpr::Var(AstNameRef::Global(AstGlobalName {
                text: "assert".to_owned(),
            }));
            let mut block = AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: binding,
                            attr: AstLocalAttr::None,
                            origin,
                        }],
                        values: vec![global],
                    })),
                    AstStmt::CallStmt(Box::new(AstCallStmt {
                        call: AstCallKind::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(binding.to_name_ref()),
                            args: vec![AstExpr::Boolean(true)],
                        })),
                    })),
                ],
            };

            assert!(rewrite_current_block(
                &mut block,
                ReadabilityOptions::default(),
                &MutableSnapshotNames::new(),
                None,
            ));
            assert!(matches!(
                block.stmts.as_slice(),
                [AstStmt::CallStmt(call)]
                    if matches!(
                        &call.call,
                        AstCallKind::Call(call)
                            if matches!(call.callee, AstExpr::Var(AstNameRef::Global(_)))
                    )
            ));
        }
    }
}
