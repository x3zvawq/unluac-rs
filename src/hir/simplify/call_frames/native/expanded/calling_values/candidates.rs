//! 将当前带捕获更新的短路分支与原完整结果组配对。
//! 保留调用结果、引用 cell 更新和所有内部选值边，供完整源码帧事务消费。

use super::*;
use crate::transformer::InstrRef;

#[derive(Debug, Clone)]
pub(super) struct Candidate {
    pub source: crate::hir::HirSourceSite,
    /// 原条件 owner；结果可由 RegionResult 或分支内的 EdgeCopy 持有。
    pub predicate: crate::hir::HirSourceSite,
    pub source_pc: u32,
    pub end: InstrRef,
    pub result: TempId,
    pub initial: TempId,
    pub value: LocalId,
    pub value_input: TempId,
    pub value_source: TempId,
    pub counter: LocalId,
    pub index: LocalId,
    pub table: LocalId,
    pub increment: i64,
    pub key: i64,
    pub hit: Literal,
    pub fallback: Literal,
}

pub(super) fn candidate(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    branch: &crate::hir::HirIf,
) -> Option<Candidate> {
    let HirExpr::LocalRef(initial_local) = branch.cond else {
        return None;
    };
    let [update, choice, fallback, writeback] = branch.then_block.stmts.as_slice() else {
        return None;
    };
    let (counter, HirExpr::Binary(add)) = scalar_local(update)? else {
        return None;
    };
    let (choice_local, HirExpr::LogicalOr(selection)) = scalar_local(choice)? else {
        return None;
    };
    let HirExpr::LogicalAnd(selected) = &selection.lhs else {
        return None;
    };
    let HirExpr::Binary(test) = &selected.lhs else {
        return None;
    };
    let HirExpr::LocalRef(index) = test.lhs else {
        return None;
    };
    let HirExpr::TableAccess(lookup) = &selection.rhs else {
        return None;
    };
    let HirExpr::LocalRef(table) = lookup.base else {
        return None;
    };
    let (fallback_local, HirExpr::LogicalOr(alternative)) = scalar_local(fallback)? else {
        return None;
    };
    let (target, HirExpr::Binary(comparison)) = scalar_local(writeback)? else {
        return None;
    };
    let carries_initial = match &branch.else_block {
        None => target == initial_local,
        Some(block) => matches!(block.stmts.as_slice(), [HirStmt::Assign(transfer)]
            if transfer.is_phi_transfer
                && transfer.targets == [HirLValue::Local(target)]
                && transfer.values.fixed == [HirExpr::LocalRef(initial_local)]
                && transfer.values.tail.is_none()
                && transfer.initializer_merge_transaction.is_none()
                && transfer.root_release.is_none()
                && transfer.method_rewrite_transaction.is_none()),
    };
    if !carries_initial {
        return None;
    }
    let HirExpr::LocalRef(value) = comparison.lhs else {
        return None;
    };
    let predicate = branch.predicate_source?;
    let frame = facts.branch_value_frame_at(predicate)?;
    // 外层 Boolean 合流可由分支内的 edge-copy 持有；Frame 已证明其全部入口
    // 仍来自当前分支，恢复完整调用时与 RegionResult 一起消费，不能仅按 disposition 漏掉它。
    let result = frame
        .results
        .iter()
        .chain(frame.edge_results(facts))
        .find(|result| facts.promoted_local_for_temp(result.value) == Some(target))?;
    let state = frame
        .results
        .iter()
        .chain(frame.edge_results(facts))
        .find(|result| facts.promoted_local_for_temp(result.value) == Some(counter))?;
    let original = |instr| crate::hir::HirSourceSite {
        proto: proto.id,
        instr,
    };
    let increment = crate::hir::luau_inlining::small_integer(&add.rhs)?;
    let key = crate::hir::luau_inlining::small_integer(&test.rhs)?;
    let hit = Literal::from_expr(&selected.rhs)?;
    // 当前 and/or 选值只有真值命中臂才能等价于 reader 的提前 return。
    if matches!(hit, Literal::Nil | Literal::Boolean(false)) {
        return None;
    }
    let fallback_value = Literal::from_expr(&alternative.rhs)?;
    let add_source = add.source_site?;
    let test_source = test.source_site?;
    let compare_source = comparison.source_site?;
    let HirOperationSources::Single(lookup_source) = lookup.sources else {
        return None;
    };
    let select = facts.branch_value_frame_at(test_source)?;
    let [selection_result] = select.results.as_slice() else {
        return None;
    };
    let alternative_frame = facts.branch_value_frame_at(original(select.end))?;
    let [alternative_result] = alternative_frame.results.as_slice() else {
        return None;
    };
    let initial = result
        .incoming
        .iter()
        .find(|incoming| incoming.copy.is_some())?;
    let source = original(initial.source?);
    let (true_exit, false_exit) = facts.original_branch_routes(compare_source)?;
    let (hit_entry, miss_entry) = facts.original_branch_routes(test_source)?;
    let (keep_entry, alternative_entry) = facts.original_branch_routes(original(select.end))?;
    let leaf =
        |result: &crate::hir::promotion::branch_values::ResultValue, site, value: &Literal| {
            result.incoming.iter().any(|incoming| {
                incoming.source == Some(site)
                    && incoming.terminal_write
                    && incoming.literal.as_ref() == Some(value)
            })
        };
    let add_layout = facts.native_binary_layout(add)?;
    let test_layout = facts.native_binary_layout(test)?;
    let compare_layout = facts.native_binary_layout(comparison)?;
    let lookup_layout = facts.native_table_read_layout(lookup)?;
    let value_copy = facts.binary_operand_copy(comparison, 0)?;
    let value_source = value_copy.source?;
    if frame.results.len() + frame.edge_results(facts).count() != 2
        || frame.predicates != [predicate.instr]
        || frame.begin > source.instr
        || source.instr.index() + 1 != predicate.instr.index()
        || facts.original_branch_routes(predicate)? != (add_source.instr, frame.end)
        || !matches!(update, HirStmt::Assign(assign) if !assign.is_phi_transfer && assign.initializer_merge_transaction.is_none())
        || !matches!(choice, HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_none())
        || !matches!(fallback, HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_none())
        || !matches!(writeback, HirStmt::Assign(assign) if !assign.is_phi_transfer && assign.initializer_merge_transaction.is_none())
        || facts.promoted_local_for_temp(initial.value) != Some(initial_local)
        || add.op != HirBinaryOpKind::Add
        || add.lhs != HirExpr::LocalRef(counter)
        || test.op != HirBinaryOpKind::Eq
        || lookup.key != HirExpr::LocalRef(index)
        || alternative.lhs != HirExpr::LocalRef(choice_local)
        || comparison.op != HirBinaryOpKind::Eq
        || comparison.rhs != HirExpr::LocalRef(fallback_local)
        || select.begin != add_source.instr
        || select.predicates != [test_source.instr]
        || test_source.instr.index() != add_source.instr.index() + 1
        || alternative_frame.predicates != [select.end]
        || alternative_frame.end != compare_source.instr
        || frame.end.index() != compare_source.instr.index() + 4
        || result.incoming.len() != 3
        || state.incoming.len() != 3
        || selection_result.incoming.len() != 2
        || alternative_result.incoming.len() != 2
        || facts.promoted_local_for_temp(selection_result.value) != Some(choice_local)
        || facts.promoted_local_for_temp(alternative_result.value) != Some(fallback_local)
        || result.home != HomeSlotKey::new(result.home.slot(), 0)
        || selection_result.home != HomeSlotKey::new(result.home.slot() + 3, 0)
        || alternative_result.home != HomeSlotKey::new(result.home.slot() + 2, 0)
        || facts.trusted_local_home_slot(value) != Some(value_copy.target_home)
        // scratch 后续可用于引用捕获；沿原 COPY 的 epoch 核对当前参数身份，不伪造零 epoch。
        || value_copy.target_home.slot() != result.home.slot() + 1
        || value_copy.source_home.slot() >= result.home.slot()
        || facts.promoted_local_for_temp(value_copy.target) != Some(value)
        || facts
            .binary_operand_copy_instruction(comparison, 0)?
            .index()
            + 1
            != source.instr.index()
        || state.home.slot() >= result.home.slot()
        || add_layout.lhs != Some(state.home)
        || add_layout.rhs.is_some()
        || facts.operation_result_home(add_source) != Some(state.home)
        || state
            .incoming
            .iter()
            .filter(|incoming| incoming.source == Some(add_source.instr))
            .count()
            != 2
        || state
            .incoming
            .iter()
            .filter(|incoming| incoming.source.is_some_and(|site| site < source.instr))
            .count()
            != 1
        || !leaf(result, true_exit, &Literal::Boolean(true))
        || !leaf(result, false_exit, &Literal::Boolean(false))
        || !leaf(selection_result, hit_entry, &hit)
        || miss_entry != lookup_source.instr
        || !selection_result.incoming.iter().any(|incoming| {
            incoming.source == Some(lookup_source.instr)
                && incoming.terminal_write
                && facts.operation_result_temp(lookup_source) == Some(incoming.value)
        })
        || !leaf(alternative_result, alternative_entry, &fallback_value)
        || !alternative_result.incoming.iter().any(|incoming| {
            incoming.source == Some(keep_entry)
                && incoming.terminal_write
                && incoming.copy
                    == Some((
                        HirBinding::Temp(selection_result.value),
                        selection_result.home,
                    ))
        })
        || compare_layout.lhs != facts.trusted_local_home_slot(value)
        || compare_layout.rhs != Some(alternative_result.home)
        || test_layout.lhs != facts.trusted_local_home_slot(index)
        || test_layout.rhs.is_some()
        || lookup_layout.base != facts.trusted_local_home_slot(table)?
        || lookup_layout.key != facts.trusted_local_home_slot(index)
        || [index, table].iter().any(|local| {
            facts
                .trusted_local_home_slot(*local)
                .is_none_or(|home| home.slot() >= result.home.slot())
        })
    {
        return None;
    }
    Some(Candidate {
        source,
        predicate,
        source_pc: facts.binary_operand_copy_after_pc(comparison, 0)?,
        end: frame.end,
        result: result.value,
        initial: initial.value,
        value,
        value_input: value_copy.target,
        value_source,
        counter,
        index,
        table,
        increment,
        key,
        hit,
        fallback: fallback_value,
    })
}
