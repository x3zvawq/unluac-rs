//! 识别初始化、完整 if assignment、精确 writeback 与控制流屏障；依赖 HIR statement，不负责条件 scratch；例如确认 then/else 都写回同一 result。

use super::*;

pub(super) fn initialized_local(stmt: &HirStmt) -> Option<(LocalId, &HirExpr)> {
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

pub(super) fn empty_local(stmt: &HirStmt) -> Option<LocalId> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    local_decl.values.is_empty().then_some(*binding)
}

pub(super) fn if_fallthrough_assignments(
    if_stmt: &HirIf,
    results: &[CarryBinding],
) -> Option<Vec<BTreeMap<CarryBinding, HirExpr>>> {
    let else_block = if_stmt.else_block.as_ref()?;
    let mut exits = Vec::new();
    let then_falls = collect_fallthrough_assignments(&if_stmt.then_block, results, &mut exits)?;
    let else_falls = collect_fallthrough_assignments(else_block, results, &mut exits)?;
    (then_falls || else_falls).then_some(exits)
}

pub(super) fn complete_if_assignments(
    if_stmt: &HirIf,
    results: &[CarryBinding],
) -> Option<Vec<BTreeMap<CarryBinding, HirExpr>>> {
    let else_block = if_stmt.else_block.as_ref()?;
    let mut exits = Vec::new();
    collect_complete_assignments(&if_stmt.then_block, results, &mut exits)?;
    collect_complete_assignments(else_block, results, &mut exits)?;
    Some(exits)
}

pub(super) fn collect_complete_assignments(
    block: &HirBlock,
    results: &[CarryBinding],
    exits: &mut Vec<BTreeMap<CarryBinding, HirExpr>>,
) -> Option<()> {
    let (last, prefix) = block.stmts.split_last()?;
    if bindings_are_mentioned_in_stmts(prefix, results) {
        return None;
    }
    match last {
        HirStmt::Assign(assign) => {
            exits.push(complete_result_assignment_values(assign, results)?);
            Some(())
        }
        HirStmt::If(if_stmt) => {
            let else_block = if_stmt.else_block.as_ref()?;
            collect_complete_assignments(&if_stmt.then_block, results, exits)?;
            collect_complete_assignments(else_block, results, exits)
        }
        HirStmt::Block(block) => collect_complete_assignments(block, results, exits),
        _ => None,
    }
}

pub(super) fn complete_result_assignment_values(
    assign: &HirAssign,
    results: &[CarryBinding],
) -> Option<BTreeMap<CarryBinding, HirExpr>> {
    let values = assignment_values(assign)?;
    let result_values = results
        .iter()
        .map(|result| values.get(result))
        .collect::<Option<Vec<_>>>()?;
    (!bindings_are_mentioned_in_exprs(result_values, results)).then_some(values)
}

pub(super) fn exact_state_writeback(stmt: &HirStmt, result: CarryBinding) -> Option<CarryBinding> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() || carry_binding_from_expr(value) != Some(result) {
        return None;
    }
    carry_binding_from_lvalue(target)
}
