//! 识别初始化、fallthrough assignment、精确 writeback 与控制流屏障；依赖 HIR statement，不负责条件 scratch。

use super::*;

pub(super) fn if_fallthrough_assignments(
    if_stmt: &HirIf,
    results: &[CarryBinding],
) -> Option<Vec<ExitValues>> {
    // 候选拒绝[SemanticBarrier:ControlFlow]：当前所有 caller 的 result 都来自空声明；无
    // else 路径保持 nil。若把 result 改名为既有 seed，该路径会错误地观察 seed 的旧值。
    let else_block = if_stmt.else_block.as_ref()?;
    let mut exits = Vec::new();
    let then_falls = collect_fallthrough_assignments(&if_stmt.then_block, results, &mut exits)?;
    let else_falls = collect_fallthrough_assignments(else_block, results, &mut exits)?;
    (then_falls || else_falls).then_some(exits)
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
