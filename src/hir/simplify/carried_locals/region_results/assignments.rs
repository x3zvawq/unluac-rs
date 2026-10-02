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

/// 纯 binding COPY 按结果建一次索引；独立声明继续保留自己的快照身份。
pub(super) fn immediate_binding_copies(
    stmt: &HirStmt,
) -> Option<BTreeMap<CarryBinding, CarryBinding>> {
    if let HirStmt::LocalDecl(decl) = stmt {
        let ([target], [source], None) = (
            decl.bindings.as_slice(),
            decl.values.fixed.as_slice(),
            &decl.values.tail,
        ) else {
            return None;
        };
        if decl.initializer_merge_transaction.is_some()
            || decl.generic_for_initializer_producer.is_some()
        {
            // 候选拒绝[LayerBoundary]：协议初始化仍由其事务 owner 消费，不能在此替换输入。
            return None;
        }
        return Some(BTreeMap::from([(
            carry_binding_from_expr(source)?,
            CarryBinding::Local(*target),
        )]));
    }
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    if assign.values.tail.is_some() || assign.targets.len() != assign.values.fixed.len() {
        return None;
    }
    let mut targets = BTreeSet::new();
    let mut writebacks = BTreeMap::new();
    for (target, value) in assign.targets.iter().zip(&assign.values.fixed) {
        let target = carry_binding_from_lvalue(target)?;
        let source = carry_binding_from_expr(value)?;
        if !targets.insert(target) || writebacks.insert(source, target).is_some() {
            return None;
        }
    }
    Some(writebacks)
}
