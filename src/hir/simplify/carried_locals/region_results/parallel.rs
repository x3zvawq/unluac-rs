//! 合并局部声明并拆分可证明独立的重写后并行赋值；依赖 binding mention 查询，不负责推导 rewrite；例如保持交叉读写赋值的并行语义。

use super::*;

pub(super) fn merge_initialized_local_declarations(
    block: &mut HirBlock,
    start: usize,
    count: usize,
) -> bool {
    if count < 2 || start + count > block.stmts.len() {
        return false;
    }
    let mut bindings = Vec::with_capacity(count);
    let mut values = Vec::with_capacity(count);
    for stmt in &block.stmts[start..start + count] {
        let Some((binding, value)) = initialized_local(stmt) else {
            return false;
        };
        let earlier = bindings
            .iter()
            .copied()
            .map(CarryBinding::Local)
            .collect::<Vec<_>>();
        if bindings_are_mentioned_in_exprs(std::iter::once(value), &earlier) {
            return false;
        }
        bindings.push(binding);
        values.push(value.clone());
    }
    block.stmts[start] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
        bindings,
        values: HirValuePack::fixed(values),
    }));
    block.stmts.drain(start + 1..start + count);
    true
}

pub(super) fn split_rewritten_parallel_assignments(
    stmt: &mut HirStmt,
    rewritten: &BTreeSet<CarryBinding>,
) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            let mut changed =
                split_rewritten_parallel_assignments_in_block(&mut if_stmt.then_block, rewritten);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= split_rewritten_parallel_assignments_in_block(else_block, rewritten);
            }
            changed
        }
        HirStmt::While(while_stmt) => {
            split_rewritten_parallel_assignments_in_block(&mut while_stmt.body, rewritten)
        }
        HirStmt::Repeat(repeat_stmt) => {
            split_rewritten_parallel_assignments_in_block(&mut repeat_stmt.body, rewritten)
        }
        HirStmt::NumericFor(numeric_for) => {
            split_rewritten_parallel_assignments_in_block(&mut numeric_for.body, rewritten)
        }
        HirStmt::GenericFor(generic_for) => {
            split_rewritten_parallel_assignments_in_block(&mut generic_for.body, rewritten)
        }
        HirStmt::Block(block) => split_rewritten_parallel_assignments_in_block(block, rewritten),
        _ => false,
    }
}

pub(super) fn split_rewritten_parallel_assignments_in_block(
    block: &mut HirBlock,
    rewritten: &BTreeSet<CarryBinding>,
) -> bool {
    let mut changed = false;
    let mut rebuilt = Vec::with_capacity(block.stmts.len());
    for mut stmt in std::mem::take(&mut block.stmts) {
        changed |= split_rewritten_parallel_assignments(&mut stmt, rewritten);
        let HirStmt::Assign(assign) = stmt else {
            rebuilt.push(stmt);
            continue;
        };
        if !parallel_assignment_is_independent(&assign, rewritten) {
            rebuilt.push(HirStmt::Assign(assign));
            continue;
        }
        let HirAssign { targets, values } = *assign;
        rebuilt.extend(
            targets
                .into_iter()
                .zip(values.fixed)
                .map(|(target, value)| {
                    HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![target],
                        values: HirValuePack::fixed(vec![value]),
                    }))
                }),
        );
        changed = true;
    }
    block.stmts = rebuilt;
    changed
}

pub(super) fn parallel_assignment_is_independent(
    assign: &HirAssign,
    rewritten: &BTreeSet<CarryBinding>,
) -> bool {
    if assign.values.tail.is_some()
        || assign.targets.len() < 2
        || assign.targets.len() != assign.values.fixed.len()
    {
        return false;
    }
    let Some(targets) = assign
        .targets
        .iter()
        .map(carry_binding_from_lvalue)
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    if targets
        .iter()
        .filter(|target| rewritten.contains(target))
        .count()
        < 1
        || targets.iter().copied().collect::<BTreeSet<_>>().len() != targets.len()
    {
        return false;
    }
    !bindings_are_mentioned_in_exprs(assign.values.fixed.iter(), &targets)
}
