//! 这个文件负责把“稳定的建表片段”收回 `TableConstructor`。
//!
//! `NewTable + SetTable + SetList` 在 low-IR 里天然是分散的；如果 HIR 一直把它们保留成
//! 零散语句，后面 AST 虽然还能继续工作，但整层会长期带着明显的机械噪音。这里专门吃一类
//! 很稳的构造区域：
//! 1. 先出现一个空表构造器 seed；
//! 2. 后面紧跟一段 keyed write、简单值生产和 `table-set-list`；
//! 3. 这段时间里表值没有逃逸，也没有跨语句依赖还没落地的中间绑定。
//!
//! 这样做的目的不是“尽可能多地猜源码”，而是把已经能够证明安全的构造片段收回更自然的
//! HIR 形状，为后续 AST 降低继续减负。

use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirProto, HirStmt, HirTableConstructor, HirTableField,
    HirTableKey, HirTableSetList, LocalId, TempId,
};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum TableBinding {
    Temp(TempId),
    Local(LocalId),
}

#[derive(Debug, Clone)]
enum RegionStep {
    Producer(TableBinding, HirExpr),
    Record(crate::hir::common::HirRecordField),
    SetList(HirTableSetList),
}

pub(super) fn stabilize_table_constructors_in_proto(proto: &mut HirProto) -> bool {
    stabilize_block(&mut proto.body)
}

fn stabilize_block(block: &mut HirBlock) -> bool {
    let mut changed = false;

    for stmt in &mut block.stmts {
        changed |= stabilize_nested(stmt);
    }

    let mut index = 0;
    while index < block.stmts.len() {
        let Some((binding, seed_ctor)) = constructor_seed(&block.stmts[index]) else {
            index += 1;
            continue;
        };

        let Some((rebuilt_ctor, end_index)) =
            try_rebuild_constructor_region(block, index, binding, seed_ctor)
        else {
            index += 1;
            continue;
        };

        install_constructor_seed(&mut block.stmts[index], rebuilt_ctor);
        block.stmts.drain(index + 1..=end_index);
        changed = true;
        index += 1;
    }

    changed
}

fn stabilize_nested(stmt: &mut HirStmt) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            let mut changed = stabilize_block(&mut if_stmt.then_block);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= stabilize_block(else_block);
            }
            changed
        }
        HirStmt::While(while_stmt) => stabilize_block(&mut while_stmt.body),
        HirStmt::Repeat(repeat_stmt) => stabilize_block(&mut repeat_stmt.body),
        HirStmt::NumericFor(numeric_for) => stabilize_block(&mut numeric_for.body),
        HirStmt::GenericFor(generic_for) => stabilize_block(&mut generic_for.body),
        HirStmt::Block(block) => stabilize_block(block),
        HirStmt::Unstructured(unstructured) => stabilize_block(&mut unstructured.body),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn constructor_seed(stmt: &HirStmt) -> Option<(TableBinding, HirTableConstructor)> {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            let [binding] = local_decl.bindings.as_slice() else {
                return None;
            };
            let [HirExpr::TableConstructor(table)] = local_decl.values.as_slice() else {
                return None;
            };
            Some((TableBinding::Local(*binding), (**table).clone()))
        }
        HirStmt::Assign(assign) => {
            let [target] = assign.targets.as_slice() else {
                return None;
            };
            let binding = binding_from_lvalue(target)?;
            let [HirExpr::TableConstructor(table)] = assign.values.as_slice() else {
                return None;
            };
            Some((binding, (**table).clone()))
        }
        _ => None,
    }
}

fn install_constructor_seed(stmt: &mut HirStmt, constructor: HirTableConstructor) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            local_decl.values = vec![HirExpr::TableConstructor(Box::new(constructor))];
        }
        HirStmt::Assign(assign) => {
            assign.values = vec![HirExpr::TableConstructor(Box::new(constructor))];
        }
        _ => unreachable!("constructor region must start from a constructor seed"),
    }
}

fn try_rebuild_constructor_region(
    block: &HirBlock,
    seed_index: usize,
    binding: TableBinding,
    constructor: HirTableConstructor,
) -> Option<(HirTableConstructor, usize)> {
    let mut steps = Vec::new();
    let mut index = seed_index + 1;

    while let Some(stmt) = block.stmts.get(index) {
        if let Some(record) = keyed_write_step(stmt, binding) {
            steps.push(RegionStep::Record(record));
            index += 1;
            continue;
        }
        if let Some(producer) = simple_value_producer_step(stmt, binding) {
            steps.push(producer);
            index += 1;
            continue;
        }
        if let Some(set_list) = table_set_list_step(stmt, binding) {
            steps.push(RegionStep::SetList(set_list));
            return rebuild_constructor_from_steps(constructor, &steps, &block.stmts[index + 1..])
                .map(|constructor| (constructor, index));
        }
        break;
    }

    if steps.is_empty() {
        None
    } else {
        rebuild_record_only_constructor(constructor, &steps, &block.stmts[index..])
            .map(|constructor| (constructor, index.saturating_sub(1)))
    }
}

fn keyed_write_step(
    stmt: &HirStmt,
    binding: TableBinding,
) -> Option<crate::hir::common::HirRecordField> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    if binding_from_expr(&access.base) != Some(binding) {
        return None;
    }
    if expr_uses_binding(&access.key, binding) || expr_uses_binding(value, binding) {
        return None;
    }
    Some(crate::hir::common::HirRecordField {
        key: table_key_from_expr(&access.key),
        value: value.clone(),
    })
}

fn simple_value_producer_step(
    stmt: &HirStmt,
    constructor_binding: TableBinding,
) -> Option<RegionStep> {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            let [binding] = local_decl.bindings.as_slice() else {
                return None;
            };
            let [value] = local_decl.values.as_slice() else {
                return None;
            };
            if expr_uses_binding(value, constructor_binding) {
                return None;
            }
            Some(RegionStep::Producer(
                TableBinding::Local(*binding),
                value.clone(),
            ))
        }
        HirStmt::Assign(assign) => {
            let [target] = assign.targets.as_slice() else {
                return None;
            };
            let binding = binding_from_lvalue(target)?;
            let [value] = assign.values.as_slice() else {
                return None;
            };
            if expr_uses_binding(value, constructor_binding) {
                return None;
            }
            Some(RegionStep::Producer(binding, value.clone()))
        }
        _ => None,
    }
}

fn table_set_list_step(stmt: &HirStmt, binding: TableBinding) -> Option<HirTableSetList> {
    let HirStmt::TableSetList(set_list) = stmt else {
        return None;
    };
    if binding_from_expr(&set_list.base) != Some(binding) {
        return None;
    }
    if set_list
        .values
        .iter()
        .any(|expr| expr_uses_binding(expr, binding))
        || set_list
            .trailing_multivalue
            .as_ref()
            .is_some_and(|expr| expr_uses_binding(expr, binding))
    {
        return None;
    }
    Some((**set_list).clone())
}

fn rebuild_constructor_from_steps(
    mut constructor: HirTableConstructor,
    steps: &[RegionStep],
    remaining_stmts: &[HirStmt],
) -> Option<HirTableConstructor> {
    let terminal = match steps.last() {
        Some(RegionStep::SetList(set_list)) => set_list,
        _ => return None,
    };
    if terminal.start_index != next_array_index(&constructor) {
        return None;
    }

    let mut pending_fixed = terminal.values.clone();
    let mut pending_producers = Vec::<(TableBinding, HirExpr)>::new();
    let mut consumed = std::collections::BTreeSet::new();

    for step in steps {
        match step {
            RegionStep::Producer(binding, value) => {
                pending_producers.push((*binding, value.clone()));
                if pending_fixed
                    .first()
                    .is_some_and(|first| matches_binding_ref(first, *binding))
                {
                    if stmt_slice_uses_binding(remaining_stmts, *binding) {
                        return None;
                    }
                    constructor.fields.push(HirTableField::Array(value.clone()));
                    pending_fixed.remove(0);
                    consumed.insert(*binding);
                }
            }
            RegionStep::Record(field) => {
                let value = inline_record_value(
                    &field.value,
                    &pending_producers,
                    &mut consumed,
                    remaining_stmts,
                )?;
                constructor.fields.push(HirTableField::Record(
                    crate::hir::common::HirRecordField {
                        key: field.key.clone(),
                        value,
                    },
                ));
            }
            RegionStep::SetList(set_list) => {
                for value in &pending_fixed {
                    if expr_depends_on_any_binding(
                        value,
                        &pending_producers
                            .iter()
                            .filter(|(binding, _)| !consumed.contains(binding))
                            .map(|(binding, _)| *binding)
                            .collect::<Vec<_>>(),
                    ) {
                        return None;
                    }
                    constructor.fields.push(HirTableField::Array(value.clone()));
                }
                if let Some(trailing) = &set_list.trailing_multivalue {
                    if expr_depends_on_any_binding(
                        trailing,
                        &pending_producers
                            .iter()
                            .filter(|(binding, _)| !consumed.contains(binding))
                            .map(|(binding, _)| *binding)
                            .collect::<Vec<_>>(),
                    ) {
                        return None;
                    }
                    constructor.trailing_multivalue = Some(trailing.clone());
                }
            }
        }
    }

    if pending_producers
        .iter()
        .any(|(binding, _)| !consumed.contains(binding))
    {
        return None;
    }

    Some(constructor)
}

fn rebuild_record_only_constructor(
    mut constructor: HirTableConstructor,
    steps: &[RegionStep],
    remaining_stmts: &[HirStmt],
) -> Option<HirTableConstructor> {
    let mut pending_producers = Vec::<(TableBinding, HirExpr)>::new();
    let mut consumed = std::collections::BTreeSet::new();

    for step in steps {
        match step {
            RegionStep::Producer(binding, value) => {
                pending_producers.push((*binding, value.clone()));
            }
            RegionStep::Record(field) => {
                let value = inline_record_value(
                    &field.value,
                    &pending_producers,
                    &mut consumed,
                    remaining_stmts,
                )?;
                constructor.fields.push(HirTableField::Record(
                    crate::hir::common::HirRecordField {
                        key: field.key.clone(),
                        value,
                    },
                ));
            }
            RegionStep::SetList(_) => return None,
        }
    }

    if pending_producers
        .iter()
        .any(|(binding, _)| !consumed.contains(binding))
    {
        return None;
    }

    Some(constructor)
}

fn next_array_index(constructor: &HirTableConstructor) -> u32 {
    constructor
        .fields
        .iter()
        .filter(|field| matches!(field, HirTableField::Array(_)))
        .count() as u32
        + 1
}

fn binding_from_lvalue(lvalue: &HirLValue) -> Option<TableBinding> {
    match lvalue {
        HirLValue::Temp(temp) => Some(TableBinding::Temp(*temp)),
        HirLValue::Local(local) => Some(TableBinding::Local(*local)),
        HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => None,
    }
}

fn binding_from_expr(expr: &HirExpr) -> Option<TableBinding> {
    match expr {
        HirExpr::TempRef(temp) => Some(TableBinding::Temp(*temp)),
        HirExpr::LocalRef(local) => Some(TableBinding::Local(*local)),
        _ => None,
    }
}

fn matches_binding_ref(expr: &HirExpr, binding: TableBinding) -> bool {
    binding_from_expr(expr) == Some(binding)
}

fn table_key_from_expr(expr: &HirExpr) -> HirTableKey {
    if let HirExpr::String(name) = expr
        && is_identifier_name(name)
    {
        return HirTableKey::Name(name.clone());
    }
    HirTableKey::Expr(expr.clone())
}

fn is_identifier_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn stmt_slice_uses_binding(stmts: &[HirStmt], binding: TableBinding) -> bool {
    stmts.iter().any(|stmt| stmt_uses_binding(stmt, binding))
}

fn inline_record_value(
    value: &HirExpr,
    pending_producers: &[(TableBinding, HirExpr)],
    consumed: &mut std::collections::BTreeSet<TableBinding>,
    remaining_stmts: &[HirStmt],
) -> Option<HirExpr> {
    for (binding, producer_value) in pending_producers {
        if matches_binding_ref(value, *binding) {
            if stmt_slice_uses_binding(remaining_stmts, *binding) {
                return None;
            }
            consumed.insert(*binding);
            return Some(producer_value.clone());
        }
    }

    if expr_depends_on_any_binding(
        value,
        &pending_producers
            .iter()
            .filter(|(binding, _)| !consumed.contains(binding))
            .map(|(binding, _)| *binding)
            .collect::<Vec<_>>(),
    ) {
        None
    } else {
        Some(value.clone())
    }
}

fn stmt_uses_binding(stmt: &HirStmt, binding: TableBinding) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|expr| expr_uses_binding(expr, binding)),
        HirStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| lvalue_uses_binding(target, binding))
                || assign
                    .values
                    .iter()
                    .any(|expr| expr_uses_binding(expr, binding))
        }
        HirStmt::TableSetList(set_list) => {
            expr_uses_binding(&set_list.base, binding)
                || set_list
                    .values
                    .iter()
                    .any(|expr| expr_uses_binding(expr, binding))
                || set_list
                    .trailing_multivalue
                    .as_ref()
                    .is_some_and(|expr| expr_uses_binding(expr, binding))
        }
        HirStmt::CallStmt(call_stmt) => call_expr_uses_binding(&call_stmt.call, binding),
        HirStmt::Return(ret) => ret
            .values
            .iter()
            .any(|expr| expr_uses_binding(expr, binding)),
        HirStmt::If(if_stmt) => {
            expr_uses_binding(&if_stmt.cond, binding)
                || stmt_slice_uses_binding(&if_stmt.then_block.stmts, binding)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| stmt_slice_uses_binding(&block.stmts, binding))
        }
        HirStmt::While(while_stmt) => {
            expr_uses_binding(&while_stmt.cond, binding)
                || stmt_slice_uses_binding(&while_stmt.body.stmts, binding)
        }
        HirStmt::Repeat(repeat_stmt) => {
            stmt_slice_uses_binding(&repeat_stmt.body.stmts, binding)
                || expr_uses_binding(&repeat_stmt.cond, binding)
        }
        HirStmt::NumericFor(numeric_for) => {
            expr_uses_binding(&numeric_for.start, binding)
                || expr_uses_binding(&numeric_for.limit, binding)
                || expr_uses_binding(&numeric_for.step, binding)
                || stmt_slice_uses_binding(&numeric_for.body.stmts, binding)
        }
        HirStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .any(|expr| expr_uses_binding(expr, binding))
                || stmt_slice_uses_binding(&generic_for.body.stmts, binding)
        }
        HirStmt::Block(block) => stmt_slice_uses_binding(&block.stmts, binding),
        HirStmt::Unstructured(unstructured) => {
            stmt_slice_uses_binding(&unstructured.body.stmts, binding)
        }
        HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_) => false,
    }
}

fn call_expr_uses_binding(call: &crate::hir::common::HirCallExpr, binding: TableBinding) -> bool {
    expr_uses_binding(&call.callee, binding)
        || call.args.iter().any(|arg| expr_uses_binding(arg, binding))
}

fn lvalue_uses_binding(lvalue: &HirLValue, binding: TableBinding) -> bool {
    match lvalue {
        HirLValue::Temp(temp) => binding == TableBinding::Temp(*temp),
        HirLValue::Local(local) => binding == TableBinding::Local(*local),
        HirLValue::TableAccess(access) => {
            expr_uses_binding(&access.base, binding) || expr_uses_binding(&access.key, binding)
        }
        HirLValue::Upvalue(_) | HirLValue::Global(_) => false,
    }
}

fn expr_depends_on_any_binding(expr: &HirExpr, bindings: &[TableBinding]) -> bool {
    bindings
        .iter()
        .any(|binding| expr_uses_binding(expr, *binding))
}

fn expr_uses_binding(expr: &HirExpr, binding: TableBinding) -> bool {
    if matches_binding_ref(expr, binding) {
        return true;
    }

    match expr {
        HirExpr::TableAccess(access) => {
            expr_uses_binding(&access.base, binding) || expr_uses_binding(&access.key, binding)
        }
        HirExpr::Unary(unary) => expr_uses_binding(&unary.expr, binding),
        HirExpr::Binary(binary) => {
            expr_uses_binding(&binary.lhs, binding) || expr_uses_binding(&binary.rhs, binding)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_uses_binding(&logical.lhs, binding) || expr_uses_binding(&logical.rhs, binding)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_uses_binding(&node.test, binding)
                || decision_target_uses_binding(&node.truthy, binding)
                || decision_target_uses_binding(&node.falsy, binding)
        }),
        HirExpr::Call(call) => call_expr_uses_binding(call, binding),
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                HirTableField::Array(expr) => expr_uses_binding(expr, binding),
                HirTableField::Record(field) => {
                    table_key_uses_binding(&field.key, binding)
                        || expr_uses_binding(&field.value, binding)
                }
            }) || table
                .trailing_multivalue
                .as_ref()
                .is_some_and(|expr| expr_uses_binding(expr, binding))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_uses_binding(&capture.value, binding)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::ParamRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
        HirExpr::TempRef(_) | HirExpr::LocalRef(_) => false,
    }
}

fn decision_target_uses_binding(
    target: &crate::hir::common::HirDecisionTarget,
    binding: TableBinding,
) -> bool {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => expr_uses_binding(expr, binding),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => false,
    }
}

fn table_key_uses_binding(key: &HirTableKey, binding: TableBinding) -> bool {
    match key {
        HirTableKey::Name(_) => false,
        HirTableKey::Expr(expr) => expr_uses_binding(expr, binding),
    }
}
