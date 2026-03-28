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
    ProducerGroup(ProducerGroup),
    Record(crate::hir::common::HirRecordField),
    SetList(HirTableSetList),
}

#[derive(Debug, Clone)]
struct ProducerGroup {
    slots: Vec<ProducerGroupSlot>,
    drop_without_consumption_is_safe: bool,
}

#[derive(Debug, Clone)]
struct ProducerGroupSlot {
    binding: TableBinding,
    value: Option<HirExpr>,
}

#[derive(Debug, Clone)]
struct PendingProducer {
    binding: TableBinding,
    value: Option<HirExpr>,
    group: Option<usize>,
}

#[derive(Debug, Clone, Copy)]
struct ProducerGroupMeta {
    drop_without_consumption_is_safe: bool,
}

#[derive(Debug, Clone)]
enum SegmentToken {
    Producer(TableBinding),
    Record(crate::hir::common::HirRecordField),
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
        debug_assert!(
            end_index > index,
            "constructor rewrite must consume at least one trailing stmt"
        );
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
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
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
    let mut best = None;

    while let Some(stmt) = block.stmts.get(index) {
        if let Some(record) = keyed_write_step(stmt, binding) {
            steps.push(RegionStep::Record(record));
            if let Some(rebuilt) = rebuild_constructor_from_steps(
                constructor.clone(),
                &steps,
                &block.stmts[index + 1..],
            ) {
                best = Some((rebuilt, index));
            }
            index += 1;
            continue;
        }
        if let Some(mut producers) = producer_steps(stmt, binding) {
            steps.append(&mut producers);
            index += 1;
            continue;
        }
        if let Some(set_list) = table_set_list_step(stmt, binding) {
            steps.push(RegionStep::SetList(set_list));
            if let Some(rebuilt) = rebuild_constructor_from_steps(
                constructor.clone(),
                &steps,
                &block.stmts[index + 1..],
            ) {
                best = Some((rebuilt, index));
            }
            index += 1;
            continue;
        }
        break;
    }

    // 不要求“扫描到的最长前缀”整体可折叠。
    // 某些稳定构造区域后面会紧跟无关的 local producer；如果继续把它们吞进候选区，
    // 末尾那批未消费 producer 会让整段 region 失败，反而错过前面已经足够安全的
    // `{ ... }` 前缀。因此这里持续记住“最后一个成功前缀”，在真正遇到无关语句时
    // 回退到最近一次可证明安全的构造器边界。
    best
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

fn producer_steps(stmt: &HirStmt, constructor_binding: TableBinding) -> Option<Vec<RegionStep>> {
    match stmt {
        HirStmt::LocalDecl(local_decl) => producer_steps_from_bindings(
            local_decl
                .bindings
                .iter()
                .copied()
                .map(TableBinding::Local)
                .collect(),
            &local_decl.values,
            constructor_binding,
        ),
        HirStmt::Assign(assign) => {
            let bindings = assign
                .targets
                .iter()
                .map(binding_from_lvalue)
                .collect::<Option<Vec<_>>>()?;
            producer_steps_from_bindings(bindings, &assign.values, constructor_binding)
        }
        _ => None,
    }
}

fn producer_steps_from_bindings(
    bindings: Vec<TableBinding>,
    values: &[HirExpr],
    constructor_binding: TableBinding,
) -> Option<Vec<RegionStep>> {
    if bindings.is_empty()
        || values.is_empty()
        || values
            .iter()
            .any(|value| expr_uses_binding(value, constructor_binding))
    {
        return None;
    }

    if bindings.len() == values.len() {
        return Some(
            bindings
                .into_iter()
                .zip(values.iter().cloned())
                .map(|(binding, value)| RegionStep::Producer(binding, value))
                .collect(),
        );
    }

    let [source] = values else {
        return None;
    };
    if bindings.len() > 1 && is_open_pack_source(source) {
        return Some(vec![RegionStep::ProducerGroup(ProducerGroup {
            slots: bindings
                .into_iter()
                .enumerate()
                .map(|(index, binding)| ProducerGroupSlot {
                    binding,
                    value: (index == 0).then_some(source.clone()),
                })
                .collect(),
            drop_without_consumption_is_safe: can_drop_open_pack_source_if_unused(source),
        })]);
    }

    None
}

fn is_open_pack_source(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::VarArg) || matches!(expr, HirExpr::Call(call) if call.multiret)
}

fn can_drop_open_pack_source_if_unused(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::VarArg)
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
    let remaining_uses = collect_stmt_slice_bindings(remaining_stmts);
    let region_contains_set_list = steps
        .iter()
        .any(|step| matches!(step, RegionStep::SetList(_)));
    let mut pending_segment = Vec::new();

    for step in steps {
        match step {
            RegionStep::Producer(_, _) | RegionStep::ProducerGroup(_) | RegionStep::Record(_) => {
                pending_segment.push(step.clone())
            }
            RegionStep::SetList(set_list) => {
                flush_constructor_segment(
                    &mut constructor,
                    &pending_segment,
                    Some(set_list),
                    &remaining_uses,
                    region_contains_set_list,
                )?;
                pending_segment.clear();
            }
        }
    }

    flush_constructor_segment(
        &mut constructor,
        &pending_segment,
        None,
        &remaining_uses,
        region_contains_set_list,
    )?;

    Some(constructor)
}

fn flush_constructor_segment(
    constructor: &mut HirTableConstructor,
    segment: &[RegionStep],
    set_list: Option<&HirTableSetList>,
    remaining_uses: &std::collections::BTreeSet<TableBinding>,
    allow_closure_records: bool,
) -> Option<()> {
    if segment.is_empty() {
        normalize_sequential_integer_record_fields(constructor);
        if let Some(set_list) = set_list {
            if set_list.start_index != next_array_index(constructor) {
                return None;
            }
            for value in &set_list.values {
                constructor.fields.push(HirTableField::Array(value.clone()));
            }
            if let Some(trailing) = &set_list.trailing_multivalue {
                constructor.trailing_multivalue = Some(trailing.clone());
            }
        }
        return Some(());
    }

    let mut producer_values = Vec::<PendingProducer>::new();
    let mut producer_groups = Vec::<ProducerGroupMeta>::new();
    let mut tokens = Vec::<SegmentToken>::new();
    let mut consumed = std::collections::BTreeSet::new();
    let mut consumed_groups = std::collections::BTreeSet::new();

    for step in segment {
        match step {
            RegionStep::Producer(binding, value) => {
                producer_values.push(PendingProducer {
                    binding: *binding,
                    value: Some(value.clone()),
                    group: None,
                });
                tokens.push(SegmentToken::Producer(*binding));
            }
            RegionStep::ProducerGroup(group) => {
                let group_id = producer_groups.len();
                producer_groups.push(ProducerGroupMeta {
                    drop_without_consumption_is_safe: group.drop_without_consumption_is_safe,
                });
                for slot in &group.slots {
                    producer_values.push(PendingProducer {
                        binding: slot.binding,
                        value: slot.value.clone(),
                        group: Some(group_id),
                    });
                    tokens.push(SegmentToken::Producer(slot.binding));
                }
            }
            RegionStep::Record(field) => {
                let value = inline_constructor_value(
                    &field.value,
                    &producer_values,
                    &mut consumed,
                    &mut consumed_groups,
                    remaining_uses,
                )?;
                // 只有能证明这段 region 还处在字面量初始化 flush 里时，才允许继续吸收
                // `field = function() ... end`。如果整段根本没有 `SETLIST`，这类 closure
                // 赋值更像“先建表、再挂方法”，需要把结构机会留给后续 method sugar。
                if matches!(value, HirExpr::Closure(_)) && !allow_closure_records {
                    return None;
                }
                tokens.push(SegmentToken::Record(crate::hir::common::HirRecordField {
                    key: field.key.clone(),
                    value,
                }));
            }
            RegionStep::SetList(_) => unreachable!("set-list should terminate constructor segment"),
        }
    }

    if let Some(set_list) = set_list {
        if set_list.start_index != next_array_index(constructor) {
            return None;
        }

        let mut queued_values = std::collections::VecDeque::from(set_list.values.clone());
        for token in tokens {
            match token {
                SegmentToken::Producer(binding) => {
                    if consumed.contains(&binding) {
                        continue;
                    }
                    match queued_values.front() {
                        Some(front) if matches_binding_ref(front, binding) => {
                            let Some(producer_value) =
                                producer_value_for_binding(&producer_values, binding)
                            else {
                                return None;
                            };
                            if remaining_uses.contains(&binding) {
                                return None;
                            }
                            consumed.insert(binding);
                            queued_values.pop_front();
                            constructor
                                .fields
                                .push(HirTableField::Array(producer_value.clone()));
                        }
                        Some(_)
                            if queued_values
                                .iter()
                                .any(|value| matches_binding_ref(value, binding)) =>
                        {
                            // Lua 编译器为构造器批量刷出的 `SETLIST` 顺序和源码数组项顺序一致。
                            // 如果 producer 在 token 序里出现得更早，却在 set-list 队列里更晚，
                            // 说明这段 region 已经不是我们能稳定证明的字面量顺序。
                            return None;
                        }
                        _ => {}
                    }
                }
                SegmentToken::Record(field) => {
                    push_constructor_field(constructor, field);
                }
            }
        }

        for value in queued_values {
            let value = inline_constructor_value(
                &value,
                &producer_values,
                &mut consumed,
                &mut consumed_groups,
                remaining_uses,
            )?;
            constructor.fields.push(HirTableField::Array(value));
        }

        if let Some(trailing) = &set_list.trailing_multivalue {
            let trailing = inline_constructor_value(
                trailing,
                &producer_values,
                &mut consumed,
                &mut consumed_groups,
                remaining_uses,
            )?;
            constructor.trailing_multivalue = Some(trailing);
        }
    } else {
        for token in tokens {
            match token {
                SegmentToken::Producer(binding) if !consumed.contains(&binding) => return None,
                SegmentToken::Producer(_) => {}
                SegmentToken::Record(field) => {
                    push_constructor_field(constructor, field);
                }
            }
        }
        normalize_sequential_integer_record_fields(constructor);
    }

    if producer_values.iter().any(|producer| {
        if consumed.contains(&producer.binding) {
            return false;
        }
        if remaining_uses.contains(&producer.binding) {
            return true;
        }
        match producer.group {
            Some(group) if consumed_groups.contains(&group) => false,
            Some(group) => !producer_groups[group].drop_without_consumption_is_safe,
            None => true,
        }
    }) {
        return None;
    }

    Some(())
}

fn next_array_index(constructor: &HirTableConstructor) -> u32 {
    constructor
        .fields
        .iter()
        .filter(|field| matches!(field, HirTableField::Array(_)))
        .count() as u32
        + 1
}

fn push_constructor_field(
    constructor: &mut HirTableConstructor,
    field: crate::hir::common::HirRecordField,
) {
    let next_index = i64::from(next_array_index(constructor));
    match &field.key {
        HirTableKey::Expr(HirExpr::Integer(value)) if *value == next_index => {
            constructor.fields.push(HirTableField::Array(field.value));
        }
        _ => constructor.fields.push(HirTableField::Record(field)),
    }
}

fn normalize_sequential_integer_record_fields(constructor: &mut HirTableConstructor) {
    loop {
        let next_index = i64::from(next_array_index(constructor));
        let Some(record_index) = constructor.fields.iter().position(|field| {
            let HirTableField::Record(field) = field else {
                return false;
            };
            matches!(&field.key, HirTableKey::Expr(HirExpr::Integer(value)) if *value == next_index)
                && can_reorder_integer_record_value(&field.value)
        }) else {
            break;
        };
        let HirTableField::Record(field) = constructor.fields.remove(record_index) else {
            unreachable!("record field position was validated above");
        };
        constructor.fields.push(HirTableField::Array(field.value));
    }
}

fn can_reorder_integer_record_value(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::Closure(_) => true,
        HirExpr::Unary(unary) => can_reorder_integer_record_value(&unary.expr),
        HirExpr::Binary(binary) => {
            can_reorder_integer_record_value(&binary.lhs)
                && can_reorder_integer_record_value(&binary.rhs)
        }
        _ => false,
    }
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

fn collect_stmt_slice_bindings(stmts: &[HirStmt]) -> std::collections::BTreeSet<TableBinding> {
    let mut bindings = std::collections::BTreeSet::new();
    for stmt in stmts {
        collect_stmt_bindings(stmt, &mut bindings);
    }
    bindings
}

fn collect_stmt_bindings(stmt: &HirStmt, bindings: &mut std::collections::BTreeSet<TableBinding>) {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_expr_bindings(value, bindings);
            }
        }
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_bindings(target, bindings);
            }
            for value in &assign.values {
                collect_expr_bindings(value, bindings);
            }
        }
        HirStmt::TableSetList(set_list) => {
            collect_expr_bindings(&set_list.base, bindings);
            for value in &set_list.values {
                collect_expr_bindings(value, bindings);
            }
            if let Some(trailing) = &set_list.trailing_multivalue {
                collect_expr_bindings(trailing, bindings);
            }
        }
        HirStmt::ErrNil(err_nil) => {
            collect_expr_bindings(&err_nil.value, bindings);
        }
        HirStmt::ToBeClosed(to_be_closed) => {
            collect_expr_bindings(&to_be_closed.value, bindings);
        }
        HirStmt::CallStmt(call_stmt) => collect_call_bindings(&call_stmt.call, bindings),
        HirStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_bindings(value, bindings);
            }
        }
        HirStmt::If(if_stmt) => {
            collect_expr_bindings(&if_stmt.cond, bindings);
            collect_stmt_slice_bindings_into(&if_stmt.then_block.stmts, bindings);
            if let Some(else_block) = &if_stmt.else_block {
                collect_stmt_slice_bindings_into(&else_block.stmts, bindings);
            }
        }
        HirStmt::While(while_stmt) => {
            collect_expr_bindings(&while_stmt.cond, bindings);
            collect_stmt_slice_bindings_into(&while_stmt.body.stmts, bindings);
        }
        HirStmt::Repeat(repeat_stmt) => {
            collect_stmt_slice_bindings_into(&repeat_stmt.body.stmts, bindings);
            collect_expr_bindings(&repeat_stmt.cond, bindings);
        }
        HirStmt::NumericFor(numeric_for) => {
            collect_expr_bindings(&numeric_for.start, bindings);
            collect_expr_bindings(&numeric_for.limit, bindings);
            collect_expr_bindings(&numeric_for.step, bindings);
            collect_stmt_slice_bindings_into(&numeric_for.body.stmts, bindings);
        }
        HirStmt::GenericFor(generic_for) => {
            for value in &generic_for.iterator {
                collect_expr_bindings(value, bindings);
            }
            collect_stmt_slice_bindings_into(&generic_for.body.stmts, bindings);
        }
        HirStmt::Block(block) => collect_stmt_slice_bindings_into(&block.stmts, bindings),
        HirStmt::Unstructured(unstructured) => {
            collect_stmt_slice_bindings_into(&unstructured.body.stmts, bindings);
        }
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
}

fn collect_stmt_slice_bindings_into(
    stmts: &[HirStmt],
    bindings: &mut std::collections::BTreeSet<TableBinding>,
) {
    for stmt in stmts {
        collect_stmt_bindings(stmt, bindings);
    }
}

fn collect_lvalue_bindings(
    lvalue: &HirLValue,
    bindings: &mut std::collections::BTreeSet<TableBinding>,
) {
    match lvalue {
        HirLValue::Temp(temp) => {
            bindings.insert(TableBinding::Temp(*temp));
        }
        HirLValue::Local(local) => {
            bindings.insert(TableBinding::Local(*local));
        }
        HirLValue::TableAccess(access) => {
            collect_expr_bindings(&access.base, bindings);
            collect_expr_bindings(&access.key, bindings);
        }
        HirLValue::Upvalue(_) | HirLValue::Global(_) => {}
    }
}

fn collect_call_bindings(
    call: &crate::hir::common::HirCallExpr,
    bindings: &mut std::collections::BTreeSet<TableBinding>,
) {
    collect_expr_bindings(&call.callee, bindings);
    for arg in &call.args {
        collect_expr_bindings(arg, bindings);
    }
}

fn collect_expr_bindings(expr: &HirExpr, bindings: &mut std::collections::BTreeSet<TableBinding>) {
    if let Some(binding) = binding_from_expr(expr) {
        bindings.insert(binding);
        return;
    }

    match expr {
        HirExpr::TableAccess(access) => {
            collect_expr_bindings(&access.base, bindings);
            collect_expr_bindings(&access.key, bindings);
        }
        HirExpr::Unary(unary) => collect_expr_bindings(&unary.expr, bindings),
        HirExpr::Binary(binary) => {
            collect_expr_bindings(&binary.lhs, bindings);
            collect_expr_bindings(&binary.rhs, bindings);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            collect_expr_bindings(&logical.lhs, bindings);
            collect_expr_bindings(&logical.rhs, bindings);
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                collect_expr_bindings(&node.test, bindings);
                collect_decision_target_bindings(&node.truthy, bindings);
                collect_decision_target_bindings(&node.falsy, bindings);
            }
        }
        HirExpr::Call(call) => collect_call_bindings(call, bindings),
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(expr) => collect_expr_bindings(expr, bindings),
                    HirTableField::Record(field) => {
                        collect_table_key_bindings(&field.key, bindings);
                        collect_expr_bindings(&field.value, bindings);
                    }
                }
            }
            if let Some(trailing) = &table.trailing_multivalue {
                collect_expr_bindings(trailing, bindings);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                collect_expr_bindings(&capture.value, bindings);
            }
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
        HirExpr::LocalRef(_) | HirExpr::TempRef(_) => {}
    }
}

fn collect_decision_target_bindings(
    target: &crate::hir::common::HirDecisionTarget,
    bindings: &mut std::collections::BTreeSet<TableBinding>,
) {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => collect_expr_bindings(expr, bindings),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => {}
    }
}

fn collect_table_key_bindings(
    key: &HirTableKey,
    bindings: &mut std::collections::BTreeSet<TableBinding>,
) {
    if let HirTableKey::Expr(expr) = key {
        collect_expr_bindings(expr, bindings);
    }
}

fn inline_constructor_value(
    value: &HirExpr,
    pending_producers: &[PendingProducer],
    consumed: &mut std::collections::BTreeSet<TableBinding>,
    consumed_groups: &mut std::collections::BTreeSet<usize>,
    remaining_uses: &std::collections::BTreeSet<TableBinding>,
) -> Option<HirExpr> {
    inline_constructor_value_at_site(
        value,
        pending_producers,
        consumed,
        consumed_groups,
        remaining_uses,
        ConstructorInlineSite::Neutral,
    )
}

#[derive(Clone, Copy)]
enum ConstructorInlineSite {
    Neutral,
    CallCallee,
    AccessBase,
}

fn inline_constructor_value_at_site(
    value: &HirExpr,
    pending_producers: &[PendingProducer],
    consumed: &mut std::collections::BTreeSet<TableBinding>,
    consumed_groups: &mut std::collections::BTreeSet<usize>,
    remaining_uses: &std::collections::BTreeSet<TableBinding>,
    site: ConstructorInlineSite,
) -> Option<HirExpr> {
    for producer in pending_producers {
        if matches_binding_ref(value, producer.binding) {
            if remaining_uses.contains(&producer.binding) {
                return None;
            }
            let producer_value = producer.value.as_ref()?;
            if !matches!(site, ConstructorInlineSite::Neutral)
                && !is_constructor_access_base_inline_expr(producer_value)
            {
                return None;
            }
            consumed.insert(producer.binding);
            if let Some(group) = producer.group {
                consumed_groups.insert(group);
            }
            return Some(producer_value.clone());
        }
    }

    match value {
        HirExpr::TableAccess(access) => {
            return Some(HirExpr::TableAccess(Box::new(
                crate::hir::common::HirTableAccess {
                    base: inline_constructor_value_at_site(
                        &access.base,
                        pending_producers,
                        consumed,
                        consumed_groups,
                        remaining_uses,
                        ConstructorInlineSite::AccessBase,
                    )?,
                    key: inline_constructor_value_at_site(
                        &access.key,
                        pending_producers,
                        consumed,
                        consumed_groups,
                        remaining_uses,
                        ConstructorInlineSite::Neutral,
                    )?,
                },
            )));
        }
        HirExpr::Call(call) => {
            return Some(HirExpr::Call(Box::new(crate::hir::common::HirCallExpr {
                callee: inline_constructor_value_at_site(
                    &call.callee,
                    pending_producers,
                    consumed,
                    consumed_groups,
                    remaining_uses,
                    ConstructorInlineSite::CallCallee,
                )?,
                args: call
                    .args
                    .iter()
                    .map(|arg| {
                        inline_constructor_value_at_site(
                            arg,
                            pending_producers,
                            consumed,
                            consumed_groups,
                            remaining_uses,
                            ConstructorInlineSite::Neutral,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?,
                multiret: call.multiret,
                method: call.method,
            })));
        }
        _ => {}
    }

    if expr_depends_on_any_binding(
        value,
        &pending_producers
            .iter()
            .filter(|producer| !consumed.contains(&producer.binding))
            .map(|producer| producer.binding)
            .collect::<Vec<_>>(),
    ) {
        return None;
    } else {
        Some(value.clone())
    }
}

fn is_constructor_access_base_inline_expr(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_) => true,
        HirExpr::TableAccess(access) => is_constructor_access_base_inline_expr(&access.base),
        _ => false,
    }
}

fn producer_value_for_binding(
    producers: &[PendingProducer],
    binding: TableBinding,
) -> Option<&HirExpr> {
    producers.iter().find_map(|producer| {
        (producer.binding == binding)
            .then_some(producer.value.as_ref())
            .flatten()
    })
}

fn call_expr_uses_binding(call: &crate::hir::common::HirCallExpr, binding: TableBinding) -> bool {
    expr_uses_binding(&call.callee, binding)
        || call.args.iter().any(|arg| expr_uses_binding(arg, binding))
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
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
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

#[cfg(test)]
mod tests;
