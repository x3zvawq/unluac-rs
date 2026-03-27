//! 函数声明相关的 readability sugar。

use std::collections::BTreeSet;

use super::super::common::{
    AstAssign, AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionDecl, AstFunctionExpr,
    AstFunctionName, AstGlobalBindingTarget, AstGlobalDecl, AstLValue, AstLocalAttr, AstLocalDecl,
    AstLocalFunctionDecl, AstModule, AstNamePath, AstNameRef, AstStmt, AstTableField, AstTableKey,
    AstTargetDialect,
};
use super::ReadabilityContext;

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let method_fields = collect_method_field_names(module);
    rewrite_block(&mut module.body, context.target, &method_fields)
}

fn rewrite_block(
    block: &mut AstBlock,
    target: AstTargetDialect,
    method_fields: &BTreeSet<String>,
) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= rewrite_nested(stmt, target, method_fields);
    }

    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut index = 0;
    while index < old_stmts.len() {
        if let Some((stmt, consumed)) =
            try_inline_terminal_constructor_call(&old_stmts[index..], method_fields)
        {
            new_stmts.push(stmt);
            changed = true;
            index += consumed;
            continue;
        }

        if let Some((stmt, consumed)) = try_chain_local_method_call_stmt(&old_stmts[index..]) {
            new_stmts.push(stmt);
            changed = true;
            index += consumed;
            continue;
        }

        if let Some((stmt, consumed)) =
            try_lower_forwarded_function_stmt(&old_stmts[index..], target, method_fields)
        {
            new_stmts.push(stmt);
            changed = true;
            index += consumed;
            continue;
        }

        let stmt = lower_direct_function_stmt(old_stmts[index].clone(), target, method_fields);
        changed |= stmt != old_stmts[index];
        new_stmts.push(stmt);
        index += 1;
    }
    block.stmts = new_stmts;
    changed
}

fn rewrite_nested(
    stmt: &mut AstStmt,
    target: AstTargetDialect,
    method_fields: &BTreeSet<String>,
) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            let mut changed = rewrite_block(&mut if_stmt.then_block, target, method_fields);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block, target, method_fields);
            }
            changed |= rewrite_function_exprs_in_expr(&mut if_stmt.cond, target);
            changed
        }
        AstStmt::While(while_stmt) => {
            rewrite_function_exprs_in_expr(&mut while_stmt.cond, target)
                | rewrite_block(&mut while_stmt.body, target, method_fields)
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_block(&mut repeat_stmt.body, target, method_fields)
                | rewrite_function_exprs_in_expr(&mut repeat_stmt.cond, target)
        }
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut numeric_for.start, target);
            changed |= rewrite_function_exprs_in_expr(&mut numeric_for.limit, target);
            changed |= rewrite_function_exprs_in_expr(&mut numeric_for.step, target);
            changed |= rewrite_block(&mut numeric_for.body, target, method_fields);
            changed
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for expr in &mut generic_for.iterator {
                changed |= rewrite_function_exprs_in_expr(expr, target);
            }
            changed |= rewrite_block(&mut generic_for.body, target, method_fields);
            changed
        }
        AstStmt::DoBlock(block) => rewrite_block(block, target, method_fields),
        AstStmt::FunctionDecl(function_decl) => {
            rewrite_function_expr(&mut function_decl.func, target)
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            rewrite_function_expr(&mut local_function_decl.func, target)
        }
        AstStmt::LocalDecl(local_decl) => {
            let mut changed = false;
            for value in &mut local_decl.values {
                changed |= rewrite_function_exprs_in_expr(value, target);
            }
            changed
        }
        AstStmt::GlobalDecl(global_decl) => {
            let mut changed = false;
            for value in &mut global_decl.values {
                changed |= rewrite_function_exprs_in_expr(value, target);
            }
            changed
        }
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target_lvalue in &mut assign.targets {
                changed |= rewrite_function_exprs_in_lvalue(target_lvalue, target);
            }
            for value in &mut assign.values {
                changed |= rewrite_function_exprs_in_expr(value, target);
            }
            changed
        }
        AstStmt::CallStmt(call_stmt) => rewrite_function_exprs_in_call(&mut call_stmt.call, target),
        AstStmt::Return(ret) => {
            let mut changed = false;
            for value in &mut ret.values {
                changed |= rewrite_function_exprs_in_expr(value, target);
            }
            changed
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

fn rewrite_function_expr(function: &mut AstFunctionExpr, target: AstTargetDialect) -> bool {
    let mut method_fields = BTreeSet::new();
    collect_method_field_names_in_block(&function.body, &mut method_fields);
    rewrite_block(&mut function.body, target, &method_fields)
}

fn rewrite_function_exprs_in_call(call: &mut AstCallKind, target: AstTargetDialect) -> bool {
    match call {
        AstCallKind::Call(call) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut call.callee, target);
            for arg in &mut call.args {
                changed |= rewrite_function_exprs_in_expr(arg, target);
            }
            changed
        }
        AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut call.receiver, target);
            for arg in &mut call.args {
                changed |= rewrite_function_exprs_in_expr(arg, target);
            }
            changed
        }
    }
}

fn rewrite_function_exprs_in_lvalue(
    target_lvalue: &mut AstLValue,
    target: AstTargetDialect,
) -> bool {
    match target_lvalue {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => rewrite_function_exprs_in_expr(&mut access.base, target),
        AstLValue::IndexAccess(access) => {
            rewrite_function_exprs_in_expr(&mut access.base, target)
                | rewrite_function_exprs_in_expr(&mut access.index, target)
        }
    }
}

fn rewrite_function_exprs_in_expr(expr: &mut AstExpr, target: AstTargetDialect) -> bool {
    match expr {
        AstExpr::FieldAccess(access) => rewrite_function_exprs_in_expr(&mut access.base, target),
        AstExpr::IndexAccess(access) => {
            rewrite_function_exprs_in_expr(&mut access.base, target)
                | rewrite_function_exprs_in_expr(&mut access.index, target)
        }
        AstExpr::Unary(unary) => rewrite_function_exprs_in_expr(&mut unary.expr, target),
        AstExpr::Binary(binary) => {
            rewrite_function_exprs_in_expr(&mut binary.lhs, target)
                | rewrite_function_exprs_in_expr(&mut binary.rhs, target)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_function_exprs_in_expr(&mut logical.lhs, target)
                | rewrite_function_exprs_in_expr(&mut logical.rhs, target)
        }
        AstExpr::Call(call) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut call.callee, target);
            for arg in &mut call.args {
                changed |= rewrite_function_exprs_in_expr(arg, target);
            }
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut call.receiver, target);
            for arg in &mut call.args {
                changed |= rewrite_function_exprs_in_expr(arg, target);
            }
            changed
        }
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                match field {
                    super::super::common::AstTableField::Array(value) => {
                        changed |= rewrite_function_exprs_in_expr(value, target);
                    }
                    super::super::common::AstTableField::Record(record) => {
                        if let super::super::common::AstTableKey::Expr(key) = &mut record.key {
                            changed |= rewrite_function_exprs_in_expr(key, target);
                        }
                        changed |= rewrite_function_exprs_in_expr(&mut record.value, target);
                    }
                }
            }
            changed
        }
        AstExpr::FunctionExpr(function) => rewrite_function_expr(function, target),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
}

fn lower_direct_function_stmt(
    stmt: AstStmt,
    target: AstTargetDialect,
    method_fields: &BTreeSet<String>,
) -> AstStmt {
    match &stmt {
        AstStmt::LocalDecl(local_decl) => try_lower_local_function_decl((**local_decl).clone()),
        AstStmt::GlobalDecl(global_decl) => {
            try_lower_global_function_decl((**global_decl).clone(), target).unwrap_or(stmt)
        }
        AstStmt::Assign(assign) => {
            try_lower_function_assign((**assign).clone(), method_fields).unwrap_or(stmt)
        }
        _ => stmt,
    }
}

fn try_lower_forwarded_function_stmt(
    stmts: &[AstStmt],
    target: AstTargetDialect,
    method_fields: &BTreeSet<String>,
) -> Option<(AstStmt, usize)> {
    let [AstStmt::LocalDecl(local_decl), next, ..] = stmts else {
        return None;
    };
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    let binding = local_decl.bindings[0].id;
    if local_decl.bindings[0].attr != AstLocalAttr::None {
        return None;
    }
    let AstExpr::FunctionExpr(function) = &local_decl.values[0] else {
        return None;
    };
    // 只有“纯转发”的函数壳才适合被下一条语句吸收。
    // 递归 local function 这类 case 在 AST 函数体里往往已经只剩 `u0` 之类的 upvalue 引用，
    // 直接扫 body 看不到它对当前 binding 槽位的依赖；所以这里优先使用 AST build
    // 带下来的 capture provenance，确认这个局部槽位是不是闭包初始化的一部分。
    if function.captured_bindings.contains(&binding)
        || count_binding_value_uses_in_block(&function.body, binding) != 0
    {
        return None;
    }
    if count_binding_value_uses_in_stmts(&stmts[1..], binding) != 1 {
        return None;
    }
    let function = function.as_ref().clone();
    let stmt = inline_function_into_stmt(next, binding, function, target, method_fields)?;
    Some((stmt, 2))
}

fn try_inline_terminal_constructor_call(
    stmts: &[AstStmt],
    method_fields: &BTreeSet<String>,
) -> Option<(AstStmt, usize)> {
    let (callee_binding, callee_expr) = single_local_alias_decl(stmts.first()?)?;
    let mut consumed = 1usize;
    let mut arg_locals = Vec::<(AstBindingRef, AstExpr)>::new();

    while let Some(stmt) = stmts.get(consumed) {
        let Some((binding, value)) = single_local_alias_decl(stmt) else {
            break;
        };
        arg_locals.push((binding, value.clone()));
        consumed += 1;
    }
    if arg_locals.is_empty() {
        return None;
    }

    while let Some(stmt) = stmts.get(consumed) {
        let AstStmt::FunctionDecl(function_decl) = stmt else {
            break;
        };
        let Some((binding, field, func)) =
            inlineable_table_function_field(function_decl, method_fields)
        else {
            break;
        };
        let (_, table_expr) = arg_locals.iter_mut().find(|(id, _)| *id == binding)?;
        let AstExpr::TableConstructor(table) = table_expr else {
            return None;
        };
        table.fields.push(AstTableField::Record(
            super::super::common::AstRecordField {
                key: AstTableKey::Name(field),
                value: AstExpr::FunctionExpr(Box::new(func)),
            },
        ));
        consumed += 1;
    }

    let AstStmt::Return(ret) = stmts.get(consumed)? else {
        return None;
    };
    let [AstExpr::Call(call)] = ret.values.as_slice() else {
        return None;
    };
    let AstExpr::Var(name) = &call.callee else {
        return None;
    };
    if !name_matches_binding(name, callee_binding) || call.args.len() != arg_locals.len() {
        return None;
    }
    for (arg, (binding, _)) in call.args.iter().zip(arg_locals.iter()) {
        let AstExpr::Var(name) = arg else {
            return None;
        };
        if !name_matches_binding(name, *binding) {
            return None;
        }
    }

    let mut lowered_return = ret.as_ref().clone();
    let AstExpr::Call(lowered_call) = &mut lowered_return.values[0] else {
        unreachable!("matched above")
    };
    lowered_call.callee = callee_expr.clone();
    lowered_call.args = arg_locals
        .into_iter()
        .map(|(_, value)| value)
        .collect::<Vec<_>>();
    Some((AstStmt::Return(Box::new(lowered_return)), consumed + 1))
}

fn single_local_alias_decl(stmt: &AstStmt) -> Option<(AstBindingRef, &AstExpr)> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    if local_decl.bindings[0].attr != AstLocalAttr::None {
        return None;
    }
    Some((local_decl.bindings[0].id, &local_decl.values[0]))
}

fn inlineable_table_function_field(
    function_decl: &AstFunctionDecl,
    method_fields: &BTreeSet<String>,
) -> Option<(AstBindingRef, String, AstFunctionExpr)> {
    let AstFunctionName::Plain(path) = &function_decl.target else {
        return None;
    };
    if path.fields.len() != 1 || method_fields.contains(&path.fields[0]) {
        return None;
    }
    let binding = match &path.root {
        AstNameRef::Local(local) => AstBindingRef::Local(*local),
        AstNameRef::SyntheticLocal(local) => AstBindingRef::SyntheticLocal(*local),
        AstNameRef::Temp(temp) => AstBindingRef::Temp(*temp),
        AstNameRef::Param(_) | AstNameRef::Upvalue(_) | AstNameRef::Global(_) => return None,
    };
    Some((binding, path.fields[0].clone(), function_decl.func.clone()))
}

fn try_lower_local_function_decl(local_decl: AstLocalDecl) -> AstStmt {
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return AstStmt::LocalDecl(Box::new(local_decl));
    }
    let binding = &local_decl.bindings[0];
    if binding.attr != AstLocalAttr::None {
        return AstStmt::LocalDecl(Box::new(local_decl));
    }
    let name = match binding.id {
        AstBindingRef::Local(name) => AstBindingRef::Local(name),
        AstBindingRef::SyntheticLocal(name) => AstBindingRef::SyntheticLocal(name),
        AstBindingRef::Temp(_) => return AstStmt::LocalDecl(Box::new(local_decl)),
    };
    let AstExpr::FunctionExpr(func) = &local_decl.values[0] else {
        return AstStmt::LocalDecl(Box::new(local_decl));
    };
    AstStmt::LocalFunctionDecl(Box::new(AstLocalFunctionDecl {
        name,
        func: func.as_ref().clone(),
    }))
}

fn try_lower_global_function_decl(
    global_decl: AstGlobalDecl,
    target: AstTargetDialect,
) -> Option<AstStmt> {
    if !target.caps.global_decl || global_decl.bindings.len() != 1 || global_decl.values.len() != 1
    {
        return None;
    }
    if global_decl.bindings[0].attr != super::super::common::AstGlobalAttr::None {
        return None;
    }
    let AstGlobalBindingTarget::Name(name) = &global_decl.bindings[0].target else {
        return None;
    };
    let AstExpr::FunctionExpr(func) = &global_decl.values[0] else {
        return None;
    };
    Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
        target: AstFunctionName::Plain(AstNamePath {
            root: AstNameRef::Global(name.clone()),
            fields: Vec::new(),
        }),
        func: func.as_ref().clone(),
    })))
}

fn try_lower_function_assign(
    assign: AstAssign,
    method_fields: &BTreeSet<String>,
) -> Option<AstStmt> {
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return None;
    }
    let AstExpr::FunctionExpr(func) = &assign.values[0] else {
        return None;
    };
    let (target, func) = function_decl_target_from_lvalue(&assign.targets[0], func, method_fields)?;
    Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
        target,
        func,
    })))
}

fn inline_function_into_stmt(
    stmt: &AstStmt,
    binding: AstBindingRef,
    function: AstFunctionExpr,
    target: AstTargetDialect,
    method_fields: &BTreeSet<String>,
) -> Option<AstStmt> {
    match stmt {
        AstStmt::GlobalDecl(global_decl)
            if global_decl.bindings.len() == 1 && global_decl.values.len() == 1 =>
        {
            let AstExpr::Var(name) = &global_decl.values[0] else {
                return None;
            };
            if !name_matches_binding(name, binding) {
                return None;
            }
            if global_decl.bindings[0].attr == super::super::common::AstGlobalAttr::None
                && target.caps.global_decl
            {
                let AstGlobalBindingTarget::Name(name) = &global_decl.bindings[0].target else {
                    return None;
                };
                return Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                    target: AstFunctionName::Plain(AstNamePath {
                        root: AstNameRef::Global(name.clone()),
                        fields: Vec::new(),
                    }),
                    func: function,
                })));
            }

            let mut global_decl = global_decl.as_ref().clone();
            global_decl.values[0] = AstExpr::FunctionExpr(Box::new(function));
            Some(AstStmt::GlobalDecl(Box::new(global_decl)))
        }
        AstStmt::Assign(assign) if assign.targets.len() == 1 && assign.values.len() == 1 => {
            let AstExpr::Var(name) = &assign.values[0] else {
                return None;
            };
            if !name_matches_binding(name, binding) {
                return None;
            }
            if let Some((target_name, function)) =
                function_decl_target_from_lvalue(&assign.targets[0], &function, method_fields)
            {
                return Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                    target: target_name,
                    func: function,
                })));
            }

            let mut assign = assign.as_ref().clone();
            assign.values[0] = AstExpr::FunctionExpr(Box::new(function));
            Some(AstStmt::Assign(Box::new(assign)))
        }
        _ => None,
    }
}

fn try_chain_local_method_call_stmt(stmts: &[AstStmt]) -> Option<(AstStmt, usize)> {
    let [first, second, third, ..] = stmts else {
        return try_chain_local_method_call_stmt_without_dead_alias(stmts);
    };

    let AstStmt::LocalDecl(dead_alias) = first else {
        return try_chain_local_method_call_stmt_without_dead_alias(stmts);
    };
    if dead_alias.bindings.len() != 1
        || dead_alias.values.len() != 1
        || dead_alias.bindings[0].attr != AstLocalAttr::None
    {
        return try_chain_local_method_call_stmt_without_dead_alias(stmts);
    }
    if count_binding_value_uses_in_stmts(&stmts[1..], dead_alias.bindings[0].id) != 0 {
        return try_chain_local_method_call_stmt_without_dead_alias(stmts);
    }

    let chained = chain_local_method_call_stmt(second, third)?;
    Some((chained, 3))
}

fn try_chain_local_method_call_stmt_without_dead_alias(
    stmts: &[AstStmt],
) -> Option<(AstStmt, usize)> {
    let [first, second, ..] = stmts else {
        return None;
    };
    Some((chain_local_method_call_stmt(first, second)?, 2))
}

fn chain_local_method_call_stmt(first: &AstStmt, second: &AstStmt) -> Option<AstStmt> {
    let AstStmt::LocalDecl(local_decl) = first else {
        return None;
    };
    if local_decl.bindings.len() != 1
        || local_decl.values.len() != 1
        || local_decl.bindings[0].attr != AstLocalAttr::None
    {
        return None;
    }
    let AstExpr::MethodCall(first_call) = &local_decl.values[0] else {
        return None;
    };
    let AstStmt::CallStmt(call_stmt) = second else {
        return None;
    };
    let AstCallKind::MethodCall(second_call) = &call_stmt.call else {
        return None;
    };
    let AstExpr::Var(name) = &second_call.receiver else {
        return None;
    };
    if !name_matches_binding(name, local_decl.bindings[0].id)
        || count_binding_value_uses_in_stmts(
            std::slice::from_ref(second),
            local_decl.bindings[0].id,
        ) != 1
    {
        return None;
    }

    // 这里只收回“一次 method 调用立刻接下一次 method 调用”的局部壳：
    // 它本质上是 VM / HIR 为了保存中间 receiver 才拆出来的临时 local，
    // 不是源码里有意义的阶段变量。把它压回 `a:b():c()` 能明显更接近原形，
    // 同时不会放宽到普通任意调用结果的跨语句内联。
    Some(AstStmt::CallStmt(Box::new(
        super::super::common::AstCallStmt {
            call: AstCallKind::MethodCall(Box::new(super::super::common::AstMethodCallExpr {
                receiver: AstExpr::MethodCall(first_call.clone()),
                method: second_call.method.clone(),
                args: second_call.args.clone(),
            })),
        },
    )))
}

fn function_decl_target_from_lvalue(
    target: &AstLValue,
    func: &AstFunctionExpr,
    method_fields: &BTreeSet<String>,
) -> Option<(AstFunctionName, AstFunctionExpr)> {
    match target {
        AstLValue::Name(AstNameRef::Global(global)) => Some((
            AstFunctionName::Plain(AstNamePath {
                root: AstNameRef::Global(global.clone()),
                fields: Vec::new(),
            }),
            func.clone(),
        )),
        AstLValue::Name(_) => None,
        AstLValue::FieldAccess(access) => {
            let (root, mut fields) = name_path_from_expr(&access.base)?;
            if method_fields.contains(&access.field) && !func.params.is_empty() {
                return Some((
                    AstFunctionName::Method(AstNamePath { root, fields }, access.field.clone()),
                    func.clone(),
                ));
            }
            fields.push(access.field.clone());
            Some((
                AstFunctionName::Plain(AstNamePath { root, fields }),
                func.clone(),
            ))
        }
        AstLValue::IndexAccess(_) => None,
    }
}

fn name_path_from_expr(expr: &AstExpr) -> Option<(AstNameRef, Vec<String>)> {
    match expr {
        AstExpr::Var(
            name @ (AstNameRef::Param(_)
            | AstNameRef::Local(_)
            | AstNameRef::SyntheticLocal(_)
            | AstNameRef::Upvalue(_)
            | AstNameRef::Global(_)),
        ) => Some((name.clone(), Vec::new())),
        AstExpr::FieldAccess(access) => {
            let (root, mut fields) = name_path_from_expr(&access.base)?;
            fields.push(access.field.clone());
            Some((root, fields))
        }
        _ => None,
    }
}

fn count_binding_value_uses_in_stmts(stmts: &[AstStmt], binding: AstBindingRef) -> usize {
    stmts
        .iter()
        .map(|stmt| count_binding_value_uses_in_stmt(stmt, binding))
        .sum()
}

fn count_binding_value_uses_in_stmt(stmt: &AstStmt, binding: AstBindingRef) -> usize {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .map(|value| count_binding_value_uses_in_expr(value, binding))
            .sum(),
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .map(|value| count_binding_value_uses_in_expr(value, binding))
            .sum(),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .map(|target| count_binding_value_uses_in_lvalue(target, binding))
                .sum::<usize>()
                + assign
                    .values
                    .iter()
                    .map(|value| count_binding_value_uses_in_expr(value, binding))
                    .sum::<usize>()
        }
        AstStmt::CallStmt(call_stmt) => count_binding_value_uses_in_call(&call_stmt.call, binding),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .map(|value| count_binding_value_uses_in_expr(value, binding))
            .sum(),
        AstStmt::If(if_stmt) => {
            count_binding_value_uses_in_expr(&if_stmt.cond, binding)
                + count_binding_value_uses_in_block(&if_stmt.then_block, binding)
                + if_stmt
                    .else_block
                    .as_ref()
                    .map(|else_block| count_binding_value_uses_in_block(else_block, binding))
                    .unwrap_or(0)
        }
        AstStmt::While(while_stmt) => {
            count_binding_value_uses_in_expr(&while_stmt.cond, binding)
                + count_binding_value_uses_in_block(&while_stmt.body, binding)
        }
        AstStmt::Repeat(repeat_stmt) => {
            count_binding_value_uses_in_block(&repeat_stmt.body, binding)
                + count_binding_value_uses_in_expr(&repeat_stmt.cond, binding)
        }
        AstStmt::NumericFor(numeric_for) => {
            count_binding_value_uses_in_expr(&numeric_for.start, binding)
                + count_binding_value_uses_in_expr(&numeric_for.limit, binding)
                + count_binding_value_uses_in_expr(&numeric_for.step, binding)
                + count_binding_value_uses_in_block(&numeric_for.body, binding)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .map(|expr| count_binding_value_uses_in_expr(expr, binding))
                .sum::<usize>()
                + count_binding_value_uses_in_block(&generic_for.body, binding)
        }
        AstStmt::DoBlock(block) => count_binding_value_uses_in_block(block, binding),
        AstStmt::FunctionDecl(function_decl) => {
            count_binding_value_uses_in_block(&function_decl.func.body, binding)
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            count_binding_value_uses_in_block(&local_function_decl.func.body, binding)
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => 0,
    }
}

fn count_binding_value_uses_in_block(block: &AstBlock, binding: AstBindingRef) -> usize {
    block
        .stmts
        .iter()
        .map(|stmt| count_binding_value_uses_in_stmt(stmt, binding))
        .sum()
}

fn count_binding_value_uses_in_call(call: &AstCallKind, binding: AstBindingRef) -> usize {
    match call {
        AstCallKind::Call(call) => {
            count_binding_value_uses_in_expr(&call.callee, binding)
                + call
                    .args
                    .iter()
                    .map(|arg| count_binding_value_uses_in_expr(arg, binding))
                    .sum::<usize>()
        }
        AstCallKind::MethodCall(call) => {
            count_binding_value_uses_in_expr(&call.receiver, binding)
                + call
                    .args
                    .iter()
                    .map(|arg| count_binding_value_uses_in_expr(arg, binding))
                    .sum::<usize>()
        }
    }
}

fn count_binding_value_uses_in_lvalue(target: &AstLValue, binding: AstBindingRef) -> usize {
    match target {
        AstLValue::Name(_) => 0,
        AstLValue::FieldAccess(access) => count_binding_value_uses_in_expr(&access.base, binding),
        AstLValue::IndexAccess(access) => {
            count_binding_value_uses_in_expr(&access.base, binding)
                + count_binding_value_uses_in_expr(&access.index, binding)
        }
    }
}

fn count_binding_value_uses_in_expr(expr: &AstExpr, binding: AstBindingRef) -> usize {
    match expr {
        AstExpr::Var(name) if name_matches_binding(name, binding) => 1,
        AstExpr::FieldAccess(access) => count_binding_value_uses_in_expr(&access.base, binding),
        AstExpr::IndexAccess(access) => {
            count_binding_value_uses_in_expr(&access.base, binding)
                + count_binding_value_uses_in_expr(&access.index, binding)
        }
        AstExpr::Unary(unary) => count_binding_value_uses_in_expr(&unary.expr, binding),
        AstExpr::Binary(binary) => {
            count_binding_value_uses_in_expr(&binary.lhs, binding)
                + count_binding_value_uses_in_expr(&binary.rhs, binding)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            count_binding_value_uses_in_expr(&logical.lhs, binding)
                + count_binding_value_uses_in_expr(&logical.rhs, binding)
        }
        AstExpr::Call(call) => {
            count_binding_value_uses_in_call(&AstCallKind::Call(call.clone()), binding)
        }
        AstExpr::MethodCall(call) => {
            count_binding_value_uses_in_call(&AstCallKind::MethodCall(call.clone()), binding)
        }
        AstExpr::TableConstructor(table) => table
            .fields
            .iter()
            .map(|field| match field {
                super::super::common::AstTableField::Array(value) => {
                    count_binding_value_uses_in_expr(value, binding)
                }
                super::super::common::AstTableField::Record(record) => {
                    let key_count =
                        if let super::super::common::AstTableKey::Expr(key) = &record.key {
                            count_binding_value_uses_in_expr(key, binding)
                        } else {
                            0
                        };
                    key_count + count_binding_value_uses_in_expr(&record.value, binding)
                }
            })
            .sum(),
        AstExpr::FunctionExpr(function) => {
            count_binding_value_uses_in_block(&function.body, binding)
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => 0,
    }
}

fn name_matches_binding(name: &AstNameRef, binding: AstBindingRef) -> bool {
    match (name, binding) {
        (AstNameRef::Local(local), AstBindingRef::Local(binding_local)) => *local == binding_local,
        (AstNameRef::SyntheticLocal(local), AstBindingRef::SyntheticLocal(binding_local)) => {
            *local == binding_local
        }
        (AstNameRef::Temp(temp), AstBindingRef::Temp(binding_temp)) => *temp == binding_temp,
        _ => false,
    }
}

fn collect_method_field_names(module: &AstModule) -> BTreeSet<String> {
    let mut fields = BTreeSet::new();
    collect_method_field_names_in_block(&module.body, &mut fields);
    fields
}

fn collect_method_field_names_in_block(block: &AstBlock, fields: &mut BTreeSet<String>) {
    for stmt in &block.stmts {
        collect_method_field_names_in_stmt(stmt, fields);
    }
}

fn collect_method_field_names_in_stmt(stmt: &AstStmt, fields: &mut BTreeSet<String>) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_method_field_names_in_expr(value, fields);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_method_field_names_in_expr(value, fields);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_method_field_names_in_lvalue(target, fields);
            }
            for value in &assign.values {
                collect_method_field_names_in_expr(value, fields);
            }
        }
        AstStmt::CallStmt(call_stmt) => collect_method_field_names_in_call(&call_stmt.call, fields),
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_method_field_names_in_expr(value, fields);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_method_field_names_in_expr(&if_stmt.cond, fields);
            collect_method_field_names_in_block(&if_stmt.then_block, fields);
            if let Some(else_block) = &if_stmt.else_block {
                collect_method_field_names_in_block(else_block, fields);
            }
        }
        AstStmt::While(while_stmt) => {
            collect_method_field_names_in_expr(&while_stmt.cond, fields);
            collect_method_field_names_in_block(&while_stmt.body, fields);
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_method_field_names_in_block(&repeat_stmt.body, fields);
            collect_method_field_names_in_expr(&repeat_stmt.cond, fields);
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_method_field_names_in_expr(&numeric_for.start, fields);
            collect_method_field_names_in_expr(&numeric_for.limit, fields);
            collect_method_field_names_in_expr(&numeric_for.step, fields);
            collect_method_field_names_in_block(&numeric_for.body, fields);
        }
        AstStmt::GenericFor(generic_for) => {
            for iterator in &generic_for.iterator {
                collect_method_field_names_in_expr(iterator, fields);
            }
            collect_method_field_names_in_block(&generic_for.body, fields);
        }
        AstStmt::DoBlock(block) => collect_method_field_names_in_block(block, fields),
        AstStmt::FunctionDecl(function_decl) => {
            if let AstFunctionName::Method(_, method) = &function_decl.target {
                fields.insert(method.clone());
            }
            collect_method_field_names_in_block(&function_decl.func.body, fields);
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            collect_method_field_names_in_block(&local_function_decl.func.body, fields);
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
    }
}

fn collect_method_field_names_in_lvalue(target: &AstLValue, fields: &mut BTreeSet<String>) {
    match target {
        AstLValue::Name(_) => {}
        AstLValue::FieldAccess(access) => collect_method_field_names_in_expr(&access.base, fields),
        AstLValue::IndexAccess(access) => {
            collect_method_field_names_in_expr(&access.base, fields);
            collect_method_field_names_in_expr(&access.index, fields);
        }
    }
}

fn collect_method_field_names_in_call(call: &AstCallKind, fields: &mut BTreeSet<String>) {
    match call {
        AstCallKind::Call(call) => {
            collect_method_field_names_in_expr(&call.callee, fields);
            for arg in &call.args {
                collect_method_field_names_in_expr(arg, fields);
            }
        }
        AstCallKind::MethodCall(call) => {
            fields.insert(call.method.clone());
            collect_method_field_names_in_expr(&call.receiver, fields);
            for arg in &call.args {
                collect_method_field_names_in_expr(arg, fields);
            }
        }
    }
}

fn collect_method_field_names_in_expr(expr: &AstExpr, fields: &mut BTreeSet<String>) {
    match expr {
        AstExpr::FieldAccess(access) => collect_method_field_names_in_expr(&access.base, fields),
        AstExpr::IndexAccess(access) => {
            collect_method_field_names_in_expr(&access.base, fields);
            collect_method_field_names_in_expr(&access.index, fields);
        }
        AstExpr::Unary(unary) => collect_method_field_names_in_expr(&unary.expr, fields),
        AstExpr::Binary(binary) => {
            collect_method_field_names_in_expr(&binary.lhs, fields);
            collect_method_field_names_in_expr(&binary.rhs, fields);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_method_field_names_in_expr(&logical.lhs, fields);
            collect_method_field_names_in_expr(&logical.rhs, fields);
        }
        AstExpr::Call(call) => {
            collect_method_field_names_in_expr(&call.callee, fields);
            for arg in &call.args {
                collect_method_field_names_in_expr(arg, fields);
            }
        }
        AstExpr::MethodCall(call) => {
            fields.insert(call.method.clone());
            collect_method_field_names_in_expr(&call.receiver, fields);
            for arg in &call.args {
                collect_method_field_names_in_expr(arg, fields);
            }
        }
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    super::super::common::AstTableField::Array(value) => {
                        collect_method_field_names_in_expr(value, fields);
                    }
                    super::super::common::AstTableField::Record(record) => {
                        if let super::super::common::AstTableKey::Expr(key) = &record.key {
                            collect_method_field_names_in_expr(key, fields);
                        }
                        collect_method_field_names_in_expr(&record.value, fields);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(function) => {
            collect_method_field_names_in_block(&function.body, fields)
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => {}
    }
}

#[cfg(test)]
mod tests;
