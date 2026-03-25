//! 函数声明相关的 readability sugar。

use super::super::common::{
    AstAssign, AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionDecl, AstFunctionExpr,
    AstFunctionName, AstGlobalDecl, AstLValue, AstLocalAttr, AstLocalDecl, AstLocalFunctionDecl,
    AstModule, AstNamePath, AstNameRef, AstStmt, AstTargetDialect,
};

pub(super) fn apply(module: &mut AstModule, target: AstTargetDialect) -> bool {
    rewrite_block(&mut module.body, target)
}

fn rewrite_block(block: &mut AstBlock, target: AstTargetDialect) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= rewrite_nested(stmt, target);
    }

    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut index = 0;
    while index < old_stmts.len() {
        if let Some((stmt, consumed)) =
            try_lower_forwarded_function_stmt(&old_stmts[index..], target)
        {
            new_stmts.push(stmt);
            changed = true;
            index += consumed;
            continue;
        }

        let stmt = lower_direct_function_stmt(old_stmts[index].clone(), target);
        changed |= stmt != old_stmts[index];
        new_stmts.push(stmt);
        index += 1;
    }
    block.stmts = new_stmts;
    changed
}

fn rewrite_nested(stmt: &mut AstStmt, target: AstTargetDialect) -> bool {
    match stmt {
        AstStmt::If(if_stmt) => {
            let mut changed = rewrite_block(&mut if_stmt.then_block, target);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block, target);
            }
            changed |= rewrite_function_exprs_in_expr(&mut if_stmt.cond, target);
            changed
        }
        AstStmt::While(while_stmt) => {
            rewrite_function_exprs_in_expr(&mut while_stmt.cond, target)
                | rewrite_block(&mut while_stmt.body, target)
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_block(&mut repeat_stmt.body, target)
                | rewrite_function_exprs_in_expr(&mut repeat_stmt.cond, target)
        }
        AstStmt::NumericFor(numeric_for) => {
            let mut changed = rewrite_function_exprs_in_expr(&mut numeric_for.start, target);
            changed |= rewrite_function_exprs_in_expr(&mut numeric_for.limit, target);
            changed |= rewrite_function_exprs_in_expr(&mut numeric_for.step, target);
            changed |= rewrite_block(&mut numeric_for.body, target);
            changed
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for expr in &mut generic_for.iterator {
                changed |= rewrite_function_exprs_in_expr(expr, target);
            }
            changed |= rewrite_block(&mut generic_for.body, target);
            changed
        }
        AstStmt::DoBlock(block) => rewrite_block(block, target),
        AstStmt::FunctionDecl(function_decl) => rewrite_function_expr(&mut function_decl.func, target),
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
    rewrite_block(&mut function.body, target)
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

fn rewrite_function_exprs_in_lvalue(target_lvalue: &mut AstLValue, target: AstTargetDialect) -> bool {
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

fn lower_direct_function_stmt(stmt: AstStmt, target: AstTargetDialect) -> AstStmt {
    match &stmt {
        AstStmt::LocalDecl(local_decl) => try_lower_local_function_decl((**local_decl).clone()),
        AstStmt::GlobalDecl(global_decl) => {
            try_lower_global_function_decl((**global_decl).clone(), target).unwrap_or(stmt)
        }
        AstStmt::Assign(assign) => {
            try_lower_function_assign((**assign).clone()).unwrap_or(stmt)
        }
        _ => stmt,
    }
}

fn try_lower_forwarded_function_stmt(
    stmts: &[AstStmt],
    target: AstTargetDialect,
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
    if count_binding_value_uses_in_stmts(&stmts[1..], binding) != 1 {
        return None;
    }
    let function = function.as_ref().clone();
    let stmt = inline_function_into_stmt(next, binding, function, target)?;
    Some((stmt, 2))
}

fn try_lower_local_function_decl(local_decl: AstLocalDecl) -> AstStmt {
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return AstStmt::LocalDecl(Box::new(local_decl));
    }
    let binding = &local_decl.bindings[0];
    if binding.attr != AstLocalAttr::None {
        return AstStmt::LocalDecl(Box::new(local_decl));
    }
    let AstBindingRef::Local(name) = binding.id else {
        return AstStmt::LocalDecl(Box::new(local_decl));
    };
    let AstExpr::FunctionExpr(func) = &local_decl.values[0] else {
        return AstStmt::LocalDecl(Box::new(local_decl));
    };
    AstStmt::LocalFunctionDecl(Box::new(AstLocalFunctionDecl {
        name: AstBindingRef::Local(name),
        func: func.as_ref().clone(),
    }))
}

fn try_lower_global_function_decl(
    global_decl: AstGlobalDecl,
    target: AstTargetDialect,
) -> Option<AstStmt> {
    if !target.caps.global_decl || global_decl.bindings.len() != 1 || global_decl.values.len() != 1 {
        return None;
    }
    if global_decl.bindings[0].attr != super::super::common::AstGlobalAttr::None {
        return None;
    }
    let AstExpr::FunctionExpr(func) = &global_decl.values[0] else {
        return None;
    };
    Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
        target: AstFunctionName::Plain(AstNamePath {
            root: AstNameRef::Global(global_decl.bindings[0].name.clone()),
            fields: Vec::new(),
        }),
        func: func.as_ref().clone(),
    })))
}

fn try_lower_function_assign(assign: AstAssign) -> Option<AstStmt> {
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return None;
    }
    let AstExpr::FunctionExpr(func) = &assign.values[0] else {
        return None;
    };
    let target = function_name_from_lvalue(&assign.targets[0])?;
    Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
        target,
        func: func.as_ref().clone(),
    })))
}

fn inline_function_into_stmt(
    stmt: &AstStmt,
    binding: AstBindingRef,
    function: AstFunctionExpr,
    target: AstTargetDialect,
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
                return Some(AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                    target: AstFunctionName::Plain(AstNamePath {
                        root: AstNameRef::Global(global_decl.bindings[0].name.clone()),
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
            if let Some(target_name) = function_name_from_lvalue(&assign.targets[0]) {
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

fn function_name_from_lvalue(target: &AstLValue) -> Option<AstFunctionName> {
    match target {
        AstLValue::Name(AstNameRef::Global(global)) => Some(AstFunctionName::Plain(AstNamePath {
            root: AstNameRef::Global(global.clone()),
            fields: Vec::new(),
        })),
        AstLValue::Name(_) => None,
        AstLValue::FieldAccess(access) => {
            let (root, mut fields) = name_path_from_expr(&access.base)?;
            fields.push(access.field.clone());
            Some(AstFunctionName::Plain(AstNamePath { root, fields }))
        }
        AstLValue::IndexAccess(_) => None,
    }
}

fn name_path_from_expr(expr: &AstExpr) -> Option<(AstNameRef, Vec<String>)> {
    match expr {
        AstExpr::Var(name @ (AstNameRef::Param(_)
        | AstNameRef::Local(_)
        | AstNameRef::Upvalue(_)
        | AstNameRef::Global(_))) => Some((name.clone(), Vec::new())),
        AstExpr::FieldAccess(access) => {
            let (root, mut fields) = name_path_from_expr(&access.base)?;
            fields.push(access.field.clone());
            Some((root, fields))
        }
        _ => None,
    }
}

fn count_binding_value_uses_in_stmts(stmts: &[AstStmt], binding: AstBindingRef) -> usize {
    stmts.iter().map(|stmt| count_binding_value_uses_in_stmt(stmt, binding)).sum()
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
        AstStmt::FunctionDecl(function_decl) => count_binding_value_uses_in_block(&function_decl.func.body, binding),
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
        AstExpr::Call(call) => count_binding_value_uses_in_call(&AstCallKind::Call(call.clone()), binding),
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
                    let key_count = if let super::super::common::AstTableKey::Expr(key) = &record.key {
                        count_binding_value_uses_in_expr(key, binding)
                    } else {
                        0
                    };
                    key_count + count_binding_value_uses_in_expr(&record.value, binding)
                }
            })
            .sum(),
        AstExpr::FunctionExpr(function) => count_binding_value_uses_in_block(&function.body, binding),
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
        (AstNameRef::Temp(temp), AstBindingRef::Temp(binding_temp)) => *temp == binding_temp,
        _ => false,
    }
}
