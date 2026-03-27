//! global declaration 相关的 readability sugar。

use std::collections::BTreeSet;

use super::ReadabilityContext;
use super::binding_flow::count_binding_uses_in_stmts;
use crate::ast::common::{
    AstBindingRef, AstBlock, AstExpr, AstFunctionDecl, AstFunctionExpr, AstFunctionName,
    AstGlobalAttr, AstGlobalBinding, AstGlobalBindingTarget, AstGlobalDecl, AstLValue, AstModule,
    AstNameRef, AstStmt,
};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    if !context.target.caps.global_decl {
        return false;
    }
    rewrite_block(&mut module.body, &BTreeSet::new())
}

fn rewrite_block(block: &mut AstBlock, outer_declared: &BTreeSet<String>) -> bool {
    let mut changed = merge_seed_global_runs(block);
    let explicit_here = collect_explicit_globals(block);
    let nested_written_here = collect_nested_written_globals(block);
    let missing_here =
        collect_missing_globals(block, outer_declared, &explicit_here, &nested_written_here);
    if !missing_here.none.is_empty() || !missing_here.const_.is_empty() {
        insert_missing_global_decls(block, &missing_here);
        changed = true;
    }

    let mut visible = outer_declared.clone();
    visible.extend(explicit_here);
    visible.extend(missing_here.none.iter().cloned());
    visible.extend(missing_here.const_.iter().cloned());

    for stmt in &mut block.stmts {
        changed |= rewrite_nested_stmt(stmt, &visible);
    }
    changed
}

fn rewrite_nested_stmt(stmt: &mut AstStmt, visible_globals: &BTreeSet<String>) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            local_decl.values.iter_mut().fold(false, |changed, value| {
                changed | rewrite_nested_expr(value, visible_globals)
            })
        }
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target in &mut assign.targets {
                changed |= rewrite_nested_lvalue(target, visible_globals);
            }
            for value in &mut assign.values {
                changed |= rewrite_nested_expr(value, visible_globals);
            }
            changed
        }
        AstStmt::CallStmt(call_stmt) => rewrite_nested_call(&mut call_stmt.call, visible_globals),
        AstStmt::Return(ret) => ret.values.iter_mut().fold(false, |changed, value| {
            changed | rewrite_nested_expr(value, visible_globals)
        }),
        AstStmt::If(if_stmt) => {
            rewrite_nested_expr(&mut if_stmt.cond, visible_globals)
                | rewrite_block(&mut if_stmt.then_block, visible_globals)
                | if_stmt
                    .else_block
                    .as_mut()
                    .is_some_and(|else_block| rewrite_block(else_block, visible_globals))
        }
        AstStmt::While(while_stmt) => {
            rewrite_nested_expr(&mut while_stmt.cond, visible_globals)
                | rewrite_block(&mut while_stmt.body, visible_globals)
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_block(&mut repeat_stmt.body, visible_globals)
                | rewrite_nested_expr(&mut repeat_stmt.cond, visible_globals)
        }
        AstStmt::NumericFor(numeric_for) => {
            rewrite_nested_expr(&mut numeric_for.start, visible_globals)
                | rewrite_nested_expr(&mut numeric_for.limit, visible_globals)
                | rewrite_nested_expr(&mut numeric_for.step, visible_globals)
                | rewrite_block(&mut numeric_for.body, visible_globals)
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for iterator in &mut generic_for.iterator {
                changed |= rewrite_nested_expr(iterator, visible_globals);
            }
            changed | rewrite_block(&mut generic_for.body, visible_globals)
        }
        AstStmt::DoBlock(block) => rewrite_block(block, visible_globals),
        AstStmt::FunctionDecl(function_decl) => {
            rewrite_block(&mut function_decl.func.body, visible_globals)
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            rewrite_block(&mut function_decl.func.body, visible_globals)
        }
        AstStmt::GlobalDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) => false,
    }
}

fn rewrite_nested_call(
    call: &mut crate::ast::common::AstCallKind,
    visible_globals: &BTreeSet<String>,
) -> bool {
    match call {
        crate::ast::common::AstCallKind::Call(call) => {
            let mut changed = rewrite_nested_expr(&mut call.callee, visible_globals);
            for arg in &mut call.args {
                changed |= rewrite_nested_expr(arg, visible_globals);
            }
            changed
        }
        crate::ast::common::AstCallKind::MethodCall(call) => {
            let mut changed = rewrite_nested_expr(&mut call.receiver, visible_globals);
            for arg in &mut call.args {
                changed |= rewrite_nested_expr(arg, visible_globals);
            }
            changed
        }
    }
}

fn rewrite_nested_lvalue(target: &mut AstLValue, visible_globals: &BTreeSet<String>) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => rewrite_nested_expr(&mut access.base, visible_globals),
        AstLValue::IndexAccess(access) => {
            rewrite_nested_expr(&mut access.base, visible_globals)
                | rewrite_nested_expr(&mut access.index, visible_globals)
        }
    }
}

fn rewrite_nested_expr(expr: &mut AstExpr, visible_globals: &BTreeSet<String>) -> bool {
    match expr {
        AstExpr::FieldAccess(access) => rewrite_nested_expr(&mut access.base, visible_globals),
        AstExpr::IndexAccess(access) => {
            rewrite_nested_expr(&mut access.base, visible_globals)
                | rewrite_nested_expr(&mut access.index, visible_globals)
        }
        AstExpr::Unary(unary) => rewrite_nested_expr(&mut unary.expr, visible_globals),
        AstExpr::Binary(binary) => {
            rewrite_nested_expr(&mut binary.lhs, visible_globals)
                | rewrite_nested_expr(&mut binary.rhs, visible_globals)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_nested_expr(&mut logical.lhs, visible_globals)
                | rewrite_nested_expr(&mut logical.rhs, visible_globals)
        }
        AstExpr::Call(call) => {
            let mut changed = rewrite_nested_expr(&mut call.callee, visible_globals);
            for arg in &mut call.args {
                changed |= rewrite_nested_expr(arg, visible_globals);
            }
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = rewrite_nested_expr(&mut call.receiver, visible_globals);
            for arg in &mut call.args {
                changed |= rewrite_nested_expr(arg, visible_globals);
            }
            changed
        }
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                match field {
                    crate::ast::common::AstTableField::Array(value) => {
                        changed |= rewrite_nested_expr(value, visible_globals);
                    }
                    crate::ast::common::AstTableField::Record(record) => {
                        if let crate::ast::common::AstTableKey::Expr(key) = &mut record.key {
                            changed |= rewrite_nested_expr(key, visible_globals);
                        }
                        changed |= rewrite_nested_expr(&mut record.value, visible_globals);
                    }
                }
            }
            changed
        }
        AstExpr::FunctionExpr(function) => rewrite_block(&mut function.body, visible_globals),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
}

fn merge_seed_global_runs(block: &mut AstBlock) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut index = 0usize;
    let mut changed = false;

    while index < old_stmts.len() {
        if let Some((stmt, consumed)) = try_merge_seed_global_run(&old_stmts, index) {
            new_stmts.push(stmt);
            index += consumed;
            changed = true;
            continue;
        }
        new_stmts.push(old_stmts[index].clone());
        index += 1;
    }

    block.stmts = new_stmts;
    changed
}

fn try_merge_seed_global_run(stmts: &[AstStmt], start: usize) -> Option<(AstStmt, usize)> {
    let mut seeds = Vec::<(AstBindingRef, AstExpr)>::new();
    let mut index = start;
    while let Some(stmt) = stmts.get(index) {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            break;
        };
        if local_decl.bindings.len() != 1
            || local_decl.values.len() != 1
            || local_decl.bindings[0].attr != crate::ast::AstLocalAttr::None
        {
            break;
        }
        seeds.push((local_decl.bindings[0].id, local_decl.values[0].clone()));
        index += 1;
    }
    if seeds.is_empty() {
        return None;
    }

    let mut globals = Vec::<(AstBindingRef, AstGlobalBinding)>::new();
    let mut attr = None;
    while let Some(stmt) = stmts.get(index) {
        let AstStmt::GlobalDecl(global_decl) = stmt else {
            break;
        };
        if global_decl.bindings.len() != 1 || global_decl.values.len() != 1 {
            break;
        }
        let AstExpr::Var(name) = &global_decl.values[0] else {
            break;
        };
        let Some(binding) = binding_from_name_ref(name) else {
            break;
        };
        let current_attr = global_decl.bindings[0].attr;
        if attr.is_none() {
            attr = Some(current_attr);
        }
        if attr != Some(current_attr) {
            break;
        }
        globals.push((binding, global_decl.bindings[0].clone()));
        index += 1;
    }
    if globals.is_empty() {
        return None;
    }

    let after_run = &stmts[index..];
    let mut merged_bindings = Vec::new();
    let mut merged_values = Vec::new();
    let mut matched = BTreeSet::new();
    for (binding, value) in &seeds {
        if count_binding_uses_in_stmts(after_run, *binding) != 0 {
            return None;
        }
        let Some((_, global_binding)) = globals.iter().find(|(candidate, _)| candidate == binding)
        else {
            continue;
        };
        if !matched.insert(*binding) {
            return None;
        }
        merged_bindings.push(global_binding.clone());
        merged_values.push(value.clone());
    }
    if merged_bindings.len() != globals.len() {
        return None;
    }

    Some((
        AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
            bindings: merged_bindings,
            values: merged_values,
        })),
        index - start,
    ))
}

fn binding_from_name_ref(name: &AstNameRef) -> Option<AstBindingRef> {
    match name {
        AstNameRef::Local(local) => Some(AstBindingRef::Local(*local)),
        AstNameRef::SyntheticLocal(local) => Some(AstBindingRef::SyntheticLocal(*local)),
        AstNameRef::Temp(temp) => Some(AstBindingRef::Temp(*temp)),
        AstNameRef::Param(_) | AstNameRef::Upvalue(_) | AstNameRef::Global(_) => None,
    }
}

fn collect_explicit_globals(block: &AstBlock) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for stmt in &block.stmts {
        match stmt {
            AstStmt::GlobalDecl(global_decl) => {
                for binding in &global_decl.bindings {
                    if let AstGlobalBindingTarget::Name(name) = &binding.target {
                        names.insert(name.text.clone());
                    }
                }
            }
            AstStmt::LocalDecl(local_decl) => {
                for value in &local_decl.values {
                    collect_explicit_globals_in_expr(value, &mut names);
                }
            }
            AstStmt::Assign(assign) => {
                for target in &assign.targets {
                    collect_explicit_globals_in_lvalue(target, &mut names);
                }
                for value in &assign.values {
                    collect_explicit_globals_in_expr(value, &mut names);
                }
            }
            AstStmt::CallStmt(call_stmt) => {
                collect_explicit_globals_in_call(&call_stmt.call, &mut names)
            }
            AstStmt::Return(ret) => {
                for value in &ret.values {
                    collect_explicit_globals_in_expr(value, &mut names);
                }
            }
            AstStmt::If(if_stmt) => collect_explicit_globals_in_expr(&if_stmt.cond, &mut names),
            AstStmt::While(while_stmt) => {
                collect_explicit_globals_in_expr(&while_stmt.cond, &mut names)
            }
            AstStmt::Repeat(repeat_stmt) => {
                collect_explicit_globals_in_expr(&repeat_stmt.cond, &mut names)
            }
            AstStmt::NumericFor(numeric_for) => {
                collect_explicit_globals_in_expr(&numeric_for.start, &mut names);
                collect_explicit_globals_in_expr(&numeric_for.limit, &mut names);
                collect_explicit_globals_in_expr(&numeric_for.step, &mut names);
            }
            AstStmt::GenericFor(generic_for) => {
                for iterator in &generic_for.iterator {
                    collect_explicit_globals_in_expr(iterator, &mut names);
                }
            }
            AstStmt::FunctionDecl(function_decl) => {
                if let Some(name) = global_declared_name(function_decl) {
                    names.insert(name);
                }
            }
            AstStmt::LocalFunctionDecl(_) => {}
            AstStmt::DoBlock(_)
            | AstStmt::Break
            | AstStmt::Continue
            | AstStmt::Goto(_)
            | AstStmt::Label(_) => {}
        }
    }
    names
}

fn collect_explicit_globals_in_call(
    call: &crate::ast::common::AstCallKind,
    names: &mut BTreeSet<String>,
) {
    match call {
        crate::ast::common::AstCallKind::Call(call) => {
            collect_explicit_globals_in_expr(&call.callee, names);
            for arg in &call.args {
                collect_explicit_globals_in_expr(arg, names);
            }
        }
        crate::ast::common::AstCallKind::MethodCall(call) => {
            collect_explicit_globals_in_expr(&call.receiver, names);
            for arg in &call.args {
                collect_explicit_globals_in_expr(arg, names);
            }
        }
    }
}

fn collect_explicit_globals_in_lvalue(target: &AstLValue, names: &mut BTreeSet<String>) {
    match target {
        AstLValue::Name(_) => {}
        AstLValue::FieldAccess(access) => collect_explicit_globals_in_expr(&access.base, names),
        AstLValue::IndexAccess(access) => {
            collect_explicit_globals_in_expr(&access.base, names);
            collect_explicit_globals_in_expr(&access.index, names);
        }
    }
}

fn collect_explicit_globals_in_expr(expr: &AstExpr, names: &mut BTreeSet<String>) {
    match expr {
        AstExpr::FieldAccess(access) => collect_explicit_globals_in_expr(&access.base, names),
        AstExpr::IndexAccess(access) => {
            collect_explicit_globals_in_expr(&access.base, names);
            collect_explicit_globals_in_expr(&access.index, names);
        }
        AstExpr::Unary(unary) => collect_explicit_globals_in_expr(&unary.expr, names),
        AstExpr::Binary(binary) => {
            collect_explicit_globals_in_expr(&binary.lhs, names);
            collect_explicit_globals_in_expr(&binary.rhs, names);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_explicit_globals_in_expr(&logical.lhs, names);
            collect_explicit_globals_in_expr(&logical.rhs, names);
        }
        AstExpr::Call(call) => {
            collect_explicit_globals_in_expr(&call.callee, names);
            for arg in &call.args {
                collect_explicit_globals_in_expr(arg, names);
            }
        }
        AstExpr::MethodCall(call) => {
            collect_explicit_globals_in_expr(&call.receiver, names);
            for arg in &call.args {
                collect_explicit_globals_in_expr(arg, names);
            }
        }
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    crate::ast::common::AstTableField::Array(value) => {
                        collect_explicit_globals_in_expr(value, names);
                    }
                    crate::ast::common::AstTableField::Record(record) => {
                        if let crate::ast::common::AstTableKey::Expr(key) = &record.key {
                            collect_explicit_globals_in_expr(key, names);
                        }
                        collect_explicit_globals_in_expr(&record.value, names);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(_) => {}
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => {}
    }
}

fn collect_nested_written_globals(block: &AstBlock) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for stmt in &block.stmts {
        collect_nested_written_globals_in_stmt(stmt, &mut names);
    }
    names
}

fn collect_nested_written_globals_in_stmt(stmt: &AstStmt, names: &mut BTreeSet<String>) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_nested_written_globals_in_expr(value, names);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_nested_written_globals_in_lvalue(target, names);
            }
            for value in &assign.values {
                collect_nested_written_globals_in_expr(value, names);
            }
        }
        AstStmt::CallStmt(call_stmt) => {
            collect_nested_written_globals_in_call(&call_stmt.call, names)
        }
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_nested_written_globals_in_expr(value, names);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_nested_written_globals_in_expr(&if_stmt.cond, names);
            collect_nested_written_globals_in_block(&if_stmt.then_block, names);
            if let Some(else_block) = &if_stmt.else_block {
                collect_nested_written_globals_in_block(else_block, names);
            }
        }
        AstStmt::While(while_stmt) => {
            collect_nested_written_globals_in_expr(&while_stmt.cond, names);
            collect_nested_written_globals_in_block(&while_stmt.body, names);
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_nested_written_globals_in_block(&repeat_stmt.body, names);
            collect_nested_written_globals_in_expr(&repeat_stmt.cond, names);
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_nested_written_globals_in_expr(&numeric_for.start, names);
            collect_nested_written_globals_in_expr(&numeric_for.limit, names);
            collect_nested_written_globals_in_expr(&numeric_for.step, names);
            collect_nested_written_globals_in_block(&numeric_for.body, names);
        }
        AstStmt::GenericFor(generic_for) => {
            for iterator in &generic_for.iterator {
                collect_nested_written_globals_in_expr(iterator, names);
            }
            collect_nested_written_globals_in_block(&generic_for.body, names);
        }
        AstStmt::DoBlock(block) => collect_nested_written_globals_in_block(block, names),
        AstStmt::FunctionDecl(function_decl) => {
            collect_written_globals_from_function(&function_decl.func, names);
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            collect_written_globals_from_function(&function_decl.func, names);
        }
        AstStmt::GlobalDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) => {}
    }
}

fn collect_nested_written_globals_in_block(block: &AstBlock, names: &mut BTreeSet<String>) {
    for stmt in &block.stmts {
        collect_nested_written_globals_in_stmt(stmt, names);
    }
}

fn collect_nested_written_globals_in_call(
    call: &crate::ast::common::AstCallKind,
    names: &mut BTreeSet<String>,
) {
    match call {
        crate::ast::common::AstCallKind::Call(call) => {
            collect_nested_written_globals_in_expr(&call.callee, names);
            for arg in &call.args {
                collect_nested_written_globals_in_expr(arg, names);
            }
        }
        crate::ast::common::AstCallKind::MethodCall(call) => {
            collect_nested_written_globals_in_expr(&call.receiver, names);
            for arg in &call.args {
                collect_nested_written_globals_in_expr(arg, names);
            }
        }
    }
}

fn collect_nested_written_globals_in_lvalue(target: &AstLValue, names: &mut BTreeSet<String>) {
    match target {
        AstLValue::Name(_) => {}
        AstLValue::FieldAccess(access) => {
            collect_nested_written_globals_in_expr(&access.base, names);
        }
        AstLValue::IndexAccess(access) => {
            collect_nested_written_globals_in_expr(&access.base, names);
            collect_nested_written_globals_in_expr(&access.index, names);
        }
    }
}

fn collect_nested_written_globals_in_expr(expr: &AstExpr, names: &mut BTreeSet<String>) {
    match expr {
        AstExpr::FieldAccess(access) => collect_nested_written_globals_in_expr(&access.base, names),
        AstExpr::IndexAccess(access) => {
            collect_nested_written_globals_in_expr(&access.base, names);
            collect_nested_written_globals_in_expr(&access.index, names);
        }
        AstExpr::Unary(unary) => collect_nested_written_globals_in_expr(&unary.expr, names),
        AstExpr::Binary(binary) => {
            collect_nested_written_globals_in_expr(&binary.lhs, names);
            collect_nested_written_globals_in_expr(&binary.rhs, names);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_nested_written_globals_in_expr(&logical.lhs, names);
            collect_nested_written_globals_in_expr(&logical.rhs, names);
        }
        AstExpr::Call(call) => {
            collect_nested_written_globals_in_expr(&call.callee, names);
            for arg in &call.args {
                collect_nested_written_globals_in_expr(arg, names);
            }
        }
        AstExpr::MethodCall(call) => {
            collect_nested_written_globals_in_expr(&call.receiver, names);
            for arg in &call.args {
                collect_nested_written_globals_in_expr(arg, names);
            }
        }
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    crate::ast::common::AstTableField::Array(value) => {
                        collect_nested_written_globals_in_expr(value, names);
                    }
                    crate::ast::common::AstTableField::Record(record) => {
                        if let crate::ast::common::AstTableKey::Expr(key) = &record.key {
                            collect_nested_written_globals_in_expr(key, names);
                        }
                        collect_nested_written_globals_in_expr(&record.value, names);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(function) => collect_written_globals_from_function(function, names),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => {}
    }
}

fn collect_written_globals_from_function(function: &AstFunctionExpr, names: &mut BTreeSet<String>) {
    for stmt in &function.body.stmts {
        collect_written_globals_from_stmt(stmt, names);
    }
}

fn collect_written_globals_from_stmt(stmt: &AstStmt, names: &mut BTreeSet<String>) {
    match stmt {
        AstStmt::GlobalDecl(global_decl) => {
            for binding in &global_decl.bindings {
                if let AstGlobalBindingTarget::Name(name) = &binding.target {
                    names.insert(name.text.clone());
                }
            }
        }
        AstStmt::FunctionDecl(function_decl) => {
            if let Some(name) = global_declared_name(function_decl) {
                names.insert(name);
            }
            collect_written_globals_from_function(&function_decl.func, names);
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            collect_written_globals_from_function(&function_decl.func, names);
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_written_globals_from_lvalue(target, names);
            }
            for value in &assign.values {
                collect_nested_written_globals_in_expr(value, names);
            }
        }
        AstStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_nested_written_globals_in_expr(value, names);
            }
        }
        AstStmt::CallStmt(call_stmt) => {
            collect_nested_written_globals_in_call(&call_stmt.call, names)
        }
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_nested_written_globals_in_expr(value, names);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_nested_written_globals_in_expr(&if_stmt.cond, names);
            for stmt in &if_stmt.then_block.stmts {
                collect_written_globals_from_stmt(stmt, names);
            }
            if let Some(else_block) = &if_stmt.else_block {
                for stmt in &else_block.stmts {
                    collect_written_globals_from_stmt(stmt, names);
                }
            }
        }
        AstStmt::While(while_stmt) => {
            collect_nested_written_globals_in_expr(&while_stmt.cond, names);
            for stmt in &while_stmt.body.stmts {
                collect_written_globals_from_stmt(stmt, names);
            }
        }
        AstStmt::Repeat(repeat_stmt) => {
            for stmt in &repeat_stmt.body.stmts {
                collect_written_globals_from_stmt(stmt, names);
            }
            collect_nested_written_globals_in_expr(&repeat_stmt.cond, names);
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_nested_written_globals_in_expr(&numeric_for.start, names);
            collect_nested_written_globals_in_expr(&numeric_for.limit, names);
            collect_nested_written_globals_in_expr(&numeric_for.step, names);
            for stmt in &numeric_for.body.stmts {
                collect_written_globals_from_stmt(stmt, names);
            }
        }
        AstStmt::GenericFor(generic_for) => {
            for iterator in &generic_for.iterator {
                collect_nested_written_globals_in_expr(iterator, names);
            }
            for stmt in &generic_for.body.stmts {
                collect_written_globals_from_stmt(stmt, names);
            }
        }
        AstStmt::DoBlock(block) => {
            for stmt in &block.stmts {
                collect_written_globals_from_stmt(stmt, names);
            }
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
    }
}

fn collect_written_globals_from_lvalue(target: &AstLValue, names: &mut BTreeSet<String>) {
    match target {
        AstLValue::Name(AstNameRef::Global(global)) => {
            names.insert(global.text.clone());
        }
        AstLValue::Name(_) => {}
        AstLValue::FieldAccess(access) => {
            collect_nested_written_globals_in_expr(&access.base, names);
        }
        AstLValue::IndexAccess(access) => {
            collect_nested_written_globals_in_expr(&access.base, names);
            collect_nested_written_globals_in_expr(&access.index, names);
        }
    }
}

fn global_declared_name(function_decl: &AstFunctionDecl) -> Option<String> {
    let path = match &function_decl.target {
        AstFunctionName::Plain(path) | AstFunctionName::Method(path, _) => path,
    };
    match &path.root {
        AstNameRef::Global(global) => Some(global.text.clone()),
        _ => None,
    }
}

#[derive(Default)]
struct MissingGlobals {
    none: Vec<String>,
    const_: Vec<String>,
    seen_none: BTreeSet<String>,
    seen_const: BTreeSet<String>,
}

impl MissingGlobals {
    fn note_none(&mut self, name: &str) {
        if self.seen_none.insert(name.to_owned()) {
            self.none.push(name.to_owned());
        }
        self.seen_const.remove(name);
        self.const_.retain(|candidate| candidate != name);
    }

    fn note_const(&mut self, name: &str) {
        if self.seen_none.contains(name) || !self.seen_const.insert(name.to_owned()) {
            return;
        }
        self.const_.push(name.to_owned());
    }
}

fn collect_missing_globals(
    block: &AstBlock,
    outer_declared: &BTreeSet<String>,
    explicit_here: &BTreeSet<String>,
    nested_written_here: &BTreeSet<String>,
) -> MissingGlobals {
    let mut missing = MissingGlobals::default();
    for stmt in &block.stmts {
        collect_missing_globals_in_stmt(
            stmt,
            outer_declared,
            explicit_here,
            nested_written_here,
            &mut missing,
        );
    }
    missing
}

fn collect_missing_globals_in_stmt(
    stmt: &AstStmt,
    outer_declared: &BTreeSet<String>,
    explicit_here: &BTreeSet<String>,
    nested_written_here: &BTreeSet<String>,
    missing: &mut MissingGlobals,
) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_missing_globals_in_expr(
                    value,
                    outer_declared,
                    explicit_here,
                    nested_written_here,
                    missing,
                );
            }
        }
        AstStmt::GlobalDecl(_) | AstStmt::FunctionDecl(_) | AstStmt::LocalFunctionDecl(_) => {}
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_missing_globals_in_lvalue(
                    target,
                    outer_declared,
                    explicit_here,
                    nested_written_here,
                    missing,
                    true,
                );
            }
            for value in &assign.values {
                collect_missing_globals_in_expr(
                    value,
                    outer_declared,
                    explicit_here,
                    nested_written_here,
                    missing,
                );
            }
        }
        AstStmt::CallStmt(call_stmt) => {
            collect_missing_globals_in_call(
                &call_stmt.call,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
        }
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_missing_globals_in_expr(
                    value,
                    outer_declared,
                    explicit_here,
                    nested_written_here,
                    missing,
                );
            }
        }
        AstStmt::If(if_stmt) => {
            collect_missing_globals_in_expr(
                &if_stmt.cond,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
        }
        AstStmt::While(while_stmt) => {
            collect_missing_globals_in_expr(
                &while_stmt.cond,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_missing_globals_in_expr(
                &repeat_stmt.cond,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_missing_globals_in_expr(
                &numeric_for.start,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
            collect_missing_globals_in_expr(
                &numeric_for.limit,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
            collect_missing_globals_in_expr(
                &numeric_for.step,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
        }
        AstStmt::GenericFor(generic_for) => {
            for iterator in &generic_for.iterator {
                collect_missing_globals_in_expr(
                    iterator,
                    outer_declared,
                    explicit_here,
                    nested_written_here,
                    missing,
                );
            }
        }
        AstStmt::DoBlock(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_) => {}
    }
}

fn collect_missing_globals_in_call(
    call: &crate::ast::common::AstCallKind,
    outer_declared: &BTreeSet<String>,
    explicit_here: &BTreeSet<String>,
    nested_written_here: &BTreeSet<String>,
    missing: &mut MissingGlobals,
) {
    match call {
        crate::ast::common::AstCallKind::Call(call) => {
            collect_missing_globals_in_expr(
                &call.callee,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
            for arg in &call.args {
                collect_missing_globals_in_expr(
                    arg,
                    outer_declared,
                    explicit_here,
                    nested_written_here,
                    missing,
                );
            }
        }
        crate::ast::common::AstCallKind::MethodCall(call) => {
            collect_missing_globals_in_expr(
                &call.receiver,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
            for arg in &call.args {
                collect_missing_globals_in_expr(
                    arg,
                    outer_declared,
                    explicit_here,
                    nested_written_here,
                    missing,
                );
            }
        }
    }
}

fn collect_missing_globals_in_lvalue(
    lvalue: &AstLValue,
    outer_declared: &BTreeSet<String>,
    explicit_here: &BTreeSet<String>,
    nested_written_here: &BTreeSet<String>,
    missing: &mut MissingGlobals,
    is_write: bool,
) {
    match lvalue {
        AstLValue::Name(AstNameRef::Global(global)) => {
            if !outer_declared.contains(&global.text) && !explicit_here.contains(&global.text) {
                if is_write {
                    missing.note_none(&global.text);
                } else if nested_written_here.contains(&global.text) {
                    missing.note_none(&global.text);
                } else {
                    missing.note_const(&global.text);
                }
            }
        }
        AstLValue::Name(_) => {}
        AstLValue::FieldAccess(access) => {
            collect_missing_globals_in_expr(
                &access.base,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
        }
        AstLValue::IndexAccess(access) => {
            collect_missing_globals_in_expr(
                &access.base,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
            collect_missing_globals_in_expr(
                &access.index,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
        }
    }
}

fn collect_missing_globals_in_expr(
    expr: &AstExpr,
    outer_declared: &BTreeSet<String>,
    explicit_here: &BTreeSet<String>,
    nested_written_here: &BTreeSet<String>,
    missing: &mut MissingGlobals,
) {
    match expr {
        AstExpr::Var(AstNameRef::Global(global)) => {
            if !outer_declared.contains(&global.text) && !explicit_here.contains(&global.text) {
                if nested_written_here.contains(&global.text) {
                    missing.note_none(&global.text);
                } else {
                    missing.note_const(&global.text);
                }
            }
        }
        AstExpr::Var(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::VarArg
        | AstExpr::FunctionExpr(_) => {}
        AstExpr::FieldAccess(access) => {
            collect_missing_globals_in_expr(
                &access.base,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
        }
        AstExpr::IndexAccess(access) => {
            collect_missing_globals_in_expr(
                &access.base,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
            collect_missing_globals_in_expr(
                &access.index,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
        }
        AstExpr::Unary(unary) => {
            collect_missing_globals_in_expr(
                &unary.expr,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
        }
        AstExpr::Binary(binary) => {
            collect_missing_globals_in_expr(
                &binary.lhs,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
            collect_missing_globals_in_expr(
                &binary.rhs,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_missing_globals_in_expr(
                &logical.lhs,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
            collect_missing_globals_in_expr(
                &logical.rhs,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
        }
        AstExpr::Call(call) => {
            collect_missing_globals_in_expr(
                &call.callee,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
            for arg in &call.args {
                collect_missing_globals_in_expr(
                    arg,
                    outer_declared,
                    explicit_here,
                    nested_written_here,
                    missing,
                );
            }
        }
        AstExpr::MethodCall(call) => {
            collect_missing_globals_in_expr(
                &call.receiver,
                outer_declared,
                explicit_here,
                nested_written_here,
                missing,
            );
            for arg in &call.args {
                collect_missing_globals_in_expr(
                    arg,
                    outer_declared,
                    explicit_here,
                    nested_written_here,
                    missing,
                );
            }
        }
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    crate::ast::common::AstTableField::Array(value) => {
                        collect_missing_globals_in_expr(
                            value,
                            outer_declared,
                            explicit_here,
                            nested_written_here,
                            missing,
                        );
                    }
                    crate::ast::common::AstTableField::Record(record) => {
                        if let crate::ast::common::AstTableKey::Expr(key) = &record.key {
                            collect_missing_globals_in_expr(
                                key,
                                outer_declared,
                                explicit_here,
                                nested_written_here,
                                missing,
                            );
                        }
                        collect_missing_globals_in_expr(
                            &record.value,
                            outer_declared,
                            explicit_here,
                            nested_written_here,
                            missing,
                        );
                    }
                }
            }
        }
    }
}

fn insert_missing_global_decls(block: &mut AstBlock, missing: &MissingGlobals) {
    let mut inserted = Vec::new();
    if !missing.none.is_empty() {
        inserted.push(AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
            bindings: missing
                .none
                .iter()
                .cloned()
                .map(|name| AstGlobalBinding {
                    target: AstGlobalBindingTarget::Name(crate::ast::common::AstGlobalName {
                        text: name,
                    }),
                    attr: AstGlobalAttr::None,
                })
                .collect(),
            values: Vec::new(),
        })));
    }
    if !missing.const_.is_empty() {
        inserted.push(AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
            bindings: missing
                .const_
                .iter()
                .cloned()
                .map(|name| AstGlobalBinding {
                    target: AstGlobalBindingTarget::Name(crate::ast::common::AstGlobalName {
                        text: name,
                    }),
                    attr: AstGlobalAttr::Const,
                })
                .collect(),
            values: Vec::new(),
        })));
    }
    if inserted.is_empty() {
        return;
    }

    let old_stmts = std::mem::take(&mut block.stmts);
    let insert_at = old_stmts
        .iter()
        .take_while(|stmt| matches!(stmt, AstStmt::GlobalDecl(_)))
        .count();
    let mut new_stmts = Vec::with_capacity(old_stmts.len() + inserted.len());
    new_stmts.extend(old_stmts.iter().take(insert_at).cloned());
    new_stmts.extend(inserted);
    new_stmts.extend(old_stmts.into_iter().skip(insert_at));
    block.stmts = new_stmts;
}

#[cfg(test)]
mod tests;
