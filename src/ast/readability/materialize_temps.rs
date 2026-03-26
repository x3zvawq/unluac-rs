//! 把最终仍残留在 AST 里的 temp 物化成 AST 自己的保守局部绑定。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::TempId;

use super::super::common::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstModule,
    AstNameRef, AstStmt, AstSyntheticLocalId, AstTableField, AstTableKey,
};
use super::ReadabilityContext;

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    materialize_function_block(&mut module.body)
}

fn materialize_function_block(block: &mut AstBlock) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= materialize_nested_functions_in_stmt(stmt);
    }

    let temps = collect_function_temps_in_block(block);
    if temps.is_empty() {
        return changed;
    }

    let mapping = temps
        .into_iter()
        .map(|temp| (temp, AstSyntheticLocalId(temp)))
        .collect::<BTreeMap<_, _>>();
    rewrite_function_block(block, &mapping);
    true
}

fn materialize_nested_functions_in_stmt(stmt: &mut AstStmt) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            let mut changed = false;
            for value in &mut local_decl.values {
                changed |= materialize_nested_functions_in_expr(value);
            }
            changed
        }
        AstStmt::GlobalDecl(global_decl) => {
            let mut changed = false;
            for value in &mut global_decl.values {
                changed |= materialize_nested_functions_in_expr(value);
            }
            changed
        }
        AstStmt::Assign(assign) => {
            let mut changed = false;
            for target in &mut assign.targets {
                changed |= materialize_nested_functions_in_lvalue(target);
            }
            for value in &mut assign.values {
                changed |= materialize_nested_functions_in_expr(value);
            }
            changed
        }
        AstStmt::CallStmt(call_stmt) => materialize_nested_functions_in_call(&mut call_stmt.call),
        AstStmt::Return(ret) => {
            let mut changed = false;
            for value in &mut ret.values {
                changed |= materialize_nested_functions_in_expr(value);
            }
            changed
        }
        AstStmt::If(if_stmt) => {
            let cond_changed = materialize_nested_functions_in_expr(&mut if_stmt.cond);
            let then_changed = materialize_function_block(&mut if_stmt.then_block);
            let else_changed = if_stmt
                .else_block
                .as_mut()
                .is_some_and(materialize_function_block);
            cond_changed || then_changed || else_changed
        }
        AstStmt::While(while_stmt) => {
            materialize_nested_functions_in_expr(&mut while_stmt.cond)
                || materialize_function_block(&mut while_stmt.body)
        }
        AstStmt::Repeat(repeat_stmt) => {
            materialize_function_block(&mut repeat_stmt.body)
                || materialize_nested_functions_in_expr(&mut repeat_stmt.cond)
        }
        AstStmt::NumericFor(numeric_for) => {
            let start_changed = materialize_nested_functions_in_expr(&mut numeric_for.start);
            let limit_changed = materialize_nested_functions_in_expr(&mut numeric_for.limit);
            let step_changed = materialize_nested_functions_in_expr(&mut numeric_for.step);
            let body_changed = materialize_function_block(&mut numeric_for.body);
            start_changed || limit_changed || step_changed || body_changed
        }
        AstStmt::GenericFor(generic_for) => {
            let mut changed = false;
            for expr in &mut generic_for.iterator {
                changed |= materialize_nested_functions_in_expr(expr);
            }
            changed || materialize_function_block(&mut generic_for.body)
        }
        AstStmt::DoBlock(block) => materialize_function_block(block),
        AstStmt::FunctionDecl(function_decl) => materialize_function_expr(&mut function_decl.func),
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            materialize_function_expr(&mut local_function_decl.func)
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => false,
    }
}

fn materialize_function_expr(function: &mut AstFunctionExpr) -> bool {
    materialize_function_block(&mut function.body)
}

fn materialize_nested_functions_in_call(call: &mut AstCallKind) -> bool {
    match call {
        AstCallKind::Call(call) => {
            let callee_changed = materialize_nested_functions_in_expr(&mut call.callee);
            let arg_changed = call
                .args
                .iter_mut()
                .any(materialize_nested_functions_in_expr);
            callee_changed || arg_changed
        }
        AstCallKind::MethodCall(call) => {
            let receiver_changed = materialize_nested_functions_in_expr(&mut call.receiver);
            let arg_changed = call
                .args
                .iter_mut()
                .any(materialize_nested_functions_in_expr);
            receiver_changed || arg_changed
        }
    }
}

fn materialize_nested_functions_in_lvalue(target: &mut AstLValue) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => materialize_nested_functions_in_expr(&mut access.base),
        AstLValue::IndexAccess(access) => {
            let base_changed = materialize_nested_functions_in_expr(&mut access.base);
            let index_changed = materialize_nested_functions_in_expr(&mut access.index);
            base_changed || index_changed
        }
    }
}

fn materialize_nested_functions_in_expr(expr: &mut AstExpr) -> bool {
    match expr {
        AstExpr::FieldAccess(access) => materialize_nested_functions_in_expr(&mut access.base),
        AstExpr::IndexAccess(access) => {
            let base_changed = materialize_nested_functions_in_expr(&mut access.base);
            let index_changed = materialize_nested_functions_in_expr(&mut access.index);
            base_changed || index_changed
        }
        AstExpr::Unary(unary) => materialize_nested_functions_in_expr(&mut unary.expr),
        AstExpr::Binary(binary) => {
            let lhs_changed = materialize_nested_functions_in_expr(&mut binary.lhs);
            let rhs_changed = materialize_nested_functions_in_expr(&mut binary.rhs);
            lhs_changed || rhs_changed
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            let lhs_changed = materialize_nested_functions_in_expr(&mut logical.lhs);
            let rhs_changed = materialize_nested_functions_in_expr(&mut logical.rhs);
            lhs_changed || rhs_changed
        }
        AstExpr::Call(call) => {
            let mut changed = materialize_nested_functions_in_expr(&mut call.callee);
            for arg in &mut call.args {
                changed |= materialize_nested_functions_in_expr(arg);
            }
            changed
        }
        AstExpr::MethodCall(call) => {
            let mut changed = materialize_nested_functions_in_expr(&mut call.receiver);
            for arg in &mut call.args {
                changed |= materialize_nested_functions_in_expr(arg);
            }
            changed
        }
        AstExpr::TableConstructor(table) => {
            let mut changed = false;
            for field in &mut table.fields {
                changed |= match field {
                    AstTableField::Array(value) => materialize_nested_functions_in_expr(value),
                    AstTableField::Record(record) => {
                        let key_changed = match &mut record.key {
                            AstTableKey::Name(_) => false,
                            AstTableKey::Expr(expr) => materialize_nested_functions_in_expr(expr),
                        };
                        key_changed || materialize_nested_functions_in_expr(&mut record.value)
                    }
                };
            }
            changed
        }
        AstExpr::FunctionExpr(function) => materialize_function_expr(function),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => false,
    }
}

fn collect_function_temps_in_block(block: &AstBlock) -> BTreeSet<TempId> {
    let mut temps = BTreeSet::new();
    for stmt in &block.stmts {
        collect_function_temps_in_stmt(stmt, &mut temps);
    }
    temps
}

fn collect_function_temps_in_stmt(stmt: &AstStmt, temps: &mut BTreeSet<TempId>) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                if let AstBindingRef::Temp(temp) = binding.id {
                    temps.insert(temp);
                }
            }
            for value in &local_decl.values {
                collect_function_temps_in_expr(value, temps);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_function_temps_in_expr(value, temps);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_function_temps_in_lvalue(target, temps);
            }
            for value in &assign.values {
                collect_function_temps_in_expr(value, temps);
            }
        }
        AstStmt::CallStmt(call_stmt) => collect_function_temps_in_call(&call_stmt.call, temps),
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_function_temps_in_expr(value, temps);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_function_temps_in_expr(&if_stmt.cond, temps);
            collect_function_temps_in_block(&if_stmt.then_block)
                .into_iter()
                .for_each(|temp| {
                    temps.insert(temp);
                });
            if let Some(else_block) = &if_stmt.else_block {
                collect_function_temps_in_block(else_block)
                    .into_iter()
                    .for_each(|temp| {
                        temps.insert(temp);
                    });
            }
        }
        AstStmt::While(while_stmt) => {
            collect_function_temps_in_expr(&while_stmt.cond, temps);
            collect_function_temps_in_block(&while_stmt.body)
                .into_iter()
                .for_each(|temp| {
                    temps.insert(temp);
                });
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_function_temps_in_block(&repeat_stmt.body)
                .into_iter()
                .for_each(|temp| {
                    temps.insert(temp);
                });
            collect_function_temps_in_expr(&repeat_stmt.cond, temps);
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_function_temps_in_expr(&numeric_for.start, temps);
            collect_function_temps_in_expr(&numeric_for.limit, temps);
            collect_function_temps_in_expr(&numeric_for.step, temps);
            collect_function_temps_in_block(&numeric_for.body)
                .into_iter()
                .for_each(|temp| {
                    temps.insert(temp);
                });
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_function_temps_in_expr(expr, temps);
            }
            collect_function_temps_in_block(&generic_for.body)
                .into_iter()
                .for_each(|temp| {
                    temps.insert(temp);
                });
        }
        AstStmt::DoBlock(block) => {
            collect_function_temps_in_block(block)
                .into_iter()
                .for_each(|temp| {
                    temps.insert(temp);
                });
        }
        AstStmt::FunctionDecl(function_decl) => {
            collect_function_temps_in_function_name(&function_decl.target, temps)
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            if let AstBindingRef::Temp(temp) = local_function_decl.name {
                temps.insert(temp);
            }
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
    }
}

fn collect_function_temps_in_function_name(
    target: &super::super::common::AstFunctionName,
    temps: &mut BTreeSet<TempId>,
) {
    let path = match target {
        super::super::common::AstFunctionName::Plain(path) => path,
        super::super::common::AstFunctionName::Method(path, _) => path,
    };
    if let AstNameRef::Temp(temp) = path.root {
        temps.insert(temp);
    }
}

fn collect_function_temps_in_call(call: &AstCallKind, temps: &mut BTreeSet<TempId>) {
    match call {
        AstCallKind::Call(call) => {
            collect_function_temps_in_expr(&call.callee, temps);
            for arg in &call.args {
                collect_function_temps_in_expr(arg, temps);
            }
        }
        AstCallKind::MethodCall(call) => {
            collect_function_temps_in_expr(&call.receiver, temps);
            for arg in &call.args {
                collect_function_temps_in_expr(arg, temps);
            }
        }
    }
}

fn collect_function_temps_in_lvalue(target: &AstLValue, temps: &mut BTreeSet<TempId>) {
    match target {
        AstLValue::Name(AstNameRef::Temp(temp)) => {
            temps.insert(*temp);
        }
        AstLValue::Name(_) => {}
        AstLValue::FieldAccess(access) => collect_function_temps_in_expr(&access.base, temps),
        AstLValue::IndexAccess(access) => {
            collect_function_temps_in_expr(&access.base, temps);
            collect_function_temps_in_expr(&access.index, temps);
        }
    }
}

fn collect_function_temps_in_expr(expr: &AstExpr, temps: &mut BTreeSet<TempId>) {
    match expr {
        AstExpr::Var(AstNameRef::Temp(temp)) => {
            temps.insert(*temp);
        }
        AstExpr::FieldAccess(access) => collect_function_temps_in_expr(&access.base, temps),
        AstExpr::IndexAccess(access) => {
            collect_function_temps_in_expr(&access.base, temps);
            collect_function_temps_in_expr(&access.index, temps);
        }
        AstExpr::Unary(unary) => collect_function_temps_in_expr(&unary.expr, temps),
        AstExpr::Binary(binary) => {
            collect_function_temps_in_expr(&binary.lhs, temps);
            collect_function_temps_in_expr(&binary.rhs, temps);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_function_temps_in_expr(&logical.lhs, temps);
            collect_function_temps_in_expr(&logical.rhs, temps);
        }
        AstExpr::Call(call) => {
            collect_function_temps_in_expr(&call.callee, temps);
            for arg in &call.args {
                collect_function_temps_in_expr(arg, temps);
            }
        }
        AstExpr::MethodCall(call) => {
            collect_function_temps_in_expr(&call.receiver, temps);
            for arg in &call.args {
                collect_function_temps_in_expr(arg, temps);
            }
        }
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    AstTableField::Array(value) => collect_function_temps_in_expr(value, temps),
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &record.key {
                            collect_function_temps_in_expr(key, temps);
                        }
                        collect_function_temps_in_expr(&record.value, temps);
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

fn rewrite_function_block(block: &mut AstBlock, mapping: &BTreeMap<TempId, AstSyntheticLocalId>) {
    for stmt in &mut block.stmts {
        rewrite_function_stmt(stmt, mapping);
    }
}

fn rewrite_function_stmt(stmt: &mut AstStmt, mapping: &BTreeMap<TempId, AstSyntheticLocalId>) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &mut local_decl.bindings {
                if let AstBindingRef::Temp(temp) = binding.id
                    && let Some(&synthetic) = mapping.get(&temp)
                {
                    binding.id = AstBindingRef::SyntheticLocal(synthetic);
                }
            }
            for value in &mut local_decl.values {
                rewrite_function_expr(value, mapping);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &mut global_decl.values {
                rewrite_function_expr(value, mapping);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &mut assign.targets {
                rewrite_function_lvalue(target, mapping);
            }
            for value in &mut assign.values {
                rewrite_function_expr(value, mapping);
            }
        }
        AstStmt::CallStmt(call_stmt) => rewrite_function_call(&mut call_stmt.call, mapping),
        AstStmt::Return(ret) => {
            for value in &mut ret.values {
                rewrite_function_expr(value, mapping);
            }
        }
        AstStmt::If(if_stmt) => {
            rewrite_function_expr(&mut if_stmt.cond, mapping);
            rewrite_function_block(&mut if_stmt.then_block, mapping);
            if let Some(else_block) = &mut if_stmt.else_block {
                rewrite_function_block(else_block, mapping);
            }
        }
        AstStmt::While(while_stmt) => {
            rewrite_function_expr(&mut while_stmt.cond, mapping);
            rewrite_function_block(&mut while_stmt.body, mapping);
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_function_block(&mut repeat_stmt.body, mapping);
            rewrite_function_expr(&mut repeat_stmt.cond, mapping);
        }
        AstStmt::NumericFor(numeric_for) => {
            rewrite_function_expr(&mut numeric_for.start, mapping);
            rewrite_function_expr(&mut numeric_for.limit, mapping);
            rewrite_function_expr(&mut numeric_for.step, mapping);
            rewrite_function_block(&mut numeric_for.body, mapping);
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &mut generic_for.iterator {
                rewrite_function_expr(expr, mapping);
            }
            rewrite_function_block(&mut generic_for.body, mapping);
        }
        AstStmt::DoBlock(block) => rewrite_function_block(block, mapping),
        AstStmt::FunctionDecl(function_decl) => {
            rewrite_function_name(&mut function_decl.target, mapping)
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            if let AstBindingRef::Temp(temp) = local_function_decl.name
                && let Some(&synthetic) = mapping.get(&temp)
            {
                local_function_decl.name = AstBindingRef::SyntheticLocal(synthetic);
            }
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
    }
}

fn rewrite_function_name(
    target: &mut super::super::common::AstFunctionName,
    mapping: &BTreeMap<TempId, AstSyntheticLocalId>,
) {
    let path = match target {
        super::super::common::AstFunctionName::Plain(path) => path,
        super::super::common::AstFunctionName::Method(path, _) => path,
    };
    rewrite_name_ref(&mut path.root, mapping);
}

fn rewrite_function_call(call: &mut AstCallKind, mapping: &BTreeMap<TempId, AstSyntheticLocalId>) {
    match call {
        AstCallKind::Call(call) => {
            rewrite_function_expr(&mut call.callee, mapping);
            for arg in &mut call.args {
                rewrite_function_expr(arg, mapping);
            }
        }
        AstCallKind::MethodCall(call) => {
            rewrite_function_expr(&mut call.receiver, mapping);
            for arg in &mut call.args {
                rewrite_function_expr(arg, mapping);
            }
        }
    }
}

fn rewrite_function_lvalue(
    target: &mut AstLValue,
    mapping: &BTreeMap<TempId, AstSyntheticLocalId>,
) {
    match target {
        AstLValue::Name(name) => rewrite_name_ref(name, mapping),
        AstLValue::FieldAccess(access) => rewrite_function_expr(&mut access.base, mapping),
        AstLValue::IndexAccess(access) => {
            rewrite_function_expr(&mut access.base, mapping);
            rewrite_function_expr(&mut access.index, mapping);
        }
    }
}

fn rewrite_function_expr(expr: &mut AstExpr, mapping: &BTreeMap<TempId, AstSyntheticLocalId>) {
    match expr {
        AstExpr::Var(name) => rewrite_name_ref(name, mapping),
        AstExpr::FieldAccess(access) => rewrite_function_expr(&mut access.base, mapping),
        AstExpr::IndexAccess(access) => {
            rewrite_function_expr(&mut access.base, mapping);
            rewrite_function_expr(&mut access.index, mapping);
        }
        AstExpr::Unary(unary) => rewrite_function_expr(&mut unary.expr, mapping),
        AstExpr::Binary(binary) => {
            rewrite_function_expr(&mut binary.lhs, mapping);
            rewrite_function_expr(&mut binary.rhs, mapping);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            rewrite_function_expr(&mut logical.lhs, mapping);
            rewrite_function_expr(&mut logical.rhs, mapping);
        }
        AstExpr::Call(call) => {
            rewrite_function_expr(&mut call.callee, mapping);
            for arg in &mut call.args {
                rewrite_function_expr(arg, mapping);
            }
        }
        AstExpr::MethodCall(call) => {
            rewrite_function_expr(&mut call.receiver, mapping);
            for arg in &mut call.args {
                rewrite_function_expr(arg, mapping);
            }
        }
        AstExpr::TableConstructor(table) => {
            for field in &mut table.fields {
                match field {
                    AstTableField::Array(value) => rewrite_function_expr(value, mapping),
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &mut record.key {
                            rewrite_function_expr(key, mapping);
                        }
                        rewrite_function_expr(&mut record.value, mapping);
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
        | AstExpr::VarArg => {}
    }
}

fn rewrite_name_ref(name: &mut AstNameRef, mapping: &BTreeMap<TempId, AstSyntheticLocalId>) {
    if let AstNameRef::Temp(temp) = name
        && let Some(&synthetic) = mapping.get(temp)
    {
        *name = AstNameRef::SyntheticLocal(synthetic);
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{
        AstBindingRef, AstBlock, AstExpr, AstLocalAttr, AstLocalBinding, AstLocalDecl, AstModule,
        AstNameRef, AstReturn, AstStmt,
    };
    use crate::hir::{HirProtoRef, TempId};

    #[test]
    fn materializes_remaining_temps_into_synthetic_locals() {
        let temp = TempId(2);
        let mut module = AstModule {
            entry_function: HirProtoRef(0),
            body: AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: AstBindingRef::Temp(temp),
                            attr: AstLocalAttr::None,
                        }],
                        values: vec![AstExpr::Boolean(true)],
                    })),
                    AstStmt::Return(Box::new(AstReturn {
                        values: vec![AstExpr::Var(AstNameRef::Temp(temp))],
                    })),
                ],
            },
        };

        let changed = super::apply(
            &mut module,
            super::ReadabilityContext {
                target: crate::ast::AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
                options: crate::readability::ReadabilityOptions::default(),
            },
        );

        assert!(changed);
        let AstStmt::LocalDecl(local_decl) = &module.body.stmts[0] else {
            panic!("first stmt should stay local decl");
        };
        assert!(matches!(
            local_decl.bindings[0].id,
            AstBindingRef::SyntheticLocal(_)
        ));
        let AstStmt::Return(ret) = &module.body.stmts[1] else {
            panic!("second stmt should stay return");
        };
        assert!(matches!(
            ret.values[0],
            AstExpr::Var(AstNameRef::SyntheticLocal(_))
        ));
    }
}
