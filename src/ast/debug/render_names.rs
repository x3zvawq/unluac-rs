//! 收集函数快照内 local/upvalue/synthetic binding 的稳定显示编号；依赖 AST 遍历，不负责输出语法；例如为缺失 debug 名的绑定分配一致编号。

use super::*;

pub(super) fn collect_function_render_names(block: &AstBlock) -> FunctionRenderNames {
    let mut max_local = None::<usize>;
    let mut synthetic_locals = BTreeSet::new();
    collect_function_render_names_in_block(block, &mut max_local, &mut synthetic_locals);
    let start_index = max_local.map_or(0, |index| index + 1);
    let synthetic_locals = synthetic_locals
        .into_iter()
        .enumerate()
        .map(|(offset, local)| (local, start_index + offset))
        .collect();
    FunctionRenderNames { synthetic_locals }
}

pub(super) fn collect_function_render_names_in_block(
    block: &AstBlock,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    for stmt in &block.stmts {
        collect_function_render_names_in_stmt(stmt, max_local, synthetic_locals);
    }
}

pub(super) fn collect_function_render_names_in_stmt(
    stmt: &AstStmt,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                collect_binding_ref(binding.id, max_local, synthetic_locals);
            }
            for value in &local_decl.values {
                collect_function_render_names_in_expr(value, max_local, synthetic_locals);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_function_render_names_in_expr(value, max_local, synthetic_locals);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_function_render_names_in_lvalue(target, max_local, synthetic_locals);
            }
            for value in &assign.values {
                collect_function_render_names_in_expr(value, max_local, synthetic_locals);
            }
        }
        AstStmt::CallStmt(call_stmt) => {
            collect_function_render_names_in_call(&call_stmt.call, max_local, synthetic_locals);
        }
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_function_render_names_in_expr(value, max_local, synthetic_locals);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_function_render_names_in_expr(&if_stmt.cond, max_local, synthetic_locals);
            collect_function_render_names_in_block(
                &if_stmt.then_block,
                max_local,
                synthetic_locals,
            );
            if let Some(else_block) = &if_stmt.else_block {
                collect_function_render_names_in_block(else_block, max_local, synthetic_locals);
            }
        }
        AstStmt::While(while_stmt) => {
            collect_function_render_names_in_expr(&while_stmt.cond, max_local, synthetic_locals);
            collect_function_render_names_in_block(&while_stmt.body, max_local, synthetic_locals);
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_function_render_names_in_block(&repeat_stmt.body, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&repeat_stmt.cond, max_local, synthetic_locals);
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_binding_ref(numeric_for.binding, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&numeric_for.start, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&numeric_for.limit, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&numeric_for.step, max_local, synthetic_locals);
            collect_function_render_names_in_block(&numeric_for.body, max_local, synthetic_locals);
        }
        AstStmt::GenericFor(generic_for) => {
            for binding in &generic_for.bindings {
                collect_binding_ref(*binding, max_local, synthetic_locals);
            }
            for iterator in &generic_for.iterator {
                collect_function_render_names_in_expr(iterator, max_local, synthetic_locals);
            }
            collect_function_render_names_in_block(&generic_for.body, max_local, synthetic_locals);
        }
        AstStmt::DoBlock(block) => {
            collect_function_render_names_in_block(block, max_local, synthetic_locals);
        }
        AstStmt::FunctionDecl(function_decl) => {
            collect_function_render_names_in_function_name(
                &function_decl.target,
                max_local,
                synthetic_locals,
            );
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            collect_binding_ref(local_function_decl.name, max_local, synthetic_locals);
        }
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => {}
    }
}

pub(super) fn collect_function_render_names_in_function_name(
    target: &AstFunctionName,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    let path = match target {
        AstFunctionName::Plain(path) => path,
        AstFunctionName::Method(path, _) => path,
    };
    collect_name_ref(&path.root, max_local, synthetic_locals);
}

pub(super) fn collect_function_render_names_in_call(
    call: &AstCallKind,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    match call {
        AstCallKind::Call(call) => {
            collect_function_render_names_in_expr(&call.callee, max_local, synthetic_locals);
            for arg in &call.args {
                collect_function_render_names_in_expr(arg, max_local, synthetic_locals);
            }
        }
        AstCallKind::MethodCall(call) => {
            collect_function_render_names_in_expr(&call.receiver, max_local, synthetic_locals);
            for arg in &call.args {
                collect_function_render_names_in_expr(arg, max_local, synthetic_locals);
            }
        }
    }
}

pub(super) fn collect_function_render_names_in_lvalue(
    target: &AstLValue,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    match target {
        AstLValue::Name(name) => collect_name_ref(name, max_local, synthetic_locals),
        AstLValue::FieldAccess(access) => {
            collect_function_render_names_in_expr(&access.base, max_local, synthetic_locals);
        }
        AstLValue::IndexAccess(access) => {
            collect_function_render_names_in_expr(&access.base, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&access.index, max_local, synthetic_locals);
        }
    }
}

pub(super) fn collect_function_render_names_in_expr(
    expr: &AstExpr,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    match expr {
        AstExpr::Var(name) => collect_name_ref(name, max_local, synthetic_locals),
        AstExpr::FieldAccess(access) => {
            collect_function_render_names_in_expr(&access.base, max_local, synthetic_locals);
        }
        AstExpr::IndexAccess(access) => {
            collect_function_render_names_in_expr(&access.base, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&access.index, max_local, synthetic_locals);
        }
        AstExpr::Unary(unary) => {
            collect_function_render_names_in_expr(&unary.expr, max_local, synthetic_locals);
        }
        AstExpr::Binary(binary) => {
            collect_function_render_names_in_expr(&binary.lhs, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&binary.rhs, max_local, synthetic_locals);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_function_render_names_in_expr(&logical.lhs, max_local, synthetic_locals);
            collect_function_render_names_in_expr(&logical.rhs, max_local, synthetic_locals);
        }
        AstExpr::Call(call) => {
            collect_function_render_names_in_expr(&call.callee, max_local, synthetic_locals);
            for arg in &call.args {
                collect_function_render_names_in_expr(arg, max_local, synthetic_locals);
            }
        }
        AstExpr::MethodCall(call) => {
            collect_function_render_names_in_expr(&call.receiver, max_local, synthetic_locals);
            for arg in &call.args {
                collect_function_render_names_in_expr(arg, max_local, synthetic_locals);
            }
        }
        AstExpr::SingleValue(expr) => {
            collect_function_render_names_in_expr(expr, max_local, synthetic_locals);
        }
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    AstTableField::Array(value) => {
                        collect_function_render_names_in_expr(value, max_local, synthetic_locals);
                    }
                    AstTableField::Record(record) => {
                        if let super::super::common::AstTableKey::Expr(key) = &record.key {
                            collect_function_render_names_in_expr(key, max_local, synthetic_locals);
                        }
                        collect_function_render_names_in_expr(
                            &record.value,
                            max_local,
                            synthetic_locals,
                        );
                    }
                }
            }
        }
        AstExpr::FunctionExpr(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg
        | AstExpr::Error(_) => {}
    }
}

pub(super) fn collect_name_ref(
    name: &AstNameRef,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    match name {
        AstNameRef::Local(local) => update_max_local(max_local, *local),
        AstNameRef::SyntheticLocal(local) => {
            synthetic_locals.insert(*local);
        }
        AstNameRef::Param(_)
        | AstNameRef::Temp(_)
        | AstNameRef::Upvalue(_)
        | AstNameRef::Global(_) => {}
    }
}

pub(super) fn collect_binding_ref(
    binding: AstBindingRef,
    max_local: &mut Option<usize>,
    synthetic_locals: &mut BTreeSet<AstSyntheticLocalId>,
) {
    match binding {
        AstBindingRef::Local(local) => update_max_local(max_local, local),
        AstBindingRef::SyntheticLocal(local) => {
            synthetic_locals.insert(local);
        }
        AstBindingRef::Temp(_) => {}
    }
}

pub(super) fn update_max_local(max_local: &mut Option<usize>, local: LocalId) {
    let index = local.index();
    *max_local = Some(max_local.map_or(index, |current| current.max(index)));
}
