//! 这个文件负责从 AST 结构收集 naming hint。
//!
//! 这些 hint 不是必需信息，但它们能让 `Simple/Heuristic` 比纯 fallback 更接近源码：
//! 例如 `self`、loop 角色、field/table/function/result 形状等。

use std::collections::BTreeMap;

use crate::ast::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue,
    AstLocalFunctionDecl, AstMethodCallExpr, AstModule, AstNameRef, AstStmt, AstSyntheticLocalId,
    AstTableField, AstTableKey,
};
use crate::hir::{HirModule, HirProtoRef, ParamId};

use super::NamingError;
use super::common::{CandidateHint, FunctionHints, LoopContext, NameSource};
use super::support::normalize_identifier;
use super::validate::ensure_function_exists;

/// 收集整模块的 function hints。
pub(super) fn collect_function_hints(
    module: &AstModule,
    hir: &HirModule,
    hints: &mut [FunctionHints],
) -> Result<(), NamingError> {
    ensure_function_exists(hir, module.entry_function)?;
    collect_block_hints(
        module.entry_function,
        &module.body,
        hints,
        LoopContext::default(),
        hir,
    )
}

fn collect_block_hints(
    function: HirProtoRef,
    block: &AstBlock,
    hints: &mut [FunctionHints],
    loop_ctx: LoopContext,
    hir: &HirModule,
) -> Result<(), NamingError> {
    for stmt in &block.stmts {
        collect_stmt_hints(function, stmt, hints, loop_ctx, hir)?;
    }
    Ok(())
}

fn collect_stmt_hints(
    function: HirProtoRef,
    stmt: &AstStmt,
    hints: &mut [FunctionHints],
    loop_ctx: LoopContext,
    hir: &HirModule,
) -> Result<(), NamingError> {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_expr_hints(function, value, hints, hir)?;
            }
            for binding in &local_decl.bindings {
                record_binding_presence(function, binding.id, hints);
            }
            for (binding, value) in local_decl.bindings.iter().zip(local_decl.values.iter()) {
                register_binding_expr_hint(function, binding.id, value, hints);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_expr_hints(function, value, hints, hir)?;
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_hints(function, target, hints, hir)?;
            }
            for value in &assign.values {
                collect_expr_hints(function, value, hints, hir)?;
            }
            if let ([AstLValue::Name(name)], [value]) =
                (assign.targets.as_slice(), assign.values.as_slice())
                && let Some(binding) = binding_from_name_ref(name)
            {
                record_binding_presence(function, binding, hints);
                register_binding_expr_hint(function, binding, value, hints);
            }
        }
        AstStmt::CallStmt(call_stmt) => collect_call_hints(function, &call_stmt.call, hints, hir)?,
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_hints(function, value, hints, hir)?;
            }
        }
        AstStmt::If(if_stmt) => {
            collect_expr_hints(function, &if_stmt.cond, hints, hir)?;
            collect_block_hints(function, &if_stmt.then_block, hints, loop_ctx, hir)?;
            if let Some(else_block) = &if_stmt.else_block {
                collect_block_hints(function, else_block, hints, loop_ctx, hir)?;
            }
        }
        AstStmt::While(while_stmt) => {
            collect_expr_hints(function, &while_stmt.cond, hints, hir)?;
            collect_block_hints(function, &while_stmt.body, hints, loop_ctx, hir)?;
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_block_hints(function, &repeat_stmt.body, hints, loop_ctx, hir)?;
            collect_expr_hints(function, &repeat_stmt.cond, hints, hir)?;
        }
        AstStmt::NumericFor(numeric_for) => {
            let candidate = numeric_loop_name(loop_ctx.numeric_depth);
            register_binding_hint(
                function,
                numeric_for.binding,
                candidate,
                NameSource::LoopRole,
                hints,
            );
            collect_expr_hints(function, &numeric_for.start, hints, hir)?;
            collect_expr_hints(function, &numeric_for.limit, hints, hir)?;
            collect_expr_hints(function, &numeric_for.step, hints, hir)?;
            collect_block_hints(
                function,
                &numeric_for.body,
                hints,
                LoopContext {
                    numeric_depth: loop_ctx.numeric_depth + 1,
                },
                hir,
            )?;
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_expr_hints(function, expr, hints, hir)?;
            }
            for (index, binding) in generic_for.bindings.iter().copied().enumerate() {
                let candidate = match index {
                    0 if generic_for.bindings.len() == 1 => "item",
                    0 => "k",
                    1 => "v",
                    _ => "extra",
                };
                register_binding_hint(function, binding, candidate, NameSource::LoopRole, hints);
            }
            collect_block_hints(function, &generic_for.body, hints, loop_ctx, hir)?;
        }
        AstStmt::DoBlock(block) => collect_block_hints(function, block, hints, loop_ctx, hir)?,
        AstStmt::FunctionDecl(function_decl) => {
            if matches!(function_decl.target, AstFunctionName::Method(_, _))
                && let Some(first_param) = function_decl.func.params.first().copied()
            {
                register_param_hint(
                    function_decl.func.function,
                    first_param,
                    "self",
                    NameSource::SelfParam,
                    hints,
                );
            }
            collect_function_expr_hints(&function_decl.func, hints, hir)?;
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            register_binding_hint(
                function,
                local_function_decl.name,
                "fn",
                NameSource::FunctionShape,
                hints,
            );
            collect_local_function_hints(local_function_decl, hints, hir)?;
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
    }
    Ok(())
}

fn collect_local_function_hints(
    function_decl: &AstLocalFunctionDecl,
    hints: &mut [FunctionHints],
    hir: &HirModule,
) -> Result<(), NamingError> {
    collect_function_expr_hints(&function_decl.func, hints, hir)
}

fn collect_function_expr_hints(
    function: &AstFunctionExpr,
    hints: &mut [FunctionHints],
    hir: &HirModule,
) -> Result<(), NamingError> {
    ensure_function_exists(hir, function.function)?;
    collect_block_hints(
        function.function,
        &function.body,
        hints,
        LoopContext::default(),
        hir,
    )
}

fn collect_call_hints(
    function: HirProtoRef,
    call: &AstCallKind,
    hints: &mut [FunctionHints],
    hir: &HirModule,
) -> Result<(), NamingError> {
    match call {
        AstCallKind::Call(call) => {
            collect_expr_hints(function, &call.callee, hints, hir)?;
            for arg in &call.args {
                collect_expr_hints(function, arg, hints, hir)?;
            }
        }
        AstCallKind::MethodCall(call) => {
            collect_expr_hints(function, &call.receiver, hints, hir)?;
            for arg in &call.args {
                collect_expr_hints(function, arg, hints, hir)?;
            }
        }
    }
    Ok(())
}

fn collect_lvalue_hints(
    function: HirProtoRef,
    target: &AstLValue,
    hints: &mut [FunctionHints],
    hir: &HirModule,
) -> Result<(), NamingError> {
    match target {
        AstLValue::Name(AstNameRef::SyntheticLocal(local)) => {
            record_synthetic_local(function, *local, hints);
            Ok(())
        }
        AstLValue::Name(_) => Ok(()),
        AstLValue::FieldAccess(access) => collect_expr_hints(function, &access.base, hints, hir),
        AstLValue::IndexAccess(access) => {
            collect_expr_hints(function, &access.base, hints, hir)?;
            collect_expr_hints(function, &access.index, hints, hir)
        }
    }
}

fn collect_expr_hints(
    function: HirProtoRef,
    expr: &AstExpr,
    hints: &mut [FunctionHints],
    hir: &HirModule,
) -> Result<(), NamingError> {
    match expr {
        AstExpr::FieldAccess(access) => collect_expr_hints(function, &access.base, hints, hir),
        AstExpr::IndexAccess(access) => {
            collect_expr_hints(function, &access.base, hints, hir)?;
            collect_expr_hints(function, &access.index, hints, hir)
        }
        AstExpr::Unary(unary) => collect_expr_hints(function, &unary.expr, hints, hir),
        AstExpr::Binary(binary) => {
            collect_expr_hints(function, &binary.lhs, hints, hir)?;
            collect_expr_hints(function, &binary.rhs, hints, hir)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_expr_hints(function, &logical.lhs, hints, hir)?;
            collect_expr_hints(function, &logical.rhs, hints, hir)
        }
        AstExpr::Call(call) => {
            collect_expr_hints(function, &call.callee, hints, hir)?;
            for arg in &call.args {
                collect_expr_hints(function, arg, hints, hir)?;
            }
            Ok(())
        }
        AstExpr::MethodCall(call) => collect_method_call_hints(function, call, hints, hir),
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    AstTableField::Array(value) => collect_expr_hints(function, value, hints, hir)?,
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &record.key {
                            collect_expr_hints(function, key, hints, hir)?;
                        }
                        collect_expr_hints(function, &record.value, hints, hir)?;
                    }
                }
            }
            Ok(())
        }
        AstExpr::FunctionExpr(function_expr) => {
            collect_function_expr_hints(function_expr, hints, hir)
        }
        AstExpr::Var(AstNameRef::SyntheticLocal(local)) => {
            record_synthetic_local(function, *local, hints);
            Ok(())
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => Ok(()),
    }
}

fn collect_method_call_hints(
    function: HirProtoRef,
    call: &AstMethodCallExpr,
    hints: &mut [FunctionHints],
    hir: &HirModule,
) -> Result<(), NamingError> {
    collect_expr_hints(function, &call.receiver, hints, hir)?;
    for arg in &call.args {
        collect_expr_hints(function, arg, hints, hir)?;
    }
    Ok(())
}

fn register_binding_expr_hint(
    function: HirProtoRef,
    binding: AstBindingRef,
    expr: &AstExpr,
    hints: &mut [FunctionHints],
) {
    record_binding_presence(function, binding, hints);
    let Some((candidate, source)) = candidate_from_expr(expr) else {
        return;
    };
    register_binding_hint(function, binding, &candidate, source, hints);
}

fn record_binding_presence(
    function: HirProtoRef,
    binding: AstBindingRef,
    hints: &mut [FunctionHints],
) {
    if let AstBindingRef::SyntheticLocal(local) = binding {
        record_synthetic_local(function, local, hints);
    }
}

fn register_binding_hint(
    function: HirProtoRef,
    binding: AstBindingRef,
    candidate: &str,
    source: NameSource,
    hints: &mut [FunctionHints],
) {
    match binding {
        AstBindingRef::Local(local) => {
            register_local_hint(function, local, candidate, source, hints)
        }
        AstBindingRef::SyntheticLocal(local) => {
            register_synthetic_local_hint(function, local, candidate, source, hints)
        }
        AstBindingRef::Temp(_) => {
            unreachable!("readability output must not leak raw temp bindings into naming")
        }
    }
}

fn register_param_hint(
    function: HirProtoRef,
    param: ParamId,
    candidate: &str,
    source: NameSource,
    hints: &mut [FunctionHints],
) {
    let Some(candidate) = normalize_identifier(candidate) else {
        return;
    };
    let function_hints = &mut hints[function.index()];
    insert_hint(&mut function_hints.param_hints, param, candidate, source);
}

fn register_local_hint(
    function: HirProtoRef,
    local: crate::hir::LocalId,
    candidate: &str,
    source: NameSource,
    hints: &mut [FunctionHints],
) {
    let Some(candidate) = normalize_identifier(candidate) else {
        return;
    };
    let function_hints = &mut hints[function.index()];
    insert_hint(&mut function_hints.local_hints, local, candidate, source);
}

fn register_synthetic_local_hint(
    function: HirProtoRef,
    local: AstSyntheticLocalId,
    candidate: &str,
    source: NameSource,
    hints: &mut [FunctionHints],
) {
    let Some(candidate) = normalize_identifier(candidate) else {
        return;
    };
    let function_hints = &mut hints[function.index()];
    function_hints.synthetic_locals.insert(local);
    insert_hint(
        &mut function_hints.synthetic_local_hints,
        local,
        candidate,
        source,
    );
}

fn record_synthetic_local(
    function: HirProtoRef,
    local: AstSyntheticLocalId,
    hints: &mut [FunctionHints],
) {
    hints[function.index()].synthetic_locals.insert(local);
}

fn insert_hint<K>(
    map: &mut BTreeMap<K, CandidateHint>,
    key: K,
    candidate: String,
    source: NameSource,
) where
    K: Ord,
{
    let should_replace = map
        .get(&key)
        .map(|existing| hint_priority(source) > hint_priority(existing.source))
        .unwrap_or(true);
    if should_replace {
        map.insert(
            key,
            CandidateHint {
                text: candidate,
                source,
            },
        );
    }
}

fn hint_priority(source: NameSource) -> usize {
    match source {
        NameSource::Debug => 100,
        NameSource::CaptureProvenance => 95,
        NameSource::SelfParam => 90,
        NameSource::LoopRole => 80,
        NameSource::FieldName => 70,
        NameSource::TableShape | NameSource::BoolShape | NameSource::FunctionShape => 60,
        NameSource::ResultShape => 50,
        NameSource::Discard => 20,
        NameSource::DebugLike | NameSource::Simple | NameSource::ConflictFallback => 10,
    }
}

fn candidate_from_expr(expr: &AstExpr) -> Option<(String, NameSource)> {
    match expr {
        AstExpr::FieldAccess(access) => {
            Some((normalize_identifier(&access.field)?, NameSource::FieldName))
        }
        AstExpr::IndexAccess(access) => Some((
            normalize_identifier(&candidate_from_index_base(&access.base)?)?,
            NameSource::FieldName,
        )),
        AstExpr::TableConstructor(_) => Some(("tbl".to_owned(), NameSource::TableShape)),
        AstExpr::FunctionExpr(_) => Some(("fn".to_owned(), NameSource::FunctionShape)),
        AstExpr::Call(_) | AstExpr::MethodCall(_) => {
            Some(("result".to_owned(), NameSource::ResultShape))
        }
        AstExpr::Boolean(_)
        | AstExpr::LogicalAnd(_)
        | AstExpr::LogicalOr(_)
        | AstExpr::Unary(_)
        | AstExpr::Binary(_) => Some(("ok".to_owned(), NameSource::BoolShape)),
        AstExpr::Var(AstNameRef::Global(global)) => {
            Some((normalize_identifier(&global.text)?, NameSource::FieldName))
        }
        AstExpr::Nil
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => None,
    }
}

fn candidate_from_index_base(base: &AstExpr) -> Option<String> {
    match base {
        AstExpr::FieldAccess(access) => Some(singularize_field_name(&access.field)),
        AstExpr::IndexAccess(access) => candidate_from_index_base(&access.base),
        AstExpr::Var(AstNameRef::Global(global)) => normalize_identifier(&global.text),
        AstExpr::Var(_) => Some("item".to_owned()),
        _ => None,
    }
}

fn singularize_field_name(field: &str) -> String {
    let singular = if let Some(stem) = field.strip_suffix("ies") {
        format!("{stem}y")
    } else if let Some(stem) = field.strip_suffix("ches") {
        format!("{stem}ch")
    } else if let Some(stem) = field.strip_suffix("shes") {
        format!("{stem}sh")
    } else if let Some(stem) = field.strip_suffix("sses") {
        format!("{stem}ss")
    } else if let Some(stem) = field.strip_suffix("xes") {
        format!("{stem}x")
    } else if field.len() > 1 {
        field.strip_suffix('s').unwrap_or(field).to_owned()
    } else {
        field.to_owned()
    };
    normalize_identifier(&singular).unwrap_or_else(|| "item".to_owned())
}

fn binding_from_name_ref(name: &AstNameRef) -> Option<AstBindingRef> {
    match name {
        AstNameRef::Local(local) => Some(AstBindingRef::Local(*local)),
        AstNameRef::SyntheticLocal(local) => Some(AstBindingRef::SyntheticLocal(*local)),
        AstNameRef::Temp(_) => {
            unreachable!("readability output must not leak raw temp refs into naming")
        }
        AstNameRef::Param(_) | AstNameRef::Upvalue(_) | AstNameRef::Global(_) => None,
    }
}

fn numeric_loop_name(depth: usize) -> &'static str {
    match depth {
        0 => "i",
        1 => "j",
        2 => "k",
        3 => "n",
        _ => "idx",
    }
}
