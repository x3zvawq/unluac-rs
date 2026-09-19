//! 从最终 AST 收集命名提示，区分基础语法角色与 heuristic 的形状、调用和用途线索。
//! 同级冲突保留歧义，不让遍历顺序决定名称；提示不参与语义改写或 binding 身份恢复。

use std::collections::BTreeMap;

use crate::ast::traverse::{traverse_call_children, traverse_lvalue_children};
use crate::ast::visit::{ExprNode, expr_nodes};
use crate::ast::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue,
    AstModule, AstNameRef, AstStmt, AstSyntheticLocalId,
};
use crate::hir::{HirProtoRef, ParamId};

use super::common::{CandidateHint, FunctionHints, HintChoice, LoopContext, NameSource};
use super::support::normalize_identifier;

mod expressions;
mod stdlib;
use expressions::{candidate_from_expr, field_name, initializer_for_slot};

/// 收集已通过 Naming 入口校验的最终 AST hints；不再查询 HIR 身份。
pub(super) fn collect_function_hints(module: &AstModule, hints: &mut [FunctionHints]) {
    collect_block_hints(
        module.entry_function,
        &module.body,
        hints,
        LoopContext::default(),
    );
    if hints[module.entry_function.index()].heuristic {
        stdlib::collect_hints(module, hints);
    }
}

fn collect_block_hints(
    function: HirProtoRef,
    block: &AstBlock,
    hints: &mut [FunctionHints],
    loop_ctx: LoopContext,
) {
    for stmt in &block.stmts {
        collect_stmt_hints(function, stmt, hints, loop_ctx);
    }
}

fn collect_stmt_hints(
    function: HirProtoRef,
    stmt: &AstStmt,
    hints: &mut [FunctionHints],
    loop_ctx: LoopContext,
) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_expr_hints(function, value, hints);
            }
            for binding in &local_decl.bindings {
                record_binding_presence(function, binding.id, hints);
            }
            for (index, binding) in local_decl.bindings.iter().enumerate() {
                if let Some(value) = initializer_for_slot(&local_decl.values, index) {
                    register_binding_expr_hint(function, binding.id, value, hints);
                }
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_expr_hints(function, value, hints);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_hints(function, target, hints);
            }
            for value in &assign.values {
                collect_expr_hints(function, value, hints);
            }
            for (index, target) in assign.targets.iter().enumerate() {
                if let Some(value) = initializer_for_slot(&assign.values, index) {
                    if let AstLValue::Name(name) = target
                        && let Some(binding) = final_binding_from_name_ref(name)
                    {
                        register_binding_expr_hint(function, binding, value, hints);
                    }
                    // 开放多返回尾包的每个位置没有独立 AST operand，不能把同一
                    // callee 误当作这些字段的源码变量。
                    if index < assign.values.len() {
                        register_usage_hint(function, value, field_name(target), hints);
                    }
                }
            }
        }
        AstStmt::CallStmt(call_stmt) => collect_call_hints(function, &call_stmt.call, hints),
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_hints(function, value, hints);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_expr_hints(function, &if_stmt.cond, hints);
            collect_block_hints(function, &if_stmt.then_block, hints, loop_ctx);
            if let Some(else_block) = &if_stmt.else_block {
                collect_block_hints(function, else_block, hints, loop_ctx);
            }
        }
        AstStmt::While(while_stmt) => {
            collect_expr_hints(function, &while_stmt.cond, hints);
            collect_block_hints(function, &while_stmt.body, hints, loop_ctx);
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_block_hints(function, &repeat_stmt.body, hints, loop_ctx);
            collect_expr_hints(function, &repeat_stmt.cond, hints);
        }
        AstStmt::NumericFor(numeric_for) => {
            let candidate = numeric_loop_name(loop_ctx.numeric_depth).to_owned();
            register_binding_hint(
                function,
                numeric_for.binding,
                candidate,
                NameSource::LoopRole,
                hints,
            );
            collect_expr_hints(function, &numeric_for.start, hints);
            collect_expr_hints(function, &numeric_for.limit, hints);
            collect_expr_hints(function, &numeric_for.step, hints);
            collect_block_hints(
                function,
                &numeric_for.body,
                hints,
                LoopContext {
                    numeric_depth: loop_ctx.numeric_depth + 1,
                },
            );
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_expr_hints(function, expr, hints);
            }
            for (index, binding) in generic_for.bindings.iter().copied().enumerate() {
                let candidate = match index {
                    0 if generic_for.bindings.len() == 1 => "item",
                    0 => "k",
                    1 => "v",
                    _ => "extra",
                };
                register_binding_hint(
                    function,
                    binding,
                    candidate.to_owned(),
                    NameSource::LoopRole,
                    hints,
                );
            }
            collect_block_hints(function, &generic_for.body, hints, loop_ctx);
        }
        AstStmt::DoBlock(block) => collect_block_hints(function, block, hints, loop_ctx),
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
            collect_function_expr_hints(&function_decl.func, hints);
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            register_binding_hint(
                function,
                local_function_decl.name,
                "fn".to_owned(),
                NameSource::FunctionShape,
                hints,
            );
            collect_function_expr_hints(&local_function_decl.func, hints);
        }
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => {}
    }
}

fn collect_function_expr_hints(function: &AstFunctionExpr, hints: &mut [FunctionHints]) {
    collect_block_hints(
        function.function,
        &function.body,
        hints,
        LoopContext::default(),
    )
}

fn collect_call_hints(function: HirProtoRef, call: &AstCallKind, hints: &mut [FunctionHints]) {
    traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        collect_expr_hints(function, expr, hints);
    });
}

fn collect_lvalue_hints(function: HirProtoRef, target: &AstLValue, hints: &mut [FunctionHints]) {
    if let AstLValue::Name(AstNameRef::SyntheticLocal(local)) = target {
        record_synthetic_local(function, *local, hints);
    }
    traverse_lvalue_children!(target, borrow = [&], expr(expr) => {
        collect_expr_hints(function, expr, hints);
    });
}

fn collect_expr_hints(function: HirProtoRef, expr: &AstExpr, hints: &mut [FunctionHints]) {
    for node in expr_nodes(expr) {
        match node {
            ExprNode::Expr(AstExpr::TableConstructor(table)) => {
                for field in &table.fields {
                    if let crate::ast::AstTableField::Record(record) = field {
                        let name = match &record.key {
                            crate::ast::AstTableKey::Name(name) => Some(name.as_str()),
                            crate::ast::AstTableKey::Expr(AstExpr::String(name)) => name.as_utf8(),
                            _ => None,
                        };
                        register_usage_hint(function, &record.value, name, hints);
                    }
                }
            }
            ExprNode::Expr(AstExpr::Var(AstNameRef::SyntheticLocal(local))) => {
                record_synthetic_local(function, *local, hints);
            }
            ExprNode::Function(func) => collect_function_expr_hints(func, hints),
            _ => {}
        }
    }
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
    register_binding_hint(function, binding, candidate, source, hints);
}

fn register_usage_hint(
    function: HirProtoRef,
    value: &AstExpr,
    field: Option<&str>,
    hints: &mut [FunctionHints],
) {
    let Some(name) = field.and_then(normalize_identifier) else {
        return;
    };
    let AstExpr::Var(source) = value else {
        return;
    };
    if let AstNameRef::Param(param) = source {
        register_param_hint(function, *param, &name, NameSource::Usage, hints);
    } else if let Some(binding) = final_binding_from_name_ref(source) {
        register_binding_hint(function, binding, name, NameSource::Usage, hints);
    }
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

// 候选由表达式规范化或固定角色名产生，注册只消费其所有权，不再清洗同一文本。
fn register_binding_hint(
    function: HirProtoRef,
    binding: AstBindingRef,
    candidate: String,
    source: NameSource,
    hints: &mut [FunctionHints],
) {
    if !hints[function.index()].heuristic
        && !matches!(source, NameSource::LoopRole | NameSource::FunctionShape)
    {
        return;
    }
    match binding {
        AstBindingRef::Local(local) => {
            insert_hint(
                &mut hints[function.index()].local_hints,
                local,
                candidate,
                source,
            );
        }
        AstBindingRef::SyntheticLocal(local) => {
            let function_hints = &mut hints[function.index()];
            function_hints.synthetic_locals.insert(local);
            insert_hint(
                &mut function_hints.synthetic_local_hints,
                local,
                candidate,
                source,
            );
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
    if !hints[function.index()].heuristic && source != NameSource::SelfParam {
        return;
    }
    let Some(candidate) = normalize_identifier(candidate) else {
        return;
    };
    let function_hints = &mut hints[function.index()];
    insert_hint(&mut function_hints.param_hints, param, candidate, source);
}

fn record_synthetic_local(
    function: HirProtoRef,
    local: AstSyntheticLocalId,
    hints: &mut [FunctionHints],
) {
    hints[function.index()].synthetic_locals.insert(local);
}

fn insert_hint<K>(map: &mut BTreeMap<K, HintChoice>, key: K, candidate: String, source: NameSource)
where
    K: Ord,
{
    if let Some(existing) = map.get(&key) {
        match hint_priority(source).cmp(&hint_priority(existing.source())) {
            std::cmp::Ordering::Less => return,
            std::cmp::Ordering::Equal => {
                // 两个同等可信的用途不应由出现顺序定胜负；后续重复提示也不能解除歧义。
                if existing
                    .candidate()
                    .is_some_and(|hint| hint.text != candidate)
                {
                    map.insert(key, HintChoice::Ambiguous(source));
                }
                return;
            }
            std::cmp::Ordering::Greater => {}
        }
    }
    map.insert(
        key,
        HintChoice::Unique(CandidateHint {
            text: candidate,
            source,
        }),
    );
}

fn hint_priority(source: NameSource) -> usize {
    match source {
        NameSource::LegacyArg => 110,
        NameSource::LexicalEnvironment => 110,
        NameSource::Debug => 100,
        NameSource::CaptureProvenance => 95,
        NameSource::SelfParam => 90,
        NameSource::LoopRole => 80,
        NameSource::ModulePath => 78,
        NameSource::Usage => 75,
        NameSource::FieldName => 70,
        NameSource::LibrarySignature => 68,
        NameSource::CallResult => 65,
        NameSource::TableShape | NameSource::BoolShape | NameSource::FunctionShape => 60,
        NameSource::NumberShape | NameSource::StringShape => 60,
        NameSource::ResultShape => 50,
        NameSource::Discard => 20,
        NameSource::DebugLike | NameSource::Simple | NameSource::ConflictFallback => 10,
    }
}

fn final_binding_from_name_ref(name: &AstNameRef) -> Option<AstBindingRef> {
    let binding = AstBindingRef::from_name_ref(name);
    if matches!(binding, Some(AstBindingRef::Temp(_))) {
        unreachable!("readability output must not leak raw temp refs into naming");
    }
    binding
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
