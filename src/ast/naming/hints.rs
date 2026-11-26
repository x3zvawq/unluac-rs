//! 从最终 AST 收集命名提示，区分基础语法角色与 heuristic 的形状、调用和用途线索。
//! 同级冲突保留歧义，不让遍历顺序决定名称；提示不参与语义改写或 binding 身份恢复。

use std::collections::BTreeMap;

use crate::ast::traverse::{traverse_call_children, traverse_lvalue_children};
use crate::ast::visit::{ExprNode, expr_nodes};
use crate::ast::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue,
    AstModule, AstNameRef, AstStmt, AstSyntheticLocalId, ParamId, ProtoId,
};

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
    function: ProtoId,
    block: &AstBlock,
    hints: &mut [FunctionHints],
    loop_ctx: LoopContext,
) {
    for stmt in &block.stmts {
        collect_stmt_hints(function, stmt, hints, loop_ctx);
    }
}

fn collect_stmt_hints(
    function: ProtoId,
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
                    if let Some(pcall_hint) = pcall_result_hint(value, index) {
                        register_binding_hint(
                            function,
                            binding.id,
                            pcall_hint.to_owned(),
                            NameSource::LibrarySignature,
                            hints,
                        );
                    } else {
                        register_binding_expr_hint(function, binding.id, value, hints);
                    }
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
                        if let Some(pcall_hint) = pcall_result_hint(value, index) {
                            register_binding_hint(
                                function,
                                binding,
                                pcall_hint.to_owned(),
                                NameSource::LibrarySignature,
                                hints,
                            );
                        } else {
                            register_binding_expr_hint(function, binding, value, hints);
                        }
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
            } else if hints[function_decl.func.function.index()].heuristic
                && !function_decl.global_declaration
                && let AstFunctionName::Plain(path) = &function_decl.target
                && !path.fields.is_empty()
                && !(path.fields.len() == 1 && matches!(path.root, AstNameRef::Environment))
                && let Some(first_param) = function_decl.func.params.first().copied()
                && param_used_as_table_receiver(&function_decl.func.body, first_param)
            {
                register_param_hint(
                    function_decl.func.function,
                    first_param,
                    "self",
                    NameSource::HeuristicSelfParam,
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

fn collect_call_hints(function: ProtoId, call: &AstCallKind, hints: &mut [FunctionHints]) {
    traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        collect_expr_hints(function, expr, hints);
    });
}

fn collect_lvalue_hints(function: ProtoId, target: &AstLValue, hints: &mut [FunctionHints]) {
    if let AstLValue::Name(AstNameRef::SyntheticLocal(local)) = target {
        record_synthetic_local(function, *local, hints);
    }
    traverse_lvalue_children!(target, borrow = [&], expr(expr) => {
        collect_expr_hints(function, expr, hints);
    });
}

fn collect_expr_hints(function: ProtoId, expr: &AstExpr, hints: &mut [FunctionHints]) {
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
    function: ProtoId,
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

fn pcall_result_hint(expr: &AstExpr, slot_index: usize) -> Option<&'static str> {
    let AstExpr::Call(call) = expr else {
        return None;
    };
    let AstExpr::Var(AstNameRef::Global(g)) = &call.callee else {
        return None;
    };
    if !matches!(g.text.as_str(), "pcall" | "xpcall") {
        return None;
    }
    match slot_index {
        0 => Some("ok"),
        1 => Some("result"),
        _ => None,
    }
}

fn register_usage_hint(
    function: ProtoId,
    value: &AstExpr,
    field: Option<&str>,
    hints: &mut [FunctionHints],
) {
    let Some(name) = field.and_then(normalize_identifier) else {
        return;
    };
    // 元方法键名（`__index`/`__newindex`/`__tostring` 等）不适合当作参数或局部变量名。
    if name.starts_with("__") {
        return;
    }
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
    function: ProtoId,
    binding: AstBindingRef,
    hints: &mut [FunctionHints],
) {
    if let AstBindingRef::SyntheticLocal(local) = binding {
        record_synthetic_local(function, local, hints);
    }
}

// 候选由表达式规范化或固定角色名产生，注册只消费其所有权，不再清洗同一文本。
fn register_binding_hint(
    function: ProtoId,
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
    }
}

fn register_param_hint(
    function: ProtoId,
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
    function: ProtoId,
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
        NameSource::HeuristicSelfParam => 85,
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
    AstBindingRef::from_name_ref(name)
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

/// 启发式判断表方法定义 `function tbl.foo(p0, ...)` 的首参 `p0` 是否在函数体内作为对象接收者使用
/// （字段访问 `p0.x`、索引访问 `p0[k]`、方法调用 `p0:bar()`），且不被当作普通数值/字符串/裸函数调用。
fn param_used_as_table_receiver(body: &AstBlock, param: ParamId) -> bool {
    let mut receiver_uses = 0usize;
    let mut non_receiver = false;
    scan_block_for_receiver(body, param, &mut receiver_uses, &mut non_receiver);
    receiver_uses > 0 && !non_receiver
}

fn is_param_var(expr: &AstExpr, param: ParamId) -> bool {
    matches!(expr, AstExpr::Var(AstNameRef::Param(p)) if *p == param)
}

fn scan_block_for_receiver(
    block: &AstBlock,
    param: ParamId,
    receiver_uses: &mut usize,
    non_receiver: &mut bool,
) {
    for stmt in &block.stmts {
        if *non_receiver {
            return;
        }
        match stmt {
            AstStmt::LocalDecl(d) => {
                for v in &d.values {
                    scan_expr_for_receiver(v, param, receiver_uses, non_receiver);
                }
            }
            AstStmt::GlobalDecl(d) => {
                for v in &d.values {
                    scan_expr_for_receiver(v, param, receiver_uses, non_receiver);
                }
            }
            AstStmt::Assign(a) => {
                for t in &a.targets {
                    scan_lvalue_for_receiver(t, param, receiver_uses, non_receiver);
                }
                for v in &a.values {
                    scan_expr_for_receiver(v, param, receiver_uses, non_receiver);
                }
            }
            AstStmt::CallStmt(c) => scan_call_for_receiver(&c.call, param, receiver_uses, non_receiver),
            AstStmt::Return(r) => {
                for v in &r.values {
                    scan_expr_for_receiver(v, param, receiver_uses, non_receiver);
                }
            }
            AstStmt::If(i) => {
                scan_expr_for_receiver(&i.cond, param, receiver_uses, non_receiver);
                scan_block_for_receiver(&i.then_block, param, receiver_uses, non_receiver);
                if let Some(eb) = &i.else_block {
                    scan_block_for_receiver(eb, param, receiver_uses, non_receiver);
                }
            }
            AstStmt::While(w) => {
                scan_expr_for_receiver(&w.cond, param, receiver_uses, non_receiver);
                scan_block_for_receiver(&w.body, param, receiver_uses, non_receiver);
            }
            AstStmt::Repeat(r) => {
                scan_block_for_receiver(&r.body, param, receiver_uses, non_receiver);
                scan_expr_for_receiver(&r.cond, param, receiver_uses, non_receiver);
            }
            AstStmt::NumericFor(nf) => {
                scan_expr_for_receiver(&nf.start, param, receiver_uses, non_receiver);
                scan_expr_for_receiver(&nf.limit, param, receiver_uses, non_receiver);
                scan_expr_for_receiver(&nf.step, param, receiver_uses, non_receiver);
                scan_block_for_receiver(&nf.body, param, receiver_uses, non_receiver);
            }
            AstStmt::GenericFor(gf) => {
                for e in &gf.iterator {
                    scan_expr_for_receiver(e, param, receiver_uses, non_receiver);
                }
                scan_block_for_receiver(&gf.body, param, receiver_uses, non_receiver);
            }
            AstStmt::DoBlock(b) => scan_block_for_receiver(b, param, receiver_uses, non_receiver),
            AstStmt::FunctionDecl(_)
            | AstStmt::LocalFunctionDecl(_)
            | AstStmt::Break
            | AstStmt::Continue
            | AstStmt::Goto(_)
            | AstStmt::Label(_)
            | AstStmt::Error(_) => {}
        }
    }
}

fn scan_lvalue_for_receiver(
    lv: &AstLValue,
    param: ParamId,
    receiver_uses: &mut usize,
    non_receiver: &mut bool,
) {
    match lv {
        AstLValue::Name(_) => {}
        AstLValue::FieldAccess(f) => {
            if is_param_var(&f.base, param) {
                *receiver_uses += 1;
            } else {
                scan_expr_for_receiver(&f.base, param, receiver_uses, non_receiver);
            }
        }
        AstLValue::IndexAccess(ia) => {
            if is_param_var(&ia.base, param) {
                *receiver_uses += 1;
            } else {
                scan_expr_for_receiver(&ia.base, param, receiver_uses, non_receiver);
            }
            scan_expr_for_receiver(&ia.index, param, receiver_uses, non_receiver);
        }
    }
}

fn scan_call_for_receiver(
    call: &AstCallKind,
    param: ParamId,
    receiver_uses: &mut usize,
    non_receiver: &mut bool,
) {
    match call {
        AstCallKind::Call(c) => {
            if is_param_var(&c.callee, param) {
                *non_receiver = true;
                return;
            }
            scan_expr_for_receiver(&c.callee, param, receiver_uses, non_receiver);
            for a in &c.args {
                scan_expr_for_receiver(a, param, receiver_uses, non_receiver);
            }
        }
        AstCallKind::MethodCall(mc) => {
            if is_param_var(&mc.receiver, param) {
                *receiver_uses += 1;
            } else {
                scan_expr_for_receiver(&mc.receiver, param, receiver_uses, non_receiver);
            }
            for a in &mc.args {
                scan_expr_for_receiver(a, param, receiver_uses, non_receiver);
            }
        }
    }
}

fn scan_expr_for_receiver(
    expr: &AstExpr,
    param: ParamId,
    receiver_uses: &mut usize,
    non_receiver: &mut bool,
) {
    if *non_receiver {
        return;
    }
    match expr {
        AstExpr::FieldAccess(f) => {
            if is_param_var(&f.base, param) {
                *receiver_uses += 1;
            } else {
                scan_expr_for_receiver(&f.base, param, receiver_uses, non_receiver);
            }
        }
        AstExpr::IndexAccess(ia) => {
            if is_param_var(&ia.base, param) {
                *receiver_uses += 1;
            } else {
                scan_expr_for_receiver(&ia.base, param, receiver_uses, non_receiver);
            }
            scan_expr_for_receiver(&ia.index, param, receiver_uses, non_receiver);
        }
        AstExpr::Call(c) => {
            if is_param_var(&c.callee, param) {
                *non_receiver = true;
                return;
            }
            scan_expr_for_receiver(&c.callee, param, receiver_uses, non_receiver);
            for a in &c.args {
                scan_expr_for_receiver(a, param, receiver_uses, non_receiver);
            }
        }
        AstExpr::MethodCall(mc) => {
            if is_param_var(&mc.receiver, param) {
                *receiver_uses += 1;
            } else {
                scan_expr_for_receiver(&mc.receiver, param, receiver_uses, non_receiver);
            }
            for a in &mc.args {
                scan_expr_for_receiver(a, param, receiver_uses, non_receiver);
            }
        }
        AstExpr::Unary(u) => {
            if u.op != crate::ast::AstUnaryOpKind::Not && is_param_var(&u.expr, param) {
                *non_receiver = true;
                return;
            }
            scan_expr_for_receiver(&u.expr, param, receiver_uses, non_receiver);
        }
        AstExpr::Binary(b) => {
            if b.op != crate::ast::AstBinaryOpKind::Eq
                && (is_param_var(&b.lhs, param) || is_param_var(&b.rhs, param))
            {
                *non_receiver = true;
                return;
            }
            scan_expr_for_receiver(&b.lhs, param, receiver_uses, non_receiver);
            scan_expr_for_receiver(&b.rhs, param, receiver_uses, non_receiver);
        }
        AstExpr::LogicalAnd(l) | AstExpr::LogicalOr(l) => {
            scan_expr_for_receiver(&l.lhs, param, receiver_uses, non_receiver);
            scan_expr_for_receiver(&l.rhs, param, receiver_uses, non_receiver);
        }
        AstExpr::SingleValue(inner) => {
            scan_expr_for_receiver(inner, param, receiver_uses, non_receiver);
        }
        AstExpr::TableConstructor(t) => {
            for field in &t.fields {
                match field {
                    crate::ast::AstTableField::Array(e) => {
                        scan_expr_for_receiver(e, param, receiver_uses, non_receiver);
                    }
                    crate::ast::AstTableField::Record(r) => {
                        if let crate::ast::AstTableKey::Expr(k) = &r.key {
                            scan_expr_for_receiver(k, param, receiver_uses, non_receiver);
                        }
                        scan_expr_for_receiver(&r.value, param, receiver_uses, non_receiver);
                    }
                }
            }
        }
        AstExpr::IfExpr(ie) => {
            scan_expr_for_receiver(&ie.cond, param, receiver_uses, non_receiver);
            scan_expr_for_receiver(&ie.then_expr, param, receiver_uses, non_receiver);
            scan_expr_for_receiver(&ie.else_expr, param, receiver_uses, non_receiver);
        }
        AstExpr::FunctionExpr(_)
        | AstExpr::Var(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Vector(_)
        | AstExpr::VarArg
        | AstExpr::Error(_) => {}
    }
}
