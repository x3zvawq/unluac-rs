//! 这个子模块负责把“构造器尾部立刻安装方法/字段函数”的模式收成更自然的函数 sugar。
//!
//! 它依赖前缀 local alias 证据和已经合法化的 AST，只吸收终端构造器链上的局部模式，
//! 不会在这里重写一般赋值语句。
//! 例如：
//! - `local t = {}; t.pick = function(...) end; return t`
//!   -> `local t = { pick = function(...) end }; return t`
//! - `local meta = {}; local methods = {}; function methods.bump(...) end; meta.__index = methods;
//!    local ctor = ffi.metatype("x", meta)`
//!   -> `local ctor = ffi.metatype("x", { __index = { bump = function(...) end } })`
//!
//! 这里不会去猜任意跨语句的数据流；只有“构造器 local -> 构造器字段接线”仍保持机械
//! 脚手架形状时，才会收回源码结构。非 plain 字段函数的语句自然终止连续前缀，不由本
//! pass 改写。

use std::collections::BTreeSet;

use super::super::binding_flow::{BindingUseIndex, binding_mentions_in_stmt};
use super::super::binding_ref::{binding_from_name_ref, name_matches_binding};
use super::super::expr_analysis::is_eventless_primitive_literal;
use super::super::installer_iife::function_expr_is_substantial;
use crate::ast::common::{
    AstAssign, AstBindingRef, AstCallKind, AstExpr, AstFieldAccess, AstFunctionExpr, AstFunctionName,
    AstLValue, AstLocalAttr, AstLocalDecl, AstLocalOrigin, AstReturn, AstStmt, AstTableField,
    AstTableKey,
};

pub(super) fn try_inline_terminal_constructor_fields(
    stmts: &[AstStmt],
) -> Option<(AstStmt, usize)> {
    let AstStmt::LocalDecl(local_decl) = stmts.first()? else {
        return None;
    };
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    if local_decl.bindings[0].attr != AstLocalAttr::None {
        // 候选拒绝[PolicyBoundary]：`<const>`/`<close>` 声明属性仍由声明 owner 保留；本
        // pass 不改变属性归属或资源生命周期。
        return None;
    }
    let binding = local_decl.bindings[0].id;
    let AstExpr::TableConstructor(_) = &local_decl.values[0] else {
        return None;
    };

    let mut rewritten = local_decl.as_ref().clone();
    let AstExpr::TableConstructor(table) = &mut rewritten.values[0] else {
        unreachable!("matched constructor value above")
    };
    if !table_can_append_record_field(table) {
        return None;
    }

    let mut consumed = 1usize;
    let mut inlined_any = false;
    while let Some(stmt) = stmts.get(consumed) {
        let Some((field, func)) = inlineable_local_table_function_stmt(stmt, binding) else {
            break;
        };
        table
            .fields
            .push(AstTableField::Record(crate::ast::AstRecordField {
                key: AstTableKey::Name(field),
                value: AstExpr::FunctionExpr(Box::new(func)),
            }));
        consumed += 1;
        inlined_any = true;
    }
    if !inlined_any {
        return None;
    }

    Some((AstStmt::LocalDecl(Box::new(rewritten)), consumed))
}

pub(super) fn try_inline_terminal_constructor_call(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
) -> Option<(AstStmt, usize)> {
    let (callee_binding, callee_expr) = single_local_alias_decl(stmts.first()?)?;
    // This rule exists to remove constructor scaffolding, not to turn a readable named function
    // back into a multiline result-position IIFE. Short callees still benefit from the compact
    // terminal form.
    if let AstExpr::FunctionExpr(function) = callee_expr
        && function_expr_is_substantial(function)
    {
        // 候选拒绝[PolicyBoundary]：多语句/控制流 closure 内联到结果位置会制造难读 IIFE，语义上并非禁止。
        return None;
    }
    let mut consumed = 1usize;
    let mut arg_locals = Vec::<ConstructorArg>::new();

    while let Some(stmt) = stmts.get(consumed) {
        let Some((binding, value)) = single_local_alias_decl(stmt) else {
            break;
        };
        arg_locals.push(ConstructorArg {
            binding,
            value: value.clone(),
            pass_to_sink: true,
        });
        consumed += 1;
    }
    if arg_locals.is_empty() {
        return None;
    }

    while let Some(stmt) = stmts.get(consumed) {
        if inline_arg_local_table_function(stmt, &mut arg_locals) {
            consumed += 1;
            continue;
        }
        if inline_nested_arg_local_table(stmt, &mut arg_locals) {
            consumed += 1;
            continue;
        }
        break;
    }

    let sink = stmts.get(consumed)?;
    if use_index.count_uses_in_range(
        stmt_base + consumed,
        stmt_base + consumed + 1,
        callee_binding,
    ) != 1
        || arg_locals.iter().any(|arg| {
            use_index.count_uses_in_range(
                stmt_base + consumed,
                stmt_base + consumed + 1,
                arg.binding,
            ) != usize::from(arg.pass_to_sink)
        })
    {
        // 候选拒绝[SemanticBarrier:Scope]：sink 内除目标 call 外再读 callee/arg 时，删除声明会留下未绑定 use；每个 active handoff 必须恰好出现一次，已嵌套消费的 arg 必须为零次。
        return None;
    }
    let rewritten_sink =
        rewrite_terminal_constructor_call_sink(sink, callee_binding, callee_expr, &arg_locals)?;
    let removed_bindings = std::iter::once(callee_binding)
        .chain(arg_locals.iter().map(|arg| arg.binding))
        .collect::<BTreeSet<_>>();
    if !binding_mentions_in_stmt(&rewritten_sink).is_disjoint(&removed_bindings) {
        // 候选拒绝[SemanticBarrier:Capture]：折叠后 sink 若仍直接或经字段闭包引用任一被删 binding，消除声明会留下悬空引用；regress_362 是闭包捕获 arg 的具体反例。
        return None;
    }
    if !matches!(sink, AstStmt::Return(_))
        && !removed_constructor_locals_are_dead_after_sink(
            use_index,
            stmt_base + consumed + 1,
            callee_binding,
            &arg_locals,
        )
    {
        // 候选拒绝[SemanticBarrier:Scope]：非终端 sink 后若仍引用被消除的 callee/arg local，内联会留下未绑定 use。
        return None;
    }
    Some((rewritten_sink, consumed + 1))
}

#[derive(Clone)]
struct ConstructorArg {
    binding: AstBindingRef,
    value: AstExpr,
    pass_to_sink: bool,
}

fn single_local_alias_decl(stmt: &AstStmt) -> Option<(AstBindingRef, &AstExpr)> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    match local_decl.bindings[0].attr {
        AstLocalAttr::None => {}
        AstLocalAttr::Close => {
            // 候选拒绝[SemanticBarrier:Lifetime]：删除 `<close>` alias 会同时删除其
            // 离域 close 动作与资源 owner。
            return None;
        }
        AstLocalAttr::Const => {
            // 候选拒绝[PolicyBoundary]：`<const>` 的源码声明身份继续由声明 owner 保留。
            return None;
        }
    }
    if local_decl.bindings[0].origin != AstLocalOrigin::Recovered {
        // 候选拒绝[PolicyBoundary]：DebugHinted 的源码声明身份保留；候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot 必须活到原 block 末。
        return None;
    }
    Some((local_decl.bindings[0].id, &local_decl.values[0]))
}

fn inlineable_local_table_function_stmt(
    stmt: &AstStmt,
    binding: AstBindingRef,
) -> Option<(String, AstFunctionExpr)> {
    match stmt {
        AstStmt::Assign(assign) => inlineable_local_table_function_assign(assign, binding),
        AstStmt::FunctionDecl(function_decl) => {
            let AstFunctionName::Plain(path) = &function_decl.target else {
                return None;
            };
            if path.fields.len() != 1 || !name_matches_binding(&path.root, binding) {
                return None;
            }
            // 同 assign 分支：闭包捕获了 constructor binding 时不能折入
            if function_decl.func.captured_bindings.contains(&binding) {
                // 候选拒绝[SemanticBarrier:Capture]：`function obj.f() return obj end` 折进字面量并消除 `obj` 后，闭包捕获会悬空或改绑。
                return None;
            }
            Some((path.fields[0].clone(), function_decl.func.clone()))
        }
        _ => None,
    }
}

fn inlineable_local_table_function_assign(
    assign: &AstAssign,
    binding: AstBindingRef,
) -> Option<(String, AstFunctionExpr)> {
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return None;
    }
    let AstLValue::FieldAccess(access) = &assign.targets[0] else {
        return None;
    };
    let AstFieldAccess { base, field } = access.as_ref();
    let AstExpr::Var(name) = base else {
        return None;
    };
    if !name_matches_binding(name, binding) {
        return None;
    }
    let AstExpr::FunctionExpr(function) = &assign.values[0] else {
        return None;
    };
    // 如果闭包体捕获了 constructor binding 自身（如 `obj.inc = function() obj.count = ... end`），
    // 折入 constructor 后 binding 可能因 return-handoff 被消除，导致闭包中引用悬空。
    if function.captured_bindings.contains(&binding) {
        // 候选拒绝[SemanticBarrier:Capture]：`obj.f=function() return obj end` 需要 constructor binding 作为 upvalue，不能在 return handoff 中删除。
        return None;
    }
    Some((field.clone(), function.as_ref().clone()))
}

fn inline_arg_local_table_function(stmt: &AstStmt, arg_locals: &mut [ConstructorArg]) -> bool {
    for arg_local in arg_locals {
        let Some((field, func)) = inlineable_local_table_function_stmt(stmt, arg_local.binding)
        else {
            continue;
        };
        let AstExpr::TableConstructor(table) = &mut arg_local.value else {
            continue;
        };
        if !table_can_append_record_field(table) {
            return false;
        }
        table
            .fields
            .push(AstTableField::Record(crate::ast::common::AstRecordField {
                key: AstTableKey::Name(field),
                value: AstExpr::FunctionExpr(Box::new(func)),
            }));
        return true;
    }
    false
}

fn inline_nested_arg_local_table(stmt: &AstStmt, arg_locals: &mut [ConstructorArg]) -> bool {
    let Some((outer_binding, field, inner_binding)) = inlineable_nested_table_assign(stmt) else {
        return false;
    };
    let Some(inner_index) = arg_locals
        .iter()
        .position(|arg| arg.binding == inner_binding)
    else {
        return false;
    };
    let Some(outer_index) = arg_locals
        .iter()
        .position(|arg| arg.binding == outer_binding)
    else {
        return false;
    };
    if inner_index == outer_index || !arg_locals[inner_index].pass_to_sink {
        // 候选拒绝[SemanticBarrier:Identity]：不能把 table 接到自身，且已被某次嵌套接线消费的 inner 不能再复制到第二个字段。
        return false;
    }
    if outer_index + 1 != inner_index {
        // 候选拒绝[SemanticBarrier:EvalOrder]：只有 `outer` 紧邻先于 `inner` 时，折入字段仍按 outer、inner 的原顺序构造；反向或跨 initializer 会重排事件。
        return false;
    }

    let inner_value = arg_locals[inner_index].value.clone();
    let AstExpr::TableConstructor(_) = inner_value else {
        return false;
    };
    let AstExpr::TableConstructor(table) = &mut arg_locals[outer_index].value else {
        return false;
    };
    if !table_can_append_record_field(table) {
        return false;
    }

    // 这里专门收回“先建内层 methods table，再接到外层 metadata 字段”的机械接线。
    // 它只在内层 table 仍是独立 constructor local 时触发，不会把任意普通变量赋值猜成
    // 嵌套表字面量。
    table
        .fields
        .push(AstTableField::Record(crate::ast::AstRecordField {
            key: AstTableKey::Name(field),
            value: inner_value,
        }));
    arg_locals[inner_index].pass_to_sink = false;
    true
}

fn table_can_append_record_field(table: &crate::ast::common::AstTableConstructor) -> bool {
    // 候选拒绝[SemanticBarrier:ValueArity]：追加字段会让原末尾 open call/vararg 不再展开，具体反例见 regress_401。
    !matches!(
        table.fields.last(),
        Some(AstTableField::Array(
            AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg
        ))
    )
}

fn inlineable_nested_table_assign(
    stmt: &AstStmt,
) -> Option<(AstBindingRef, String, AstBindingRef)> {
    let AstStmt::Assign(assign) = stmt else {
        return None;
    };
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return None;
    }
    let AstLValue::FieldAccess(access) = &assign.targets[0] else {
        return None;
    };
    let AstExpr::Var(outer_name) = &access.base else {
        return None;
    };
    let AstExpr::Var(inner_name) = &assign.values[0] else {
        return None;
    };
    Some((
        binding_from_name_ref(outer_name)?,
        access.field.clone(),
        binding_from_name_ref(inner_name)?,
    ))
}

fn rewrite_terminal_constructor_call_sink(
    stmt: &AstStmt,
    callee_binding: AstBindingRef,
    callee_expr: &AstExpr,
    arg_locals: &[ConstructorArg],
) -> Option<AstStmt> {
    match stmt {
        AstStmt::Return(ret) => {
            let mut rewritten: AstReturn = ret.as_ref().clone();
            rewritten.values[0] = rewrite_terminal_constructor_call_expr(
                ret.values.first()?,
                callee_binding,
                callee_expr,
                arg_locals,
            )?;
            Some(AstStmt::Return(Box::new(rewritten)))
        }
        AstStmt::LocalDecl(local_decl) => {
            let mut rewritten: AstLocalDecl = local_decl.as_ref().clone();
            rewritten.values[0] = rewrite_terminal_constructor_call_expr(
                local_decl.values.first()?,
                callee_binding,
                callee_expr,
                arg_locals,
            )?;
            Some(AstStmt::LocalDecl(Box::new(rewritten)))
        }
        AstStmt::CallStmt(call_stmt) => {
            let AstCallKind::Call(call) = &call_stmt.call else {
                return None;
            };
            let AstExpr::Call(call) = rewrite_terminal_constructor_call_expr(
                &AstExpr::Call(call.clone()),
                callee_binding,
                callee_expr,
                arg_locals,
            )?
            else {
                unreachable!("terminal constructor helper preserves the outer call")
            };
            let mut rewritten = call_stmt.as_ref().clone();
            rewritten.call = AstCallKind::Call(call);
            // 候选接受[EvalOrderProof]：CallStmt 没有外层求值前缀，constructor initializer 仍在 callee/实参位置按原顺序执行一次。
            Some(AstStmt::CallStmt(Box::new(rewritten)))
        }
        AstStmt::If(if_stmt) => {
            let mut rewritten = if_stmt.as_ref().clone();
            rewritten.cond = rewrite_terminal_constructor_call_expr(
                &if_stmt.cond,
                callee_binding,
                callee_expr,
                arg_locals,
            )?;
            // 候选接受[EvalOrderProof/ValueArityProof]：if 条件是一次性标量 owner，且没有先行运行时事件。
            Some(AstStmt::If(Box::new(rewritten)))
        }
        AstStmt::NumericFor(numeric_for) => {
            let mut rewritten = numeric_for.as_ref().clone();
            rewritten.start = rewrite_terminal_constructor_call_expr(
                &numeric_for.start,
                callee_binding,
                callee_expr,
                arg_locals,
            )?;
            // 候选接受[EvalOrderProof/ValueArityProof]：start 是 header 首个一次性标量事件，limit/step 顺序不动。
            Some(AstStmt::NumericFor(Box::new(rewritten)))
        }
        AstStmt::GenericFor(generic_for) => {
            let mut rewritten = generic_for.as_ref().clone();
            let first = rewrite_terminal_constructor_call_expr(
                generic_for.iterator.first()?,
                callee_binding,
                callee_expr,
                arg_locals,
            )?;
            rewritten.iterator[0] = first;
            // 候选接受[EvalOrderProof/ValueArityProof]：首 iterator 无前缀；单项时保留 open pack，多项时前后都截成单值。
            Some(AstStmt::GenericFor(Box::new(rewritten)))
        }
        AstStmt::While(_) | AstStmt::Repeat(_) => {
            // 候选拒绝[SemanticBarrier:EvalCount]：搬入循环条件会把一次 constructor/callee 初始化改成逐轮执行。
            None
        }
        _ => None,
    }
}

fn rewrite_terminal_constructor_call_expr(
    expr: &AstExpr,
    callee_binding: AstBindingRef,
    callee_expr: &AstExpr,
    arg_locals: &[ConstructorArg],
) -> Option<AstExpr> {
    let AstExpr::Call(call) = expr else {
        return None;
    };
    let AstExpr::Var(name) = &call.callee else {
        return None;
    };
    let active_args = arg_locals
        .iter()
        .filter(|arg| arg.pass_to_sink)
        .collect::<Vec<_>>();
    if !name_matches_binding(name, callee_binding) {
        // 候选拒绝[SemanticBarrier:Identity]：sink 必须调用被删除 alias 所指向的同一 callee。
        return None;
    }

    let mut expected_args = active_args.iter().copied().peekable();
    let mut rewritten_args = Vec::with_capacity(call.args.len());
    for arg in &call.args {
        if let Some(expected) = expected_args.peek()
            && matches!(arg, AstExpr::Var(name) if name_matches_binding(name, expected.binding))
        {
            rewritten_args.push(expected.value.clone());
            expected_args.next();
            continue;
        }
        if !is_eventless_primitive_literal(arg) {
            // 候选拒绝[ProofIncomplete]：额外实参若含 binding、lookup、调用或分配，
            // 仍需证明把 constructor initializer 搬到其后不会改变快照与求值顺序。
            return None;
        }
        // 候选接受[EvalOrderProof]：primitive literal 没有读取、分配或运行时事件，
        // 保留在原参数位置不会与被搬入的 constructor initializer 交换可观察行为。
        rewritten_args.push(arg.clone());
    }
    if expected_args.next().is_some() {
        // 候选拒绝[SemanticBarrier:Scope/EvalOrder]：每个 active constructor local 都必须
        // 按声明顺序由 sink 承接一次，否则删除声明会丢失 handoff 或改变 initializer 顺序。
        return None;
    }

    let mut rewritten = call.as_ref().clone();
    rewritten.callee = callee_expr.clone();
    rewritten.args = rewritten_args;
    if let Some(last) = rewritten.args.last_mut()
        && matches!(
            last,
            AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg
        )
    {
        // 候选接受[ValueArityProof]：constructor local 的 initializer 原本被单目标声明
        // 截成一个值；移到最终实参位置后必须显式保留该边界，不能恢复 open tail。
        let value = std::mem::replace(last, AstExpr::Nil);
        *last = AstExpr::SingleValue(Box::new(value));
    }
    Some(AstExpr::Call(Box::new(rewritten)))
}

fn removed_constructor_locals_are_dead_after_sink(
    use_index: &BindingUseIndex,
    suffix_start: usize,
    callee_binding: AstBindingRef,
    arg_locals: &[ConstructorArg],
) -> bool {
    if use_index.count_uses_in_suffix(suffix_start, callee_binding) != 0 {
        // 候选拒绝[SemanticBarrier:Scope]：callee local 在 sink 后仍有 use，不能随 constructor 壳一起删除。
        return false;
    }
    // 候选拒绝[SemanticBarrier:Scope]：任一 constructor arg local 在 sink 后仍有 use，都不能从词法作用域删除。
    arg_locals
        .iter()
        .all(|arg| use_index.count_uses_in_suffix(suffix_start, arg.binding) == 0)
}
