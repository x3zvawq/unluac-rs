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
//! 这里不会去猜任意跨语句的数据流；只有“构造器 local -> 构造器字段接线 -> 终端返回/终端局部初始化”
//! 这一整段都还保持机械脚手架形状时，才会收回源码结构。若字段闭包已有 method
//! provenance，则先让位给 `direct`，避免把可读的声明再次折回匿名 constructor field。

use std::collections::BTreeSet;

use super::super::binding_flow::BindingUseIndex;
use super::super::binding_ref::{binding_from_name_ref, name_matches_binding};
use super::super::installer_iife::function_expr_is_substantial;
use super::direct::function_decl_target_from_lvalue;
use crate::ast::common::{
    AstAssign, AstBindingRef, AstExpr, AstFieldAccess, AstFunctionExpr, AstFunctionName, AstLValue,
    AstLocalAttr, AstLocalDecl, AstReturn, AstStmt, AstTableField, AstTableKey,
};

pub(super) fn try_inline_terminal_constructor_fields(
    stmts: &[AstStmt],
    method_fields: &BTreeSet<String>,
) -> Option<(AstStmt, usize)> {
    let AstStmt::LocalDecl(local_decl) = stmts.first()? else {
        return None;
    };
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    if local_decl.bindings[0].attr != AstLocalAttr::None {
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

    let mut consumed = 1usize;
    let mut inlined_any = false;
    while let Some(stmt) = stmts.get(consumed) {
        // Preserve an assignment that the existing function-sugar owner can render as a
        // method declaration.  Folding it into the constructor would erase the lvalue/closure
        // pair before `direct` gets a chance to consume the already-proven method field fact.
        if stmt_is_recoverable_method_decl(stmt, binding, method_fields) {
            // 候选拒绝[LayerBoundary]：该字段已有 method provenance，必须留给 direct owner 生成冒号声明，不能先折回匿名 table field。
            return None;
        }
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

    let AstStmt::Return(ret) = stmts.get(consumed)? else {
        return None;
    };
    let [AstExpr::Var(name)] = ret.values.as_slice() else {
        return None;
    };
    if !name_matches_binding(name, binding) {
        // 候选拒绝[SemanticBarrier:Identity]：终端 return 必须交回同一 constructor local；换成别的 binding 会删除仍需返回的对象。
        return None;
    }

    Some((AstStmt::LocalDecl(Box::new(rewritten)), consumed))
}

fn stmt_is_recoverable_method_decl(
    stmt: &AstStmt,
    binding: AstBindingRef,
    method_fields: &BTreeSet<String>,
) -> bool {
    if let AstStmt::FunctionDecl(function_decl) = stmt {
        let AstFunctionName::Method(path, _) = &function_decl.target else {
            return false;
        };
        return path.fields.len() == 1 && name_matches_binding(&path.root, binding);
    }
    let AstStmt::Assign(assign) = stmt else {
        return false;
    };
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return false;
    }
    let AstLValue::FieldAccess(access) = &assign.targets[0] else {
        return false;
    };
    let AstExpr::Var(base) = &access.base else {
        return false;
    };
    if !name_matches_binding(base, binding) {
        return false;
    }
    let AstExpr::FunctionExpr(function) = &assign.values[0] else {
        return false;
    };
    let target = function_decl_target_from_lvalue(&assign.targets[0], function, method_fields);
    matches!(target, Some((AstFunctionName::Method(_, _), _)))
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
    let rewritten_sink =
        rewrite_terminal_constructor_call_sink(sink, callee_binding, callee_expr, &arg_locals)?;
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
    // 证明缺陷[PotentialUnsoundness:Lifetime]：dead-after-sink 不等于词法 root 已死亡；PhysicalRoot local 原本活到 block 末，内联可提前触发弱表消失或 `__gc`。
    // 证明缺陷[PotentialPolicyViolation]：callee/arg 的 DebugHinted origin 未检查，源码身份会被无条件抹掉。
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
    if local_decl.bindings[0].attr != AstLocalAttr::None {
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

    let inner_value = arg_locals[inner_index].value.clone();
    let AstExpr::TableConstructor(_) = inner_value else {
        return false;
    };
    let AstExpr::TableConstructor(table) = &mut arg_locals[outer_index].value else {
        return false;
    };

    // 证明缺陷[PotentialUnsoundness:EvalOrder]：未证明 inner/outer 在 arg-local run 中相邻且同序；把 inner constructor 搬入 outer 字段会跨过中间 initializer（如 `h()`），可把 `outer; h(); inner` 的事件改成 `outer(inner); h()`。

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
    if !name_matches_binding(name, callee_binding) || call.args.len() != active_args.len() {
        // 候选拒绝[SemanticBarrier:Identity]：sink 必须调用同一 callee，且逐一承接全部未被嵌套消费的 constructor local。
        return None;
    }
    for (arg, expected) in call.args.iter().zip(active_args.iter()) {
        let AstExpr::Var(name) = arg else {
            // 候选拒绝[SemanticBarrier:EvalOrder]：arg 若不是纯 binding handoff，替换会删除或重排它自身的求值事件。
            return None;
        };
        if !name_matches_binding(name, expected.binding) {
            // 候选拒绝[SemanticBarrier:EvalOrder]：constructor locals 的实参顺序必须与原 call 一致，否则 initializer/参数求值顺序改变。
            return None;
        }
    }

    let mut rewritten = call.as_ref().clone();
    rewritten.callee = callee_expr.clone();
    rewritten.args = active_args
        .into_iter()
        .map(|arg| arg.value.clone())
        .collect();
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
