//! 当前函数体内 AST binding 树遍历的共享 helper。
//!
//! 这里只判断 binding 在调用参数、存储目标等源码上下文中的位置；通用名字访问
//! 查询由 `binding_flow` 持有，并消费共享 visitor 的 Read/Write/Capture 角色。
//! 例如 `t[x] = y` 的 x 是地址读取，不能当作被写入的 binding。

use crate::ast::common::{
    AstBindingRef, AstCallKind, AstExpr, AstLValue, AstStmt, AstTableField, AstTableKey,
};

use super::binding_flow::expr_reads_binding;

/// 只检查本语句的求值部分；子块和函数声明不属于当前 sink 的表达式位置。
fn stmt_has_binding_use_by(
    stmt: &AstStmt,
    binding: AstBindingRef,
    check_expr: impl Fn(&AstExpr, AstBindingRef) -> bool,
    check_call: impl Fn(&AstCallKind, AstBindingRef) -> bool,
    check_assign_target: impl Fn(&AstLValue, AstBindingRef) -> bool,
) -> bool {
    crate::ast::traverse::traverse_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(expr) => { if check_expr(expr, binding) { return true; } },
        lvalue(target) => { if check_assign_target(target, binding) { return true; } },
        block(_block) => {},
        function(_function) => {},
        condition(expr) => { if check_expr(expr, binding) { return true; } },
        call(call) => { if check_call(call, binding) { return true; } }
    );
    false
}

pub(super) fn stmt_has_nested_binding_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    stmt_has_binding_use_by(
        stmt,
        binding,
        |e, b| expr_has_nested_binding_use(e, b, false),
        call_has_nested_binding_use,
        lvalue_has_nested_binding_use,
    )
}

pub(super) fn stmt_has_access_base_binding_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    stmt_has_binding_use_by(
        stmt,
        binding,
        |e, b| expr_has_access_base_binding_use(e, b, false),
        call_has_access_base_binding_use,
        lvalue_has_access_base_binding_use,
    )
}

pub(super) fn stmt_has_index_binding_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    stmt_has_binding_use_by(
        stmt,
        binding,
        |e, b| expr_has_index_binding_use(e, b, false),
        call_has_index_binding_use,
        lvalue_has_index_binding_use,
    )
}

pub(super) fn stmt_has_direct_call_arg_binding_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    stmt_has_binding_use_by(
        stmt,
        binding,
        expr_has_direct_call_arg_binding_use,
        call_has_direct_call_arg_binding_use,
        |_, _| false,
    )
}

pub(super) fn stmt_has_nested_binding_value_use(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    stmt_has_binding_use_by(
        stmt,
        binding,
        |e, b| expr_has_nested_binding_use(e, b, false),
        call_has_nested_binding_use,
        |_, _| false,
    )
}

/// Return whether a binding is stored in a table constructor or table lvalue at this statement.
/// A call-valued local is a strong root until such a table value is cleared; inlining that call
/// directly into the table would shorten the root lifetime in the generated source.
pub(super) fn stmt_stores_binding_in_table(stmt: &AstStmt, binding: AstBindingRef) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|value| expr_contains_table_binding(value, binding)),
        AstStmt::Assign(assign) => {
            let table_target = assign.targets.iter().any(|target| match target {
                AstLValue::FieldAccess(access) => expr_reads_binding(&access.base, binding),
                AstLValue::IndexAccess(access) => {
                    expr_reads_binding(&access.base, binding)
                        || expr_reads_binding(&access.index, binding)
                }
                AstLValue::Name(_) => false,
            });
            table_target
                || (assign.targets.iter().any(|target| {
                    matches!(
                        target,
                        AstLValue::FieldAccess(_) | AstLValue::IndexAccess(_)
                    )
                }) && assign.values.iter().any(|value| {
                    expr_reads_binding(value, binding)
                        || expr_contains_table_binding(value, binding)
                }))
        }
        _ => false,
    }
}

fn expr_contains_table_binding(expr: &AstExpr, binding: AstBindingRef) -> bool {
    match expr {
        AstExpr::IfExpr(branch) => [&branch.cond, &branch.then_expr, &branch.else_expr]
            .into_iter()
            .any(|expr| expr_contains_table_binding(expr, binding)),
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            AstTableField::Array(value) => expr_reads_binding(value, binding),
            AstTableField::Record(record) => {
                let key_uses = match &record.key {
                    AstTableKey::Name(_) => false,
                    AstTableKey::Expr(key) => expr_reads_binding(key, binding),
                };
                key_uses || expr_reads_binding(&record.value, binding)
            }
        }),
        AstExpr::FieldAccess(access) => expr_contains_table_binding(&access.base, binding),
        AstExpr::IndexAccess(access) => {
            expr_contains_table_binding(&access.base, binding)
                || expr_contains_table_binding(&access.index, binding)
        }
        AstExpr::Unary(unary) => expr_contains_table_binding(&unary.expr, binding),
        AstExpr::Binary(binary) => {
            expr_contains_table_binding(&binary.lhs, binding)
                || expr_contains_table_binding(&binary.rhs, binding)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_contains_table_binding(&logical.lhs, binding)
                || expr_contains_table_binding(&logical.rhs, binding)
        }
        AstExpr::Call(call) => {
            expr_contains_table_binding(&call.callee, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_contains_table_binding(arg, binding))
        }
        AstExpr::MethodCall(call) => {
            expr_contains_table_binding(&call.receiver, binding)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_contains_table_binding(arg, binding))
        }
        AstExpr::SingleValue(inner) => expr_contains_table_binding(inner, binding),
        AstExpr::FunctionExpr(function) => function.captured_bindings.contains(&binding),
        AstExpr::Var(_)
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::CaptureInitializer(_)
        | AstExpr::VarArg
        | AstExpr::Error(_) => false,
    }
}

fn call_has_nested_binding_use(call: &AstCallKind, binding: AstBindingRef) -> bool {
    call_has_contextual_binding_use(call, binding, BindingUseContext::Nested { active: false })
}

fn lvalue_has_nested_binding_use(target: &AstLValue, binding: AstBindingRef) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => expr_has_nested_binding_use(&access.base, binding, true),
        AstLValue::IndexAccess(access) => {
            expr_has_nested_binding_use(&access.base, binding, true)
                || expr_has_nested_binding_use(&access.index, binding, true)
        }
    }
}

fn call_has_access_base_binding_use(call: &AstCallKind, binding: AstBindingRef) -> bool {
    call_has_contextual_binding_use(
        call,
        binding,
        BindingUseContext::AccessBase { active: false },
    )
}

fn call_has_index_binding_use(call: &AstCallKind, binding: AstBindingRef) -> bool {
    call_has_contextual_binding_use(call, binding, BindingUseContext::Index { active: false })
}

fn call_has_direct_call_arg_binding_use(call: &AstCallKind, binding: AstBindingRef) -> bool {
    call_has_contextual_binding_use(call, binding, BindingUseContext::DirectCallArg)
}

fn args_have_direct_call_arg_binding_use(args: &[AstExpr], binding: AstBindingRef) -> bool {
    args.iter()
        .any(|arg| matches!(arg, AstExpr::Var(name) if binding.matches_name_ref(name)))
}

fn call_has_contextual_binding_use(
    call: &AstCallKind,
    binding: AstBindingRef,
    context: BindingUseContext,
) -> bool {
    match call {
        AstCallKind::Call(call) => {
            call_parts_have_contextual_binding_use(&call.callee, &call.args, binding, context)
        }
        AstCallKind::MethodCall(call) => {
            call_parts_have_contextual_binding_use(&call.receiver, &call.args, binding, context)
        }
    }
}

fn call_parts_have_contextual_binding_use(
    target: &AstExpr,
    args: &[AstExpr],
    binding: AstBindingRef,
    context: BindingUseContext,
) -> bool {
    match context {
        // direct-call-arg 只关心“当前这次调用”的顶层实参；如果实参本身又是调用，
        // 那个内层调用是否可折叠应由它自己的父级表达式位置决定。
        BindingUseContext::DirectCallArg => args_have_direct_call_arg_binding_use(args, binding),
        _ => {
            expr_has_contextual_binding_use(target, binding, context.call_target())
                || args
                    .iter()
                    .any(|arg| expr_has_contextual_binding_use(arg, binding, context.call_arg()))
        }
    }
}

fn lvalue_has_access_base_binding_use(target: &AstLValue, binding: AstBindingRef) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => {
            expr_has_access_base_binding_use(&access.base, binding, true)
        }
        AstLValue::IndexAccess(access) => {
            expr_has_access_base_binding_use(&access.base, binding, true)
                || expr_has_access_base_binding_use(&access.index, binding, false)
        }
    }
}

fn lvalue_has_index_binding_use(target: &AstLValue, binding: AstBindingRef) -> bool {
    match target {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(access) => expr_has_index_binding_use(&access.base, binding, false),
        AstLValue::IndexAccess(access) => {
            expr_has_index_binding_use(&access.base, binding, false)
                || expr_has_index_binding_use(&access.index, binding, true)
        }
    }
}

/// 单棵表达式里的 binding use 位置状态。
///
/// Readability 的多个 pass 会问“这个 binding 是否出现在字段基底 / 索引 / 调用
/// callee / 嵌套表达式”等类似问题；用同一个状态机递归，避免每加一种位置查询
/// 都复制一整套 AST match。
#[derive(Clone, Copy)]
enum BindingUseContext {
    AccessBase { active: bool },
    Index { active: bool },
    DirectCallArg,
    Nested { active: bool },
}

impl BindingUseContext {
    fn matches_var(self) -> bool {
        match self {
            Self::AccessBase { active } | Self::Index { active } => active,
            Self::Nested { active } => active,
            Self::DirectCallArg => false,
        }
    }

    fn field_base(self) -> Self {
        match self {
            Self::AccessBase { .. } => Self::AccessBase { active: true },
            Self::Index { .. } => Self::Index { active: false },
            Self::Nested { .. } => Self::Nested { active: true },
            Self::DirectCallArg => Self::DirectCallArg,
        }
    }

    fn index_base(self) -> Self {
        match self {
            Self::AccessBase { .. } => Self::AccessBase { active: true },
            Self::Index { .. } => Self::Index { active: false },
            Self::Nested { .. } => Self::Nested { active: true },
            Self::DirectCallArg => Self::DirectCallArg,
        }
    }

    fn index_key(self) -> Self {
        match self {
            Self::AccessBase { .. } => Self::AccessBase { active: false },
            Self::Index { .. } => Self::Index { active: true },
            Self::Nested { .. } => Self::Nested { active: true },
            Self::DirectCallArg => Self::DirectCallArg,
        }
    }

    fn nested_expr(self) -> Self {
        match self {
            Self::AccessBase { .. } => Self::AccessBase { active: false },
            Self::Index { .. } => Self::Index { active: false },
            Self::Nested { .. } => Self::Nested { active: true },
            Self::DirectCallArg => Self::DirectCallArg,
        }
    }

    fn single_value(self) -> Self {
        self.nested_expr()
    }

    fn call_target(self) -> Self {
        match self {
            Self::Nested { .. } => Self::Nested { active: true },
            Self::AccessBase { .. } => Self::AccessBase { active: false },
            Self::Index { .. } => Self::Index { active: false },
            Self::DirectCallArg => Self::DirectCallArg,
        }
    }

    fn call_arg(self) -> Self {
        self.nested_expr()
    }
}

fn expr_has_access_base_binding_use(
    expr: &AstExpr,
    binding: AstBindingRef,
    access_base: bool,
) -> bool {
    expr_has_contextual_binding_use(
        expr,
        binding,
        BindingUseContext::AccessBase {
            active: access_base,
        },
    )
}

fn expr_has_index_binding_use(expr: &AstExpr, binding: AstBindingRef, index: bool) -> bool {
    expr_has_contextual_binding_use(expr, binding, BindingUseContext::Index { active: index })
}

fn expr_has_direct_call_arg_binding_use(expr: &AstExpr, binding: AstBindingRef) -> bool {
    expr_has_contextual_binding_use(expr, binding, BindingUseContext::DirectCallArg)
}

fn expr_has_nested_binding_use(expr: &AstExpr, binding: AstBindingRef, nested: bool) -> bool {
    expr_has_contextual_binding_use(expr, binding, BindingUseContext::Nested { active: nested })
}

fn expr_has_contextual_binding_use(
    expr: &AstExpr,
    binding: AstBindingRef,
    context: BindingUseContext,
) -> bool {
    match expr {
        AstExpr::IfExpr(branch) => [&branch.cond, &branch.then_expr, &branch.else_expr]
            .into_iter()
            .any(|expr| expr_has_contextual_binding_use(expr, binding, context.nested_expr())),
        AstExpr::Var(name) if binding.matches_name_ref(name) => context.matches_var(),
        AstExpr::FieldAccess(access) => {
            expr_has_contextual_binding_use(&access.base, binding, context.field_base())
        }
        AstExpr::IndexAccess(access) => {
            expr_has_contextual_binding_use(&access.base, binding, context.index_base())
                || expr_has_contextual_binding_use(&access.index, binding, context.index_key())
        }
        AstExpr::Call(call) => {
            call_parts_have_contextual_binding_use(&call.callee, &call.args, binding, context)
        }
        AstExpr::MethodCall(call) => {
            call_parts_have_contextual_binding_use(&call.receiver, &call.args, binding, context)
        }
        AstExpr::SingleValue(expr) => {
            expr_has_contextual_binding_use(expr, binding, context.single_value())
        }
        AstExpr::Unary(unary) => {
            expr_has_contextual_binding_use(&unary.expr, binding, context.nested_expr())
        }
        AstExpr::Binary(binary) => {
            expr_has_contextual_binding_use(&binary.lhs, binding, context.nested_expr())
                || expr_has_contextual_binding_use(&binary.rhs, binding, context.nested_expr())
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_has_contextual_binding_use(&logical.lhs, binding, context.nested_expr())
                || expr_has_contextual_binding_use(&logical.rhs, binding, context.nested_expr())
        }
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            AstTableField::Array(value) => {
                expr_has_contextual_binding_use(value, binding, context.nested_expr())
            }
            AstTableField::Record(record) => {
                let key_matches = match &record.key {
                    AstTableKey::Name(_) => false,
                    AstTableKey::Expr(key) => {
                        expr_has_contextual_binding_use(key, binding, context.nested_expr())
                    }
                };
                key_matches
                    || expr_has_contextual_binding_use(
                        &record.value,
                        binding,
                        context.nested_expr(),
                    )
            }
        }),
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
        | AstExpr::Var(_)
        | AstExpr::CaptureInitializer(_)
        | AstExpr::VarArg
        | AstExpr::Error(_) => false,
    }
}
