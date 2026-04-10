//! AST 子节点递归骨架的共享宏。
//!
//! readability walker / visitor 和 naming 模块的多个收集器都需要"按 AST 节点类型
//! 递归枚举子节点"。这里把 child dispatch 收成参数化宏，每个使用方只需提供
//! 自己的回调即可，不用重复维护 AST 形状的 match 骨架。

macro_rules! traverse_call_children {
    (
        $call:expr,
        iter = $iter:ident,
        borrow = [$($borrow:tt)+],
        expr($expr:ident) => $on_expr:block
    ) => {{
        match $call {
            crate::ast::AstCallKind::Call(call) => {
                {
                    let $expr = $($borrow)+ call.callee;
                    $on_expr
                }
                for $expr in call.args.$iter() {
                    $on_expr
                }
            }
            crate::ast::AstCallKind::MethodCall(call) => {
                {
                    let $expr = $($borrow)+ call.receiver;
                    $on_expr
                }
                for $expr in call.args.$iter() {
                    $on_expr
                }
            }
        }
    }};
}

macro_rules! traverse_lvalue_children {
    (
        $lvalue:expr,
        borrow = [$($borrow:tt)+],
        expr($expr:ident) => $on_expr:block
    ) => {{
        match $lvalue {
            crate::ast::AstLValue::Name(_) => {}
            crate::ast::AstLValue::FieldAccess(access) => {
                let $expr = $($borrow)+ access.base;
                $on_expr
            }
            crate::ast::AstLValue::IndexAccess(access) => {
                {
                    let $expr = $($borrow)+ access.base;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ access.index;
                    $on_expr
                }
            }
        }
    }};
}

macro_rules! traverse_expr_children {
    (
        $expr_node:expr,
        iter = $iter:ident,
        borrow = [$($borrow:tt)+],
        expr($expr:ident) => $on_expr:block,
        function($function:ident) => $on_function:block
    ) => {{
        match $expr_node {
            crate::ast::AstExpr::FieldAccess(access) => {
                let $expr = $($borrow)+ access.base;
                $on_expr
            }
            crate::ast::AstExpr::IndexAccess(access) => {
                {
                    let $expr = $($borrow)+ access.base;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ access.index;
                    $on_expr
                }
            }
            crate::ast::AstExpr::Unary(unary) => {
                let $expr = $($borrow)+ unary.expr;
                $on_expr
            }
            crate::ast::AstExpr::Binary(binary) => {
                {
                    let $expr = $($borrow)+ binary.lhs;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ binary.rhs;
                    $on_expr
                }
            }
            crate::ast::AstExpr::LogicalAnd(logical)
            | crate::ast::AstExpr::LogicalOr(logical) => {
                {
                    let $expr = $($borrow)+ logical.lhs;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ logical.rhs;
                    $on_expr
                }
            }
            crate::ast::AstExpr::Call(call) => {
                {
                    let $expr = $($borrow)+ call.callee;
                    $on_expr
                }
                for $expr in call.args.$iter() {
                    $on_expr
                }
            }
            crate::ast::AstExpr::MethodCall(call) => {
                {
                    let $expr = $($borrow)+ call.receiver;
                    $on_expr
                }
                for $expr in call.args.$iter() {
                    $on_expr
                }
            }
            crate::ast::AstExpr::SingleValue(inner) => {
                let $expr = $($borrow)+ **inner;
                $on_expr
            }
            crate::ast::AstExpr::TableConstructor(table) => {
                for field in table.fields.$iter() {
                    match field {
                        crate::ast::AstTableField::Array(value) => {
                            let $expr = value;
                            $on_expr
                        }
                        crate::ast::AstTableField::Record(record) => {
                            match $($borrow)+ record.key {
                                crate::ast::AstTableKey::Name(_) => {}
                                crate::ast::AstTableKey::Expr($expr) => {
                                    $on_expr
                                }
                            }
                            let $expr = $($borrow)+ record.value;
                            $on_expr
                        }
                    }
                }
            }
            crate::ast::AstExpr::FunctionExpr(function) => {
                let $function = $($borrow)+ **function;
                $on_function
            }
            crate::ast::AstExpr::Nil
            | crate::ast::AstExpr::Boolean(_)
            | crate::ast::AstExpr::Integer(_)
            | crate::ast::AstExpr::Number(_)
            | crate::ast::AstExpr::String(_)
            | crate::ast::AstExpr::Int64(_)
            | crate::ast::AstExpr::UInt64(_)
            | crate::ast::AstExpr::Complex { .. }
            | crate::ast::AstExpr::Var(_)
            | crate::ast::AstExpr::VarArg
            | crate::ast::AstExpr::Error(_) => {}
        }
    }};
}

macro_rules! traverse_stmt_children {
    (
        $stmt:expr,
        iter = $iter:ident,
        opt = $opt:ident,
        borrow = [$($borrow:tt)+],
        expr($expr:ident) => $on_expr:block,
        lvalue($lvalue:ident) => $on_lvalue:block,
        block($block:ident) => $on_block:block,
        function($function:ident) => $on_function:block,
        condition($condition:ident) => $on_condition:block,
        call($call_name:ident) => $on_call:block
    ) => {{
        match $stmt {
            crate::ast::AstStmt::LocalDecl(local_decl) => {
                for $expr in local_decl.values.$iter() {
                    $on_expr
                }
            }
            crate::ast::AstStmt::GlobalDecl(global_decl) => {
                for $expr in global_decl.values.$iter() {
                    $on_expr
                }
            }
            crate::ast::AstStmt::Assign(assign) => {
                for $lvalue in assign.targets.$iter() {
                    $on_lvalue
                }
                for $expr in assign.values.$iter() {
                    $on_expr
                }
            }
            crate::ast::AstStmt::CallStmt(call_stmt) => {
                let $call_name = $($borrow)+ call_stmt.call;
                $on_call
            }
            crate::ast::AstStmt::Return(ret) => {
                for $expr in ret.values.$iter() {
                    $on_expr
                }
            }
            crate::ast::AstStmt::If(if_stmt) => {
                {
                    let $condition = $($borrow)+ if_stmt.cond;
                    $on_condition
                }
                {
                    let $block = $($borrow)+ if_stmt.then_block;
                    $on_block
                }
                if let Some($block) = if_stmt.else_block.$opt() {
                    $on_block
                }
            }
            crate::ast::AstStmt::While(while_stmt) => {
                {
                    let $condition = $($borrow)+ while_stmt.cond;
                    $on_condition
                }
                {
                    let $block = $($borrow)+ while_stmt.body;
                    $on_block
                }
            }
            crate::ast::AstStmt::Repeat(repeat_stmt) => {
                {
                    let $block = $($borrow)+ repeat_stmt.body;
                    $on_block
                }
                {
                    let $condition = $($borrow)+ repeat_stmt.cond;
                    $on_condition
                }
            }
            crate::ast::AstStmt::NumericFor(numeric_for) => {
                {
                    let $expr = $($borrow)+ numeric_for.start;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ numeric_for.limit;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ numeric_for.step;
                    $on_expr
                }
                {
                    let $block = $($borrow)+ numeric_for.body;
                    $on_block
                }
            }
            crate::ast::AstStmt::GenericFor(generic_for) => {
                for $expr in generic_for.iterator.$iter() {
                    $on_expr
                }
                {
                    let $block = $($borrow)+ generic_for.body;
                    $on_block
                }
            }
            crate::ast::AstStmt::DoBlock($block) => {
                $on_block
            }
            crate::ast::AstStmt::FunctionDecl(function_decl) => {
                let $function = $($borrow)+ function_decl.func;
                $on_function
            }
            crate::ast::AstStmt::LocalFunctionDecl(local_function_decl) => {
                let $function = $($borrow)+ local_function_decl.func;
                $on_function
            }
            crate::ast::AstStmt::Break
            | crate::ast::AstStmt::Continue
            | crate::ast::AstStmt::Goto(_)
            | crate::ast::AstStmt::Label(_)
            | crate::ast::AstStmt::Error(_) => {}
        }
    }};
}

pub(crate) use traverse_call_children;
pub(crate) use traverse_expr_children;
pub(crate) use traverse_lvalue_children;
pub(crate) use traverse_stmt_children;
