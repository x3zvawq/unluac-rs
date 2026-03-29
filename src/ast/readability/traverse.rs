//! 这个文件承载 readability walker / visitor 共用的 AST 递归骨架。
//!
//! `walk` 和 `visit` 的外部语义不同：前者负责可变重写并返回 `changed`，后者负责只读收集。
//! 但它们在“一个节点有哪些子节点需要继续递归”这件事上是同一套结构事实。
//! 这里把 child dispatch 收成共享宏，避免两边继续平行维护 AST 形状。

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum BlockKind {
    ModuleBody,
    FunctionBody,
    Regular,
}

macro_rules! traverse_call_children {
    (
        $call:expr,
        iter = $iter:ident,
        borrow = [$($borrow:tt)+],
        expr($expr:ident) => $on_expr:block
    ) => {{
        match $call {
            crate::ast::common::AstCallKind::Call(call) => {
                {
                    let $expr = $($borrow)+ call.callee;
                    $on_expr
                }
                for $expr in call.args.$iter() {
                    $on_expr
                }
            }
            crate::ast::common::AstCallKind::MethodCall(call) => {
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
            crate::ast::common::AstLValue::Name(_) => {}
            crate::ast::common::AstLValue::FieldAccess(access) => {
                let $expr = $($borrow)+ access.base;
                $on_expr
            }
            crate::ast::common::AstLValue::IndexAccess(access) => {
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
        function($function:ident, $function_kind:ident) => $on_function:block
    ) => {{
        match $expr_node {
            crate::ast::common::AstExpr::FieldAccess(access) => {
                let $expr = $($borrow)+ access.base;
                $on_expr
            }
            crate::ast::common::AstExpr::IndexAccess(access) => {
                {
                    let $expr = $($borrow)+ access.base;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ access.index;
                    $on_expr
                }
            }
            crate::ast::common::AstExpr::Unary(unary) => {
                let $expr = $($borrow)+ unary.expr;
                $on_expr
            }
            crate::ast::common::AstExpr::Binary(binary) => {
                {
                    let $expr = $($borrow)+ binary.lhs;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ binary.rhs;
                    $on_expr
                }
            }
            crate::ast::common::AstExpr::LogicalAnd(logical)
            | crate::ast::common::AstExpr::LogicalOr(logical) => {
                {
                    let $expr = $($borrow)+ logical.lhs;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ logical.rhs;
                    $on_expr
                }
            }
            crate::ast::common::AstExpr::Call(call) => {
                {
                    let $expr = $($borrow)+ call.callee;
                    $on_expr
                }
                for $expr in call.args.$iter() {
                    $on_expr
                }
            }
            crate::ast::common::AstExpr::MethodCall(call) => {
                {
                    let $expr = $($borrow)+ call.receiver;
                    $on_expr
                }
                for $expr in call.args.$iter() {
                    $on_expr
                }
            }
            crate::ast::common::AstExpr::SingleValue(inner) => {
                let $expr = $($borrow)+ **inner;
                $on_expr
            }
            crate::ast::common::AstExpr::TableConstructor(table) => {
                for field in table.fields.$iter() {
                    match field {
                        crate::ast::common::AstTableField::Array(value) => {
                            let $expr = value;
                            $on_expr
                        }
                        crate::ast::common::AstTableField::Record(record) => {
                            match $($borrow)+ record.key {
                                crate::ast::common::AstTableKey::Name(_) => {}
                                crate::ast::common::AstTableKey::Expr($expr) => {
                                    $on_expr
                                }
                            }
                            let $expr = $($borrow)+ record.value;
                            $on_expr
                        }
                    }
                }
            }
            crate::ast::common::AstExpr::FunctionExpr(function) => {
                let $function_kind = BlockKind::FunctionBody;
                let $function = $($borrow)+ **function;
                $on_function
            }
            crate::ast::common::AstExpr::Nil
            | crate::ast::common::AstExpr::Boolean(_)
            | crate::ast::common::AstExpr::Integer(_)
            | crate::ast::common::AstExpr::Number(_)
            | crate::ast::common::AstExpr::String(_)
            | crate::ast::common::AstExpr::Int64(_)
            | crate::ast::common::AstExpr::UInt64(_)
            | crate::ast::common::AstExpr::Complex { .. }
            | crate::ast::common::AstExpr::Var(_)
            | crate::ast::common::AstExpr::VarArg => {}
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
        block($block:ident, $block_kind:ident) => $on_block:block,
        function($function:ident, $function_kind:ident) => $on_function:block,
        condition($condition:ident) => $on_condition:block,
        call($call_name:ident) => $on_call:block
    ) => {{
        match $stmt {
            crate::ast::common::AstStmt::LocalDecl(local_decl) => {
                for $expr in local_decl.values.$iter() {
                    $on_expr
                }
            }
            crate::ast::common::AstStmt::GlobalDecl(global_decl) => {
                for $expr in global_decl.values.$iter() {
                    $on_expr
                }
            }
            crate::ast::common::AstStmt::Assign(assign) => {
                for $lvalue in assign.targets.$iter() {
                    $on_lvalue
                }
                for $expr in assign.values.$iter() {
                    $on_expr
                }
            }
            crate::ast::common::AstStmt::CallStmt(call_stmt) => {
                let $call_name = $($borrow)+ call_stmt.call;
                $on_call
            }
            crate::ast::common::AstStmt::Return(ret) => {
                for $expr in ret.values.$iter() {
                    $on_expr
                }
            }
            crate::ast::common::AstStmt::If(if_stmt) => {
                {
                    let $condition = $($borrow)+ if_stmt.cond;
                    $on_condition
                }
                {
                    let $block = $($borrow)+ if_stmt.then_block;
                    let $block_kind = BlockKind::Regular;
                    $on_block
                }
                if let Some($block) = if_stmt.else_block.$opt() {
                    let $block_kind = BlockKind::Regular;
                    $on_block
                }
            }
            crate::ast::common::AstStmt::While(while_stmt) => {
                {
                    let $condition = $($borrow)+ while_stmt.cond;
                    $on_condition
                }
                {
                    let $block = $($borrow)+ while_stmt.body;
                    let $block_kind = BlockKind::Regular;
                    $on_block
                }
            }
            crate::ast::common::AstStmt::Repeat(repeat_stmt) => {
                {
                    let $block = $($borrow)+ repeat_stmt.body;
                    let $block_kind = BlockKind::Regular;
                    $on_block
                }
                {
                    let $condition = $($borrow)+ repeat_stmt.cond;
                    $on_condition
                }
            }
            crate::ast::common::AstStmt::NumericFor(numeric_for) => {
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
                    let $block_kind = BlockKind::Regular;
                    $on_block
                }
            }
            crate::ast::common::AstStmt::GenericFor(generic_for) => {
                for $expr in generic_for.iterator.$iter() {
                    $on_expr
                }
                {
                    let $block = $($borrow)+ generic_for.body;
                    let $block_kind = BlockKind::Regular;
                    $on_block
                }
            }
            crate::ast::common::AstStmt::DoBlock($block) => {
                let $block_kind = BlockKind::Regular;
                $on_block
            }
            crate::ast::common::AstStmt::FunctionDecl(function_decl) => {
                let $function_kind = BlockKind::FunctionBody;
                let $function = $($borrow)+ function_decl.func;
                $on_function
            }
            crate::ast::common::AstStmt::LocalFunctionDecl(local_function_decl) => {
                let $function_kind = BlockKind::FunctionBody;
                let $function = $($borrow)+ local_function_decl.func;
                $on_function
            }
            crate::ast::common::AstStmt::Break
            | crate::ast::common::AstStmt::Continue
            | crate::ast::common::AstStmt::Goto(_)
            | crate::ast::common::AstStmt::Label(_) => {}
        }
    }};
}

pub(super) use traverse_call_children;
pub(super) use traverse_expr_children;
pub(super) use traverse_lvalue_children;
pub(super) use traverse_stmt_children;
