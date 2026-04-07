//! 这个文件承载 HIR simplify walker / visitor 共用的递归骨架。
//!
//! `walk` 和 `visit` 的外部语义不同：前者负责可变重写并返回 `changed`，后者负责只读收集。
//! 但它们在"一个节点有哪些子节点需要继续递归"这件事上是同一套结构事实。
//! 这里把 child dispatch 收成共享宏，避免两边继续平行维护 HIR 形状。

macro_rules! traverse_hir_call_children {
    (
        $call:expr,
        iter = $iter:ident,
        borrow = [$($borrow:tt)+],
        expr($expr:ident) => $on_expr:block
    ) => {{
        {
            let $expr = $($borrow)+ $call.callee;
            $on_expr
        }
        for $expr in $call.args.$iter() {
            $on_expr
        }
    }};
}

macro_rules! traverse_hir_lvalue_children {
    (
        $lvalue:expr,
        borrow = [$($borrow:tt)+],
        expr($expr:ident) => $on_expr:block
    ) => {{
        match $lvalue {
            crate::hir::common::HirLValue::TableAccess(access) => {
                {
                    let $expr = $($borrow)+ access.base;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ access.key;
                    $on_expr
                }
            }
            crate::hir::common::HirLValue::Temp(_)
            | crate::hir::common::HirLValue::Local(_)
            | crate::hir::common::HirLValue::Upvalue(_)
            | crate::hir::common::HirLValue::Global(_) => {}
        }
    }};
}

macro_rules! traverse_hir_decision_children {
    (
        $decision:expr,
        iter = $iter:ident,
        borrow = [$($borrow:tt)+],
        expr($expr:ident) => $on_expr:block,
        condition($cond:ident) => $on_cond:block
    ) => {{
        for node in $decision.nodes.$iter() {
            {
                let $cond = $($borrow)+ node.test;
                $on_cond
            }
            match $($borrow)+ node.truthy {
                crate::hir::common::HirDecisionTarget::Expr($expr) => {
                    $on_expr
                }
                crate::hir::common::HirDecisionTarget::Node(_)
                | crate::hir::common::HirDecisionTarget::CurrentValue => {}
            }
            match $($borrow)+ node.falsy {
                crate::hir::common::HirDecisionTarget::Expr($expr) => {
                    $on_expr
                }
                crate::hir::common::HirDecisionTarget::Node(_)
                | crate::hir::common::HirDecisionTarget::CurrentValue => {}
            }
        }
    }};
}

macro_rules! traverse_hir_table_constructor_children {
    (
        $table:expr,
        iter = $iter:ident,
        opt = $opt:ident,
        borrow = [$($borrow:tt)+],
        expr($expr:ident) => $on_expr:block
    ) => {{
        for field in $table.fields.$iter() {
            match field {
                crate::hir::common::HirTableField::Array($expr) => {
                    $on_expr
                }
                crate::hir::common::HirTableField::Record(record) => {
                    match $($borrow)+ record.key {
                        crate::hir::common::HirTableKey::Name(_) => {}
                        crate::hir::common::HirTableKey::Expr($expr) => {
                            $on_expr
                        }
                    }
                    {
                        let $expr = $($borrow)+ record.value;
                        $on_expr
                    }
                }
            }
        }
        if let Some($expr) = $table.trailing_multivalue.$opt() {
            $on_expr
        }
    }};
}

macro_rules! traverse_hir_expr_children {
    (
        $expr_node:expr,
        iter = $iter:ident,
        borrow = [$($borrow:tt)+],
        expr($expr:ident) => $on_expr:block,
        call($call:ident) => $on_call:block,
        decision($decision:ident) => $on_decision:block,
        table_constructor($table:ident) => $on_table:block
    ) => {{
        match $expr_node {
            crate::hir::common::HirExpr::TableAccess(access) => {
                {
                    let $expr = $($borrow)+ access.base;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ access.key;
                    $on_expr
                }
            }
            crate::hir::common::HirExpr::Unary(unary) => {
                let $expr = $($borrow)+ unary.expr;
                $on_expr
            }
            crate::hir::common::HirExpr::Binary(binary) => {
                {
                    let $expr = $($borrow)+ binary.lhs;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ binary.rhs;
                    $on_expr
                }
            }
            crate::hir::common::HirExpr::LogicalAnd(logical)
            | crate::hir::common::HirExpr::LogicalOr(logical) => {
                {
                    let $expr = $($borrow)+ logical.lhs;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ logical.rhs;
                    $on_expr
                }
            }
            crate::hir::common::HirExpr::Decision($decision) => {
                $on_decision
            }
            crate::hir::common::HirExpr::Call($call) => {
                $on_call
            }
            crate::hir::common::HirExpr::TableConstructor($table) => {
                $on_table
            }
            crate::hir::common::HirExpr::Closure(closure) => {
                for capture in closure.captures.$iter() {
                    let $expr = $($borrow)+ capture.value;
                    $on_expr
                }
            }
            crate::hir::common::HirExpr::Nil
            | crate::hir::common::HirExpr::Boolean(_)
            | crate::hir::common::HirExpr::Integer(_)
            | crate::hir::common::HirExpr::Number(_)
            | crate::hir::common::HirExpr::String(_)
            | crate::hir::common::HirExpr::Int64(_)
            | crate::hir::common::HirExpr::UInt64(_)
            | crate::hir::common::HirExpr::Complex { .. }
            | crate::hir::common::HirExpr::ParamRef(_)
            | crate::hir::common::HirExpr::LocalRef(_)
            | crate::hir::common::HirExpr::UpvalueRef(_)
            | crate::hir::common::HirExpr::TempRef(_)
            | crate::hir::common::HirExpr::GlobalRef(_)
            | crate::hir::common::HirExpr::VarArg
            | crate::hir::common::HirExpr::Unresolved(_) => {}
        }
    }};
}

macro_rules! traverse_hir_stmt_children {
    (
        $stmt:expr,
        iter = $iter:ident,
        opt = $opt:ident,
        borrow = [$($borrow:tt)+],
        expr($expr:ident) => $on_expr:block,
        lvalue($lvalue:ident) => $on_lvalue:block,
        block($block:ident) => $on_block:block,
        call($call:ident) => $on_call:block,
        condition($cond:ident) => $on_cond:block
    ) => {{
        match $stmt {
            crate::hir::common::HirStmt::LocalDecl(local_decl) => {
                for $expr in local_decl.values.$iter() {
                    $on_expr
                }
            }
            crate::hir::common::HirStmt::Assign(assign) => {
                for $lvalue in assign.targets.$iter() {
                    $on_lvalue
                }
                for $expr in assign.values.$iter() {
                    $on_expr
                }
            }
            crate::hir::common::HirStmt::TableSetList(set_list) => {
                {
                    let $expr = $($borrow)+ set_list.base;
                    $on_expr
                }
                for $expr in set_list.values.$iter() {
                    $on_expr
                }
                if let Some($expr) = set_list.trailing_multivalue.$opt() {
                    $on_expr
                }
            }
            crate::hir::common::HirStmt::ErrNil(err_nil) => {
                let $expr = $($borrow)+ err_nil.value;
                $on_expr
            }
            crate::hir::common::HirStmt::ToBeClosed(to_be_closed) => {
                let $expr = $($borrow)+ to_be_closed.value;
                $on_expr
            }
            crate::hir::common::HirStmt::CallStmt(call_stmt) => {
                let $call = $($borrow)+ call_stmt.call;
                $on_call
            }
            crate::hir::common::HirStmt::Return(ret) => {
                for $expr in ret.values.$iter() {
                    $on_expr
                }
            }
            crate::hir::common::HirStmt::If(if_stmt) => {
                {
                    let $cond = $($borrow)+ if_stmt.cond;
                    $on_cond
                }
                {
                    let $block = $($borrow)+ if_stmt.then_block;
                    $on_block
                }
                if let Some($block) = if_stmt.else_block.$opt() {
                    $on_block
                }
            }
            crate::hir::common::HirStmt::While(while_stmt) => {
                {
                    let $cond = $($borrow)+ while_stmt.cond;
                    $on_cond
                }
                {
                    let $block = $($borrow)+ while_stmt.body;
                    $on_block
                }
            }
            crate::hir::common::HirStmt::Repeat(repeat_stmt) => {
                {
                    let $block = $($borrow)+ repeat_stmt.body;
                    $on_block
                }
                {
                    let $cond = $($borrow)+ repeat_stmt.cond;
                    $on_cond
                }
            }
            crate::hir::common::HirStmt::NumericFor(numeric_for) => {
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
            crate::hir::common::HirStmt::GenericFor(generic_for) => {
                for $expr in generic_for.iterator.$iter() {
                    $on_expr
                }
                {
                    let $block = $($borrow)+ generic_for.body;
                    $on_block
                }
            }
            crate::hir::common::HirStmt::Block($block) => {
                $on_block
            }
            crate::hir::common::HirStmt::Unstructured(unstructured) => {
                let $block = $($borrow)+ unstructured.body;
                $on_block
            }
            crate::hir::common::HirStmt::Break
            | crate::hir::common::HirStmt::Close(_)
            | crate::hir::common::HirStmt::Continue
            | crate::hir::common::HirStmt::Goto(_)
            | crate::hir::common::HirStmt::Label(_) => {}
        }
    }};
}

pub(super) use traverse_hir_call_children;
pub(super) use traverse_hir_decision_children;
pub(super) use traverse_hir_expr_children;
pub(super) use traverse_hir_lvalue_children;
pub(super) use traverse_hir_stmt_children;
pub(super) use traverse_hir_table_constructor_children;
