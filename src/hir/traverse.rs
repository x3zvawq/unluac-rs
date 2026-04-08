//! HIR 层共享的子节点遍历宏。
//!
//! 和 `ast::traverse` 同一套思路：把"一个 HIR 节点有哪些子节点需要递归"这件
//! 结构事实收成参数化宏，不同 pass 只需要提供回调就能得到完整的 child dispatch。
//!
//! 原先只在 `hir::simplify` 内部使用，现在提升到 `hir` 层面让 naming 等模块也能共享。

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
            crate::hir::HirLValue::TableAccess(access) => {
                {
                    let $expr = $($borrow)+ access.base;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ access.key;
                    $on_expr
                }
            }
            crate::hir::HirLValue::Temp(_)
            | crate::hir::HirLValue::Local(_)
            | crate::hir::HirLValue::Upvalue(_)
            | crate::hir::HirLValue::Global(_) => {}
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
                crate::hir::HirDecisionTarget::Expr($expr) => {
                    $on_expr
                }
                crate::hir::HirDecisionTarget::Node(_)
                | crate::hir::HirDecisionTarget::CurrentValue => {}
            }
            match $($borrow)+ node.falsy {
                crate::hir::HirDecisionTarget::Expr($expr) => {
                    $on_expr
                }
                crate::hir::HirDecisionTarget::Node(_)
                | crate::hir::HirDecisionTarget::CurrentValue => {}
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
                crate::hir::HirTableField::Array($expr) => {
                    $on_expr
                }
                crate::hir::HirTableField::Record(record) => {
                    match $($borrow)+ record.key {
                        crate::hir::HirTableKey::Name(_) => {}
                        crate::hir::HirTableKey::Expr($expr) => {
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
            crate::hir::HirExpr::TableAccess(access) => {
                {
                    let $expr = $($borrow)+ access.base;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ access.key;
                    $on_expr
                }
            }
            crate::hir::HirExpr::Unary(unary) => {
                let $expr = $($borrow)+ unary.expr;
                $on_expr
            }
            crate::hir::HirExpr::Binary(binary) => {
                {
                    let $expr = $($borrow)+ binary.lhs;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ binary.rhs;
                    $on_expr
                }
            }
            crate::hir::HirExpr::LogicalAnd(logical)
            | crate::hir::HirExpr::LogicalOr(logical) => {
                {
                    let $expr = $($borrow)+ logical.lhs;
                    $on_expr
                }
                {
                    let $expr = $($borrow)+ logical.rhs;
                    $on_expr
                }
            }
            crate::hir::HirExpr::Decision($decision) => {
                $on_decision
            }
            crate::hir::HirExpr::Call($call) => {
                $on_call
            }
            crate::hir::HirExpr::TableConstructor($table) => {
                $on_table
            }
            crate::hir::HirExpr::Closure(closure) => {
                for capture in closure.captures.$iter() {
                    let $expr = $($borrow)+ capture.value;
                    $on_expr
                }
            }
            crate::hir::HirExpr::Nil
            | crate::hir::HirExpr::Boolean(_)
            | crate::hir::HirExpr::Integer(_)
            | crate::hir::HirExpr::Number(_)
            | crate::hir::HirExpr::String(_)
            | crate::hir::HirExpr::Int64(_)
            | crate::hir::HirExpr::UInt64(_)
            | crate::hir::HirExpr::Complex { .. }
            | crate::hir::HirExpr::ParamRef(_)
            | crate::hir::HirExpr::LocalRef(_)
            | crate::hir::HirExpr::UpvalueRef(_)
            | crate::hir::HirExpr::TempRef(_)
            | crate::hir::HirExpr::GlobalRef(_)
            | crate::hir::HirExpr::VarArg
            | crate::hir::HirExpr::Unresolved(_) => {}
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
            crate::hir::HirStmt::LocalDecl(local_decl) => {
                for $expr in local_decl.values.$iter() {
                    $on_expr
                }
            }
            crate::hir::HirStmt::Assign(assign) => {
                for $lvalue in assign.targets.$iter() {
                    $on_lvalue
                }
                for $expr in assign.values.$iter() {
                    $on_expr
                }
            }
            crate::hir::HirStmt::TableSetList(set_list) => {
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
            crate::hir::HirStmt::ErrNil(err_nil) => {
                let $expr = $($borrow)+ err_nil.value;
                $on_expr
            }
            crate::hir::HirStmt::ToBeClosed(to_be_closed) => {
                let $expr = $($borrow)+ to_be_closed.value;
                $on_expr
            }
            crate::hir::HirStmt::CallStmt(call_stmt) => {
                let $call = $($borrow)+ call_stmt.call;
                $on_call
            }
            crate::hir::HirStmt::Return(ret) => {
                for $expr in ret.values.$iter() {
                    $on_expr
                }
            }
            crate::hir::HirStmt::If(if_stmt) => {
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
            crate::hir::HirStmt::While(while_stmt) => {
                {
                    let $cond = $($borrow)+ while_stmt.cond;
                    $on_cond
                }
                {
                    let $block = $($borrow)+ while_stmt.body;
                    $on_block
                }
            }
            crate::hir::HirStmt::Repeat(repeat_stmt) => {
                {
                    let $block = $($borrow)+ repeat_stmt.body;
                    $on_block
                }
                {
                    let $cond = $($borrow)+ repeat_stmt.cond;
                    $on_cond
                }
            }
            crate::hir::HirStmt::NumericFor(numeric_for) => {
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
            crate::hir::HirStmt::GenericFor(generic_for) => {
                for $expr in generic_for.iterator.$iter() {
                    $on_expr
                }
                {
                    let $block = $($borrow)+ generic_for.body;
                    $on_block
                }
            }
            crate::hir::HirStmt::Block($block) => {
                $on_block
            }
            crate::hir::HirStmt::Unstructured(unstructured) => {
                let $block = $($borrow)+ unstructured.body;
                $on_block
            }
            crate::hir::HirStmt::Break
            | crate::hir::HirStmt::Close(_)
            | crate::hir::HirStmt::Continue
            | crate::hir::HirStmt::Goto(_)
            | crate::hir::HirStmt::Label(_) => {}
        }
    }};
}

pub(crate) use traverse_hir_call_children;
pub(crate) use traverse_hir_decision_children;
pub(crate) use traverse_hir_expr_children;
pub(crate) use traverse_hir_lvalue_children;
pub(crate) use traverse_hir_stmt_children;
pub(crate) use traverse_hir_table_constructor_children;
