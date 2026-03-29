//! 这个文件提供 HIR simplify 共享的只读 visitor。
//!
//! 很多 simplify pass 在真正改写前，只是想先遍历 HIR 收集一批事实，例如：
//! - 哪些 label 仍然被 `goto` 引用
//! - 哪些 temp 在当前 proto 里有显式定义
//! - 某段 stmt 切片里还会读到哪些 local/temp
//!
//! 过去这些分析各自复制了一整套 `block/stmt/lvalue/call/expr` 递归骨架。这里把只读
//! 遍历收成共享设施，让 collector 更专注在“看到某个节点时记录什么”。
//!
//! 它不会跨层补事实，也不会主动进入子 proto 的 body 重新扫描整棵模块树；这里的
//! 作用域就是“当前正在 simplify 的这一个 proto”。例如 closure 只会访问 capture
//! 表达式，因为那正是当前 proto 能直接消费的事实边界。

use crate::hir::common::{
    HirBlock, HirCallExpr, HirDecisionTarget, HirExpr, HirLValue, HirProto, HirStmt, HirTableField,
    HirTableKey,
};

pub(super) trait HirVisitor {
    fn visit_block(&mut self, _block: &HirBlock) {}

    fn visit_stmt(&mut self, _stmt: &HirStmt) {}

    fn visit_expr(&mut self, _expr: &HirExpr) {}

    fn visit_lvalue(&mut self, _lvalue: &HirLValue) {}

    fn visit_call(&mut self, _call: &HirCallExpr) {}
}

pub(super) fn visit_proto(proto: &HirProto, visitor: &mut impl HirVisitor) {
    visit_block(&proto.body, visitor);
}

pub(super) fn visit_block(block: &HirBlock, visitor: &mut impl HirVisitor) {
    visitor.visit_block(block);
    visit_stmts(&block.stmts, visitor);
}

pub(super) fn visit_stmts(stmts: &[HirStmt], visitor: &mut impl HirVisitor) {
    for stmt in stmts {
        visit_stmt(stmt, visitor);
    }
}

fn visit_stmt(stmt: &HirStmt, visitor: &mut impl HirVisitor) {
    visitor.visit_stmt(stmt);
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                visit_expr(value, visitor);
            }
        }
        HirStmt::Assign(assign) => {
            for target in &assign.targets {
                visit_lvalue(target, visitor);
            }
            for value in &assign.values {
                visit_expr(value, visitor);
            }
        }
        HirStmt::TableSetList(set_list) => {
            visit_expr(&set_list.base, visitor);
            for value in &set_list.values {
                visit_expr(value, visitor);
            }
            if let Some(trailing) = &set_list.trailing_multivalue {
                visit_expr(trailing, visitor);
            }
        }
        HirStmt::ErrNil(err_nil) => visit_expr(&err_nil.value, visitor),
        HirStmt::ToBeClosed(to_be_closed) => visit_expr(&to_be_closed.value, visitor),
        HirStmt::CallStmt(call_stmt) => visit_call(&call_stmt.call, visitor),
        HirStmt::Return(ret) => {
            for value in &ret.values {
                visit_expr(value, visitor);
            }
        }
        HirStmt::If(if_stmt) => {
            visit_expr(&if_stmt.cond, visitor);
            visit_block(&if_stmt.then_block, visitor);
            if let Some(else_block) = &if_stmt.else_block {
                visit_block(else_block, visitor);
            }
        }
        HirStmt::While(while_stmt) => {
            visit_expr(&while_stmt.cond, visitor);
            visit_block(&while_stmt.body, visitor);
        }
        HirStmt::Repeat(repeat_stmt) => {
            visit_block(&repeat_stmt.body, visitor);
            visit_expr(&repeat_stmt.cond, visitor);
        }
        HirStmt::NumericFor(numeric_for) => {
            visit_expr(&numeric_for.start, visitor);
            visit_expr(&numeric_for.limit, visitor);
            visit_expr(&numeric_for.step, visitor);
            visit_block(&numeric_for.body, visitor);
        }
        HirStmt::GenericFor(generic_for) => {
            for value in &generic_for.iterator {
                visit_expr(value, visitor);
            }
            visit_block(&generic_for.body, visitor);
        }
        HirStmt::Block(block) => visit_block(block, visitor),
        HirStmt::Unstructured(unstructured) => visit_block(&unstructured.body, visitor),
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
}

pub(super) fn visit_call(call: &HirCallExpr, visitor: &mut impl HirVisitor) {
    visitor.visit_call(call);
    visit_expr(&call.callee, visitor);
    for arg in &call.args {
        visit_expr(arg, visitor);
    }
}

pub(super) fn visit_lvalue(lvalue: &HirLValue, visitor: &mut impl HirVisitor) {
    visitor.visit_lvalue(lvalue);
    if let HirLValue::TableAccess(access) = lvalue {
        visit_expr(&access.base, visitor);
        visit_expr(&access.key, visitor);
    }
}

pub(super) fn visit_expr(expr: &HirExpr, visitor: &mut impl HirVisitor) {
    visitor.visit_expr(expr);
    match expr {
        HirExpr::TableAccess(access) => {
            visit_expr(&access.base, visitor);
            visit_expr(&access.key, visitor);
        }
        HirExpr::Unary(unary) => visit_expr(&unary.expr, visitor),
        HirExpr::Binary(binary) => {
            visit_expr(&binary.lhs, visitor);
            visit_expr(&binary.rhs, visitor);
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            visit_expr(&logical.lhs, visitor);
            visit_expr(&logical.rhs, visitor);
        }
        HirExpr::Decision(decision) => {
            for node in &decision.nodes {
                visit_expr(&node.test, visitor);
                visit_decision_target(&node.truthy, visitor);
                visit_decision_target(&node.falsy, visitor);
            }
        }
        HirExpr::Call(call) => visit_call(call, visitor),
        HirExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    HirTableField::Array(value) => visit_expr(value, visitor),
                    HirTableField::Record(field) => {
                        if let HirTableKey::Expr(key) = &field.key {
                            visit_expr(key, visitor);
                        }
                        visit_expr(&field.value, visitor);
                    }
                }
            }
            if let Some(trailing) = &table.trailing_multivalue {
                visit_expr(trailing, visitor);
            }
        }
        HirExpr::Closure(closure) => {
            for capture in &closure.captures {
                visit_expr(&capture.value, visitor);
            }
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => {}
    }
}

pub(super) fn visit_decision_target(target: &HirDecisionTarget, visitor: &mut impl HirVisitor) {
    if let HirDecisionTarget::Expr(expr) = target {
        visit_expr(expr, visitor);
    }
}
