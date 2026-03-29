//! 这个文件提供 HIR simplify pass 共享的递归 walker。
//!
//! 很多 simplify pass 都只是“后序遍历整棵 HIR，然后在局部节点上做保守重写”。
//! 如果每个 pass 都各自维护一套 `block/stmt/expr/lvalue/call` 递归骨架，
//! 后面很容易一边修一个地方，一边忘掉另一个 pass 里的同构逻辑。这里把这层
//! 纯遍历样板收成共享设施，让各个 pass 只关心“当前 expr 要不要改写”。

use crate::hir::common::{
    HirBlock, HirCallExpr, HirDecisionExpr, HirDecisionTarget, HirExpr, HirLValue, HirProto,
    HirStmt, HirTableConstructor, HirTableField, HirTableKey,
};

pub(super) trait ExprRewritePass {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool;

    fn rewrite_condition_expr(&mut self, expr: &mut HirExpr) -> bool {
        self.rewrite_expr(expr)
    }
}

pub(super) fn rewrite_proto_exprs(proto: &mut HirProto, pass: &mut impl ExprRewritePass) -> bool {
    rewrite_block(&mut proto.body, pass)
}

fn rewrite_block(block: &mut HirBlock, pass: &mut impl ExprRewritePass) -> bool {
    block
        .stmts
        .iter_mut()
        .fold(false, |changed, stmt| rewrite_stmt(stmt, pass) || changed)
}

fn rewrite_stmt(stmt: &mut HirStmt, pass: &mut impl ExprRewritePass) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter_mut()
            .fold(false, |changed, expr| rewrite_expr(expr, pass) || changed),
        HirStmt::Assign(assign) => {
            let targets_changed = assign.targets.iter_mut().fold(false, |changed, target| {
                rewrite_lvalue(target, pass) || changed
            });
            let values_changed = assign
                .values
                .iter_mut()
                .fold(false, |changed, expr| rewrite_expr(expr, pass) || changed);
            targets_changed || values_changed
        }
        HirStmt::TableSetList(set_list) => {
            let base_changed = rewrite_expr(&mut set_list.base, pass);
            let values_changed = set_list
                .values
                .iter_mut()
                .fold(false, |changed, expr| rewrite_expr(expr, pass) || changed);
            let trailing_changed = set_list
                .trailing_multivalue
                .as_mut()
                .is_some_and(|expr| rewrite_expr(expr, pass));
            base_changed || values_changed || trailing_changed
        }
        HirStmt::ErrNil(err_nil) => rewrite_expr(&mut err_nil.value, pass),
        HirStmt::ToBeClosed(to_be_closed) => rewrite_expr(&mut to_be_closed.value, pass),
        HirStmt::CallStmt(call_stmt) => rewrite_call_expr(&mut call_stmt.call, pass),
        HirStmt::Return(ret) => ret
            .values
            .iter_mut()
            .fold(false, |changed, expr| rewrite_expr(expr, pass) || changed),
        HirStmt::If(if_stmt) => {
            rewrite_condition_expr(&mut if_stmt.cond, pass)
                || rewrite_block(&mut if_stmt.then_block, pass)
                || if_stmt
                    .else_block
                    .as_mut()
                    .is_some_and(|else_block| rewrite_block(else_block, pass))
        }
        HirStmt::While(while_stmt) => {
            rewrite_condition_expr(&mut while_stmt.cond, pass)
                || rewrite_block(&mut while_stmt.body, pass)
        }
        HirStmt::Repeat(repeat_stmt) => {
            rewrite_block(&mut repeat_stmt.body, pass)
                || rewrite_condition_expr(&mut repeat_stmt.cond, pass)
        }
        HirStmt::NumericFor(numeric_for) => {
            rewrite_expr(&mut numeric_for.start, pass)
                || rewrite_expr(&mut numeric_for.limit, pass)
                || rewrite_expr(&mut numeric_for.step, pass)
                || rewrite_block(&mut numeric_for.body, pass)
        }
        HirStmt::GenericFor(generic_for) => {
            let iterator_changed = generic_for
                .iterator
                .iter_mut()
                .fold(false, |changed, expr| rewrite_expr(expr, pass) || changed);
            iterator_changed || rewrite_block(&mut generic_for.body, pass)
        }
        HirStmt::Block(block) => rewrite_block(block, pass),
        HirStmt::Unstructured(unstructured) => rewrite_block(&mut unstructured.body, pass),
        HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn rewrite_lvalue(lvalue: &mut HirLValue, pass: &mut impl ExprRewritePass) -> bool {
    match lvalue {
        HirLValue::TableAccess(access) => {
            rewrite_expr(&mut access.base, pass) || rewrite_expr(&mut access.key, pass)
        }
        HirLValue::Temp(_) | HirLValue::Local(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => {
            false
        }
    }
}

fn rewrite_call_expr(call: &mut HirCallExpr, pass: &mut impl ExprRewritePass) -> bool {
    let callee_changed = rewrite_expr(&mut call.callee, pass);
    let args_changed = call
        .args
        .iter_mut()
        .fold(false, |changed, arg| rewrite_expr(arg, pass) || changed);
    callee_changed || args_changed
}

fn rewrite_expr(expr: &mut HirExpr, pass: &mut impl ExprRewritePass) -> bool {
    let nested_changed = match expr {
        HirExpr::TableAccess(access) => {
            rewrite_expr(&mut access.base, pass) || rewrite_expr(&mut access.key, pass)
        }
        HirExpr::Unary(unary) => rewrite_expr(&mut unary.expr, pass),
        HirExpr::Binary(binary) => {
            rewrite_expr(&mut binary.lhs, pass) || rewrite_expr(&mut binary.rhs, pass)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            rewrite_expr(&mut logical.lhs, pass) || rewrite_expr(&mut logical.rhs, pass)
        }
        HirExpr::Decision(decision) => rewrite_decision_expr(decision, pass),
        HirExpr::Call(call) => rewrite_call_expr(call, pass),
        HirExpr::TableConstructor(table) => rewrite_table_constructor(table, pass),
        HirExpr::Closure(closure) => closure.captures.iter_mut().fold(false, |acc, capture| {
            rewrite_expr(&mut capture.value, pass) || acc
        }),
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
        | HirExpr::Unresolved(_) => false,
    };

    pass.rewrite_expr(expr) || nested_changed
}

fn rewrite_condition_expr(expr: &mut HirExpr, pass: &mut impl ExprRewritePass) -> bool {
    let nested_changed = rewrite_expr(expr, pass);
    pass.rewrite_condition_expr(expr) || nested_changed
}

fn rewrite_decision_expr(decision: &mut HirDecisionExpr, pass: &mut impl ExprRewritePass) -> bool {
    decision.nodes.iter_mut().fold(false, |changed, node| {
        let test_changed = rewrite_condition_expr(&mut node.test, pass);
        let truthy_changed = rewrite_decision_target(&mut node.truthy, pass);
        let falsy_changed = rewrite_decision_target(&mut node.falsy, pass);
        changed || test_changed || truthy_changed || falsy_changed
    })
}

fn rewrite_decision_target(
    target: &mut HirDecisionTarget,
    pass: &mut impl ExprRewritePass,
) -> bool {
    match target {
        HirDecisionTarget::Expr(expr) => rewrite_expr(expr, pass),
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
    }
}

fn rewrite_table_constructor(
    table: &mut HirTableConstructor,
    pass: &mut impl ExprRewritePass,
) -> bool {
    let fields_changed = table.fields.iter_mut().fold(false, |changed, field| {
        let field_changed = match field {
            HirTableField::Array(expr) => rewrite_expr(expr, pass),
            HirTableField::Record(field) => {
                let key_changed = match &mut field.key {
                    HirTableKey::Name(_) => false,
                    HirTableKey::Expr(expr) => rewrite_expr(expr, pass),
                };
                let value_changed = rewrite_expr(&mut field.value, pass);
                key_changed || value_changed
            }
        };
        changed || field_changed
    });
    let trailing_changed = table
        .trailing_multivalue
        .as_mut()
        .is_some_and(|expr| rewrite_expr(expr, pass));

    fields_changed || trailing_changed
}
