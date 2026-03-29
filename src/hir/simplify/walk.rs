//! 这个文件提供 HIR simplify pass 共享的递归 walker。
//!
//! 很多 simplify pass 都只是“后序遍历整棵 HIR，然后在局部 block/stmt/expr 上做保守
//! 重写”。如果每个 pass 都各自维护一套 `block/stmt/lvalue/call/expr` 骨架，后面一旦
//! 新增 HIR 节点或调整遍历顺序，就得在多处同步返工。
//!
//! 这里把公共遍历样板收成两层接口：
//! - `HirRewritePass` 负责通用 block/stmt/expr 级重写
//! - `ExprRewritePass` 作为兼容层，继续服务“只关心表达式”的现有 pass
//!
//! 它不会替具体 pass 决定“哪些节点该改、哪些事实可信”；这些语义仍然由各个 pass
//! 自己负责。这个文件只统一递归顺序和进入子节点的边界，避免不同 pass 各自长出
//! 一套不一致的 walker。
//!
//! 例子：
//! - `logical_simplify` 只需要实现 `ExprRewritePass`
//! - `dead_labels` 这类要在整段 block 上做删改的 pass，则实现 `HirRewritePass`
//! - `close_scopes / decision-eliminate` 这类自带 block rebuild 的 pass，则可以只复用
//!   下面的 `for_each_nested_block_mut / rewrite_nested_blocks_in_stmt`

use crate::hir::common::{
    HirBlock, HirCallExpr, HirDecisionExpr, HirDecisionTarget, HirExpr, HirLValue, HirProto,
    HirStmt, HirTableConstructor, HirTableField, HirTableKey,
};

pub(super) trait HirRewritePass {
    fn rewrite_block(&mut self, _block: &mut HirBlock) -> bool {
        false
    }

    fn rewrite_stmt(&mut self, _stmt: &mut HirStmt) -> bool {
        false
    }

    fn rewrite_expr(&mut self, _expr: &mut HirExpr) -> bool {
        false
    }

    fn rewrite_lvalue(&mut self, _lvalue: &mut HirLValue) -> bool {
        false
    }

    fn rewrite_call(&mut self, _call: &mut HirCallExpr) -> bool {
        false
    }

    fn rewrite_condition_expr(&mut self, expr: &mut HirExpr) -> bool {
        self.rewrite_expr(expr)
    }
}

pub(super) fn rewrite_proto(proto: &mut HirProto, pass: &mut impl HirRewritePass) -> bool {
    rewrite_block(&mut proto.body, pass)
}

pub(super) trait ExprRewritePass {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool;

    fn rewrite_condition_expr(&mut self, expr: &mut HirExpr) -> bool {
        self.rewrite_expr(expr)
    }
}

pub(super) fn rewrite_proto_exprs(proto: &mut HirProto, pass: &mut impl ExprRewritePass) -> bool {
    let mut adapter = ExprRewritePassAdapter { pass };
    rewrite_proto(proto, &mut adapter)
}

pub(super) fn for_each_nested_block_mut(stmt: &mut HirStmt, visit: &mut impl FnMut(&mut HirBlock)) {
    match stmt {
        HirStmt::If(if_stmt) => {
            visit(&mut if_stmt.then_block);
            if let Some(else_block) = &mut if_stmt.else_block {
                visit(else_block);
            }
        }
        HirStmt::While(while_stmt) => visit(&mut while_stmt.body),
        HirStmt::Repeat(repeat_stmt) => visit(&mut repeat_stmt.body),
        HirStmt::NumericFor(numeric_for) => visit(&mut numeric_for.body),
        HirStmt::GenericFor(generic_for) => visit(&mut generic_for.body),
        HirStmt::Block(block) => visit(block),
        HirStmt::Unstructured(unstructured) => visit(&mut unstructured.body),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => {}
    }
}

pub(super) fn rewrite_nested_blocks_in_stmt(
    stmt: &mut HirStmt,
    rewrite_block: &mut impl FnMut(&mut HirBlock) -> bool,
) -> bool {
    let mut changed = false;
    for_each_nested_block_mut(stmt, &mut |block| {
        changed |= rewrite_block(block);
    });
    changed
}

struct ExprRewritePassAdapter<'a, P> {
    pass: &'a mut P,
}

impl<P: ExprRewritePass> HirRewritePass for ExprRewritePassAdapter<'_, P> {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        self.pass.rewrite_expr(expr)
    }

    fn rewrite_condition_expr(&mut self, expr: &mut HirExpr) -> bool {
        self.pass.rewrite_condition_expr(expr)
    }
}

fn rewrite_block(block: &mut HirBlock, pass: &mut impl HirRewritePass) -> bool {
    let nested_changed = block
        .stmts
        .iter_mut()
        .fold(false, |changed, stmt| rewrite_stmt(stmt, pass) || changed);
    pass.rewrite_block(block) || nested_changed
}

fn rewrite_stmt(stmt: &mut HirStmt, pass: &mut impl HirRewritePass) -> bool {
    let nested_changed = match stmt {
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
    };

    pass.rewrite_stmt(stmt) || nested_changed
}

fn rewrite_lvalue(lvalue: &mut HirLValue, pass: &mut impl HirRewritePass) -> bool {
    let nested_changed = match lvalue {
        HirLValue::TableAccess(access) => {
            rewrite_expr(&mut access.base, pass) || rewrite_expr(&mut access.key, pass)
        }
        HirLValue::Temp(_) | HirLValue::Local(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => {
            false
        }
    };

    pass.rewrite_lvalue(lvalue) || nested_changed
}

fn rewrite_call_expr(call: &mut HirCallExpr, pass: &mut impl HirRewritePass) -> bool {
    let callee_changed = rewrite_expr(&mut call.callee, pass);
    let args_changed = call
        .args
        .iter_mut()
        .fold(false, |changed, arg| rewrite_expr(arg, pass) || changed);
    pass.rewrite_call(call) || callee_changed || args_changed
}

fn rewrite_expr(expr: &mut HirExpr, pass: &mut impl HirRewritePass) -> bool {
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
        HirExpr::Closure(closure) => closure.captures.iter_mut().fold(false, |changed, capture| {
            rewrite_expr(&mut capture.value, pass) || changed
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

fn rewrite_condition_expr(expr: &mut HirExpr, pass: &mut impl HirRewritePass) -> bool {
    let nested_changed = rewrite_expr(expr, pass);
    pass.rewrite_condition_expr(expr) || nested_changed
}

fn rewrite_decision_expr(decision: &mut HirDecisionExpr, pass: &mut impl HirRewritePass) -> bool {
    decision.nodes.iter_mut().fold(false, |changed, node| {
        let test_changed = rewrite_condition_expr(&mut node.test, pass);
        let truthy_changed = rewrite_decision_target(&mut node.truthy, pass);
        let falsy_changed = rewrite_decision_target(&mut node.falsy, pass);
        changed || test_changed || truthy_changed || falsy_changed
    })
}

fn rewrite_decision_target(target: &mut HirDecisionTarget, pass: &mut impl HirRewritePass) -> bool {
    match target {
        HirDecisionTarget::Expr(expr) => rewrite_expr(expr, pass),
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
    }
}

fn rewrite_table_constructor(
    table: &mut HirTableConstructor,
    pass: &mut impl HirRewritePass,
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
