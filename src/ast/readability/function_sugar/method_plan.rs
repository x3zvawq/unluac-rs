//! method alias 的当前 AST 候选证明与单点提交。
//!
//! owner 查询和正式改写共用借用计划，只有提交才复制 AST。这里证明当前 sink 的求值位置、
//! 首匹配路径及前缀稳定性；binding 删除与 VM 根生命周期仍由 method_alias 消费已有事实。
//! 例如 `local r=source; sink(r.m(r))` 保存 sink 中首参数的路径，许可后一次提交为
//! `sink(source:m())`；`effect() + r.m(r)` 的不稳定前缀则使整次候选拒绝。
//! 路径和替换物借用同一不可变快照，不跨 Normal/Deferred 阶段或其他 AST 改写缓存。

use std::ops::ControlFlow;

use super::super::binding_flow::MutableSnapshotNames;
use super::super::expr_analysis::is_stable_context_expr;
use crate::ast::common::{
    AstCallExpr, AstCallKind, AstCallStmt, AstExpr, AstMethodCallExpr, AstStmt,
};
use crate::ast::traverse::{traverse_call_children, traverse_expr_children};

pub(super) struct MethodCallParts<'a> {
    pub receiver: &'a AstExpr,
    pub method: &'a str,
    pub args: &'a [AstExpr],
}

pub(super) struct MethodSinkPlan<'a> {
    stmt: &'a AstStmt,
    path: Vec<usize>,
    replacement: MethodCallParts<'a>,
}

impl<'a> MethodSinkPlan<'a> {
    pub(super) fn find(
        stmt: &'a AstStmt,
        repeatable: bool,
        cross_allocation: bool,
        names: &MutableSnapshotNames,
        match_call: impl Fn(&'a AstCallExpr) -> Option<MethodCallParts<'a>>,
    ) -> Option<Self> {
        let root = MethodRoot::for_sink(stmt, repeatable)?;
        let mut current = root;
        let mut path = Vec::new();
        let mut pending = Vec::new();
        let replacement = loop {
            if let Some(call) = current.call()
                && let Some(replacement) = match_call(call)
            {
                break replacement;
            }
            let start = pending.len();
            let mut ordinal = 0;
            let _ = current.visit_children(|child| {
                pending.push((child, path.len(), ordinal));
                ordinal += 1;
                ControlFlow::Continue(())
            });
            pending[start..].reverse();
            let (child, depth, ordinal) = pending.pop()?;
            path.truncate(depth);
            path.push(ordinal);
            current = MethodRoot::Expr(child);
        };
        // 首次匹配决定唯一候选；祖先路径失败不能改选后面的调用。
        current = root;
        for &ordinal in &path {
            current = current.permitted_child(ordinal, names, cross_allocation)?;
        }
        Some(Self {
            stmt,
            path,
            replacement,
        })
    }

    pub(super) fn apply(self) -> AstStmt {
        let method = Box::new(AstMethodCallExpr {
            receiver: self.replacement.receiver.clone(),
            method: self.replacement.method.to_owned(),
            args: self.replacement.args.to_vec(),
        });
        if matches!(self.stmt, AstStmt::CallStmt(_)) && self.path.is_empty() {
            return AstStmt::CallStmt(Box::new(AstCallStmt {
                call: AstCallKind::MethodCall(method),
            }));
        }
        let mut rewritten = self.stmt.clone();
        let (mut current, path) = match &mut rewritten {
            AstStmt::CallStmt(stmt) => (
                call_child_mut(&mut stmt.call, self.path[0]),
                &self.path[1..],
            ),
            stmt => (sink_expr_mut(stmt), self.path.as_slice()),
        };
        for &ordinal in path {
            current = expr_child_mut(current, ordinal);
        }
        *current = AstExpr::MethodCall(method);
        rewritten
    }
}

/// CallStmt 保留原 CallKind 身份，不为只读查询克隆一个 AstExpr 包装。
#[derive(Clone, Copy)]
enum MethodRoot<'a> {
    Expr(&'a AstExpr),
    Call(&'a AstCallKind),
}

impl<'a> MethodRoot<'a> {
    fn for_sink(stmt: &'a AstStmt, repeatable: bool) -> Option<Self> {
        let expr = match stmt {
            AstStmt::LocalDecl(stmt) => stmt.values.first()?,
            AstStmt::GlobalDecl(stmt) => stmt.values.first()?,
            AstStmt::Return(stmt) => stmt.values.first()?,
            AstStmt::Assign(stmt) => {
                // 候选拒绝[SemanticBarrier:EvalOrder]：复杂 lvalue 在 RHS 前求值。
                if stmt
                    .targets
                    .iter()
                    .any(|target| !matches!(target, crate::ast::common::AstLValue::Name(_)))
                {
                    return None;
                }
                stmt.values.first()?
            }
            AstStmt::If(stmt) => &stmt.cond,
            AstStmt::NumericFor(stmt) => &stmt.start,
            AstStmt::GenericFor(stmt) => stmt.iterator.first()?,
            AstStmt::CallStmt(stmt) => return Some(Self::Call(&stmt.call)),
            AstStmt::While(stmt) if repeatable => &stmt.cond,
            AstStmt::Repeat(stmt) if repeatable => &stmt.cond,
            // 候选拒绝[SemanticBarrier:EvalCount]：非稳定 initializer 不能变成逐轮求值。
            _ => return None,
        };
        // 首 RHS/iterator 原位置保留其单值/open-tail 边界；condition/start 始终为标量。
        Some(Self::Expr(expr))
    }

    fn call(self) -> Option<&'a AstCallExpr> {
        match self {
            Self::Expr(AstExpr::Call(call)) | Self::Call(AstCallKind::Call(call)) => Some(call),
            _ => None,
        }
    }

    fn visit_children(
        self,
        mut visit: impl FnMut(&'a AstExpr) -> ControlFlow<()>,
    ) -> ControlFlow<()> {
        match self {
            Self::Expr(expr) => {
                traverse_expr_children!(expr, iter = iter, borrow = [&],
                    expr(child) => { visit(child)?; }, function(_function) => {}
                );
            }
            Self::Call(call) => {
                traverse_call_children!(call, iter = iter, borrow = [&],
                    expr(child) => { visit(child)?; }
                );
            }
        }
        ControlFlow::Continue(())
    }

    fn permitted_child(
        self,
        selected: usize,
        names: &MutableSnapshotNames,
        cross_allocation: bool,
    ) -> Option<Self> {
        match self {
            // 候选拒绝[SemanticBarrier:ControlFlow]：短路 rhs 不能接收无条件 initializer。
            Self::Expr(AstExpr::LogicalAnd(_) | AstExpr::LogicalOr(_)) if selected != 0 => {
                return None;
            }
            // 候选拒绝[SemanticBarrier:EvalOrder]：method args 已越过 receiver 字段查询。
            Self::Expr(AstExpr::MethodCall(_)) | Self::Call(AstCallKind::MethodCall(_))
                if selected != 0 =>
            {
                return None;
            }
            Self::Expr(AstExpr::TableConstructor(_)) if !cross_allocation => return None,
            _ => {}
        }
        let mut result = None;
        let mut ordinal = 0;
        let _ = self.visit_children(|child| {
            if ordinal == selected {
                result = Some(Self::Expr(child));
                return ControlFlow::Break(());
            }
            // 各层前缀子树互不相交，继续消费共享稳定性查询，不重扫目标子树。
            if !is_stable_context_expr(child, names) {
                return ControlFlow::Break(());
            }
            ordinal += 1;
            ControlFlow::Continue(())
        });
        result
    }
}

fn sink_expr_mut(stmt: &mut AstStmt) -> &mut AstExpr {
    match stmt {
        AstStmt::LocalDecl(stmt) => &mut stmt.values[0],
        AstStmt::GlobalDecl(stmt) => &mut stmt.values[0],
        AstStmt::Return(stmt) => &mut stmt.values[0],
        AstStmt::Assign(stmt) => &mut stmt.values[0],
        AstStmt::If(stmt) => &mut stmt.cond,
        AstStmt::NumericFor(stmt) => &mut stmt.start,
        AstStmt::GenericFor(stmt) => &mut stmt.iterator[0],
        AstStmt::While(stmt) => &mut stmt.cond,
        AstStmt::Repeat(stmt) => &mut stmt.cond,
        _ => unreachable!("method plan retains its original sink"),
    }
}

fn expr_child_mut(expr: &mut AstExpr, selected: usize) -> &mut AstExpr {
    let mut ordinal = 0;
    traverse_expr_children!(expr, iter = iter_mut, borrow = [&mut],
        expr(child) => {
            if ordinal == selected { return child; }
            ordinal += 1;
        }, function(_function) => {}
    );
    let _ = ordinal;
    unreachable!("method plan retains its original expression path")
}

fn call_child_mut(call: &mut AstCallKind, selected: usize) -> &mut AstExpr {
    let mut ordinal = 0;
    traverse_call_children!(call, iter = iter_mut, borrow = [&mut],
        expr(child) => {
            if ordinal == selected { return child; }
            ordinal += 1;
        }
    );
    let _ = ordinal;
    unreachable!("method plan retains its original call path")
}
