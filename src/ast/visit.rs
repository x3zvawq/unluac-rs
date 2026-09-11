//! 这个文件提供 AST 各消费者共享的只读 visitor。
//!
//! readability、方言特性和调试编号收集器经常只是想“遍历 AST 收集一批事实”，例如统计 method 名、
//! 扫描 temp、寻找 synthetic local。过去这些分析各自复制了一整套
//! `block/stmt/lvalue/call/expr` 递归骨架；这里把只读遍历收成共享设施，让分析代码
//! 更专注在“看到某个节点时记录什么”，而不是重复维护递归。需要保持词法边界的分析
//! 可以在 `visit_block` 返回 false，裁掉由 scoped walker 另行处理的子 block。
//! 本层只枚举当前 AST 与显式 capture 元数据，不提供 HIR/VM 语义或改写许可。
//! 名字事件保留读、写、局部声明与 capture 的角色，consumer 不再各自解释函数 target。
//! 例如 `function t.m() end` 读取 t，而 `function t() end` 写入 t；把赋值改成声明语法
//! 不得丢掉前者的基址读取。函数边界的 capture 事件来自显式元数据，不遍历 child 重建。
//! 名字回调可返回 Break 结束本次入口遍历；停止信号穿过子节点循环立即返回，已进入
//! statement/function 的 leave hook 仍成对执行，未进入的 child 不产生回调。
//! 只需跳转事实时使用 any_stmt_structure，跳过求值与 child function；例如外层声明
//! 能否移动只取决于本函数的 goto，闭包体中的同号 label 不属于这个查询域。
//! 表达式先序骨架使用显式栈，并向 naming 等借用节点的收集器开放同一事件流；
//! `a + a + ...` 保持左结合树，遍历不消耗与运算链长度成正比的调用栈。

use std::ops::ControlFlow;

use crate::ast::common::{
    AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue, AstNameRef,
    AstStmt,
};

use crate::ast::traverse::{
    BlockKind, traverse_call_children, traverse_expr_children, traverse_lvalue_children,
    traverse_stmt_children,
};

#[derive(Clone, Copy)]
pub(super) enum NameAccess {
    Read,
    Write,
    LocalDeclaration,
    LocalFunctionDeclaration,
    Capture,
}

/// 裸目标写入 binding，字段/方法目标先读取路径根；global gate 与名字事件共用此判定。
pub(super) fn function_target_name(target: &AstFunctionName) -> (&AstNameRef, NameAccess) {
    match target {
        AstFunctionName::Plain(path) if path.fields.is_empty() => (&path.root, NameAccess::Write),
        AstFunctionName::Plain(path) | AstFunctionName::Method(path, _) => {
            (&path.root, NameAccess::Read)
        }
    }
}

pub(super) trait AstVisitor {
    fn visit_name(&mut self, _name: &AstNameRef, _access: NameAccess) -> ControlFlow<()> {
        ControlFlow::Continue(())
    }

    fn visit_block(&mut self, _block: &AstBlock, _kind: BlockKind) -> bool {
        true
    }

    fn visit_stmt(&mut self, _stmt: &AstStmt) {}

    fn leave_stmt(&mut self, _stmt: &AstStmt) {}

    fn visit_expr(&mut self, _expr: &AstExpr) {}

    fn visit_lvalue(&mut self, _lvalue: &AstLValue) {}

    fn visit_call(&mut self, _call: &AstCallKind) {}

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        true
    }

    fn leave_function_expr(&mut self, _function: &AstFunctionExpr) {}

    fn visit_condition_expr(&mut self, _expr: &AstExpr) {}
}

pub(super) fn visit_block(block: &AstBlock, visitor: &mut impl AstVisitor) {
    let _ = visit_block_with_kind(block, BlockKind::Regular, visitor);
}

pub(super) fn visit_stmt(stmt: &AstStmt, visitor: &mut impl AstVisitor) {
    let _ = visit_stmt_impl(stmt, visitor);
}

pub(super) fn visit_expr(expr: &AstExpr, visitor: &mut impl AstVisitor) {
    let _ = visit_expr_impl(expr, visitor);
}

/// 当前函数语句骨架的先序查询；表达式、函数体和 capture 不含本域的 label/goto。
pub(super) fn any_stmt_structure(
    stmt: &AstStmt,
    predicate: &mut impl FnMut(&AstStmt) -> bool,
) -> bool {
    if predicate(stmt) {
        return true;
    }
    traverse_stmt_children!(
        stmt, iter = iter, opt = as_ref, borrow = [&],
        expr(_expr) => {},
        lvalue(_lvalue) => {},
        block(block) => {
            if block.stmts.iter().any(|stmt| any_stmt_structure(stmt, predicate)) {
                return true;
            }
        },
        function(_function) => {},
        condition(_condition) => {},
        call(_call) => {}
    );
    false
}

fn visit_block_with_kind(
    block: &AstBlock,
    kind: BlockKind,
    visitor: &mut impl AstVisitor,
) -> ControlFlow<()> {
    if visitor.visit_block(block, kind) {
        for stmt in &block.stmts {
            visit_stmt_impl(stmt, visitor)?;
        }
    }
    ControlFlow::Continue(())
}

fn visit_stmt_impl(stmt: &AstStmt, visitor: &mut impl AstVisitor) -> ControlFlow<()> {
    visitor.visit_stmt(stmt);
    // 短路只跳过后续节点，已进入 statement 的 leave hook 仍须执行。
    let result = (|| {
        match stmt {
            AstStmt::LocalDecl(decl) => {
                for binding in &decl.bindings {
                    visitor.visit_name(&binding.id.to_name_ref(), NameAccess::LocalDeclaration)?;
                }
            }
            AstStmt::NumericFor(stmt) => {
                visitor.visit_name(&stmt.binding.to_name_ref(), NameAccess::LocalDeclaration)?;
            }
            AstStmt::GenericFor(stmt) => {
                for binding in &stmt.bindings {
                    visitor.visit_name(&binding.to_name_ref(), NameAccess::LocalDeclaration)?;
                }
            }
            AstStmt::FunctionDecl(decl) => {
                let (name, access) = function_target_name(&decl.target);
                visitor.visit_name(name, access)?;
            }
            AstStmt::LocalFunctionDecl(decl) => {
                visitor.visit_name(
                    &decl.name.to_name_ref(),
                    NameAccess::LocalFunctionDeclaration,
                )?;
            }
            _ => {}
        }
        traverse_stmt_children!(
            stmt,
            iter = iter,
            opt = as_ref,
            borrow = [&],
            expr(expr) => { visit_expr_impl(expr, visitor)?; },
            lvalue(lvalue) => { visit_lvalue(lvalue, visitor)?; },
            block(block) => { visit_block_with_kind(block, BlockKind::Regular, visitor)?; },
            function(function) => { visit_function_expr(function, BlockKind::FunctionBody, visitor)?; },
            condition(condition) => { visit_condition_expr(condition, visitor)?; },
            call(call) => { visit_call(call, visitor)?; }
        );
        ControlFlow::Continue(())
    })();
    visitor.leave_stmt(stmt);
    result
}

fn visit_call(call: &AstCallKind, visitor: &mut impl AstVisitor) -> ControlFlow<()> {
    visitor.visit_call(call);
    traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        visit_expr_impl(expr, visitor)?;
    });
    ControlFlow::Continue(())
}

fn visit_lvalue(lvalue: &AstLValue, visitor: &mut impl AstVisitor) -> ControlFlow<()> {
    visitor.visit_lvalue(lvalue);
    if let AstLValue::Name(name) = lvalue {
        visitor.visit_name(name, NameAccess::Write)?;
    }
    traverse_lvalue_children!(lvalue, borrow = [&], expr(expr) => {
        visit_expr_impl(expr, visitor)?;
    });
    ControlFlow::Continue(())
}

fn visit_expr_impl(expr: &AstExpr, visitor: &mut impl AstVisitor) -> ControlFlow<()> {
    for node in expr_nodes(expr) {
        match node {
            ExprNode::Expr(expr) => {
                visitor.visit_expr(expr);
                if let AstExpr::Var(name) = expr {
                    visitor.visit_name(name, NameAccess::Read)?;
                }
            }
            ExprNode::Function(function) => {
                visit_function_expr(function, BlockKind::FunctionBody, visitor)?;
            }
        }
    }
    ControlFlow::Continue(())
}

#[derive(Clone, Copy)]
pub(super) enum ExprNode<'a> {
    Expr(&'a AstExpr),
    Function(&'a AstFunctionExpr),
}

/// 共享先序表达式骨架；函数边界交给消费者处理，不进入 child body 或解释 capture。
/// 左结合算术可以远深于 Lua 的语法嵌套限制，必须保持原树并使用显式栈。
pub(super) fn expr_nodes(expr: &AstExpr) -> impl Iterator<Item = ExprNode<'_>> {
    let mut current = Some(ExprNode::Expr(expr));
    let mut pending = Vec::new();
    std::iter::from_fn(move || {
        let node = current.take()?;
        let start = pending.len();
        if let ExprNode::Expr(expr) = node {
            traverse_expr_children!(
                expr, iter = iter, borrow = [&],
                expr(child) => { pending.push(ExprNode::Expr(child)); },
                function(child) => { pending.push(ExprNode::Function(child)); }
            );
        }
        pending[start..].reverse();
        current = pending.pop();
        Some(node)
    })
}

fn visit_condition_expr(expr: &AstExpr, visitor: &mut impl AstVisitor) -> ControlFlow<()> {
    visitor.visit_condition_expr(expr);
    visit_expr_impl(expr, visitor)
}

fn visit_function_expr(
    function: &AstFunctionExpr,
    kind: BlockKind,
    visitor: &mut impl AstVisitor,
) -> ControlFlow<()> {
    for binding in &function.captured_bindings {
        visitor.visit_name(&binding.to_name_ref(), NameAccess::Capture)?;
    }
    let result = if visitor.visit_function_expr(function) {
        visit_block_with_kind(&function.body, kind, visitor)
    } else {
        ControlFlow::Continue(())
    };
    visitor.leave_function_expr(function);
    result
}
