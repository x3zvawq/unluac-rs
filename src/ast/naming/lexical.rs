//! 从最终 AST 发布闭包定义点与 binding 可见区间。
//!
//! 消费当前声明和词法作用域，供 Naming 关联最终名字；不复用已经过时的 HIR 块树。

use std::ops::Range;

use crate::ast::traverse::{traverse_call_children, traverse_lvalue_children};
use crate::ast::visit::{ExprNode, expr_nodes};
use crate::ast::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstLocalDecl,
    AstModule, AstStmt, AstSyntheticLocalId,
};
use crate::hir::{HirModule, HirProtoRef, LocalId, ParamId, UpvalueId};

/// 按函数记录最终 AST 定义点与本函数声明的可见区间。
#[derive(Debug, Clone, Default)]
pub(crate) struct LexicalContexts {
    pub(crate) functions: Vec<FunctionLexicalContext>,
    next_definition_position: usize,
}

impl LexicalContexts {
    pub(crate) fn function(&self, function: HirProtoRef) -> Option<&FunctionLexicalContext> {
        self.functions.get(function.index())
    }
}

/// 单个函数的词法上下文。
#[derive(Debug, Clone, Default)]
pub(crate) struct FunctionLexicalContext {
    pub(crate) definition_position: usize,
    pub(crate) visible_bindings: Vec<(VisibleBinding, Range<usize>)>,
}

/// 声明函数持有的 binding 身份；可见区间只覆盖后续子孙 closure 定义点。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub(crate) enum VisibleBinding {
    Param {
        function: HirProtoRef,
        param: ParamId,
    },
    Local {
        function: HirProtoRef,
        local: LocalId,
    },
    SyntheticLocal {
        function: HirProtoRef,
        local: AstSyntheticLocalId,
    },
    Upvalue {
        function: HirProtoRef,
        upvalue: UpvalueId,
    },
}

/// 从已通过 Naming 入口身份校验的 AST 推导最终词法上下文。
pub(super) fn collect_lexical_contexts(module: &AstModule, hir: &HirModule) -> LexicalContexts {
    let mut contexts = LexicalContexts {
        functions: vec![FunctionLexicalContext::default(); hir.protos.len()],
        next_definition_position: 0,
    };
    collect_function_context(module.entry_function, &module.body, hir, &mut contexts);
    contexts
}

fn collect_function_context(
    function: HirProtoRef,
    body: &AstBlock,
    hir: &HirModule,
    contexts: &mut LexicalContexts,
) {
    let proto = &hir.protos[function.index()];
    contexts.functions[function.index()] = FunctionLexicalContext {
        definition_position: contexts.next_definition_position,
        visible_bindings: Vec::new(),
    };
    contexts.next_definition_position += 1;

    let mut scopes = vec![Vec::new()];
    for &param in &proto.params {
        declare_binding(
            &mut scopes,
            VisibleBinding::Param { function, param },
            contexts.next_definition_position,
        );
    }
    if let Some(local) = proto.vararg_param_local {
        declare_binding(
            &mut scopes,
            VisibleBinding::Local { function, local },
            contexts.next_definition_position,
        );
    }
    for &upvalue in &proto.upvalues {
        declare_binding(
            &mut scopes,
            VisibleBinding::Upvalue { function, upvalue },
            contexts.next_definition_position,
        );
    }

    collect_block_context(function, body, hir, contexts, &mut scopes);
    close_scope(function, contexts, &mut scopes);
}

fn collect_block_context(
    function: HirProtoRef,
    block: &AstBlock,
    hir: &HirModule,
    contexts: &mut LexicalContexts,
    scopes: &mut PendingScopes,
) {
    for stmt in &block.stmts {
        collect_stmt_context(function, stmt, hir, contexts, scopes);
    }
}

fn collect_stmt_context(
    function: HirProtoRef,
    stmt: &AstStmt,
    hir: &HirModule,
    contexts: &mut LexicalContexts,
    scopes: &mut PendingScopes,
) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            collect_local_decl_context(function, local_decl, hir, contexts, scopes);
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_expr_context(value, hir, contexts);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_context(target, hir, contexts);
            }
            for value in &assign.values {
                collect_expr_context(value, hir, contexts);
            }
        }
        AstStmt::CallStmt(call_stmt) => {
            collect_call_context(&call_stmt.call, hir, contexts);
        }
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_context(value, hir, contexts);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_expr_context(&if_stmt.cond, hir, contexts);
            with_nested_scope(function, contexts, scopes, |contexts, scopes| {
                collect_block_context(function, &if_stmt.then_block, hir, contexts, scopes)
            });
            if let Some(else_block) = &if_stmt.else_block {
                with_nested_scope(function, contexts, scopes, |contexts, scopes| {
                    collect_block_context(function, else_block, hir, contexts, scopes)
                });
            }
        }
        AstStmt::While(while_stmt) => {
            collect_expr_context(&while_stmt.cond, hir, contexts);
            with_nested_scope(function, contexts, scopes, |contexts, scopes| {
                collect_block_context(function, &while_stmt.body, hir, contexts, scopes)
            });
        }
        AstStmt::Repeat(repeat_stmt) => {
            // `repeat ... until cond` 的条件仍处在同一个词法块里。
            // 这里不能像 while 一样先跑 body 再弹 scope，否则会丢掉 body 中局部对 cond 的可见性。
            with_nested_scope(function, contexts, scopes, |contexts, scopes| {
                collect_block_context(function, &repeat_stmt.body, hir, contexts, scopes);
                collect_expr_context(&repeat_stmt.cond, hir, contexts)
            });
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_expr_context(&numeric_for.start, hir, contexts);
            collect_expr_context(&numeric_for.limit, hir, contexts);
            collect_expr_context(&numeric_for.step, hir, contexts);
            with_nested_scope(function, contexts, scopes, |contexts, scopes| {
                declare_ast_binding(
                    function,
                    numeric_for.binding,
                    scopes,
                    contexts.next_definition_position,
                );
                collect_block_context(function, &numeric_for.body, hir, contexts, scopes)
            });
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_expr_context(expr, hir, contexts);
            }
            with_nested_scope(function, contexts, scopes, |contexts, scopes| {
                for &binding in &generic_for.bindings {
                    declare_ast_binding(
                        function,
                        binding,
                        scopes,
                        contexts.next_definition_position,
                    );
                }
                collect_block_context(function, &generic_for.body, hir, contexts, scopes)
            });
        }
        AstStmt::DoBlock(block) => {
            with_nested_scope(function, contexts, scopes, |contexts, scopes| {
                collect_block_context(function, block, hir, contexts, scopes)
            });
        }
        AstStmt::FunctionDecl(function_decl) => {
            collect_nested_function_context(&function_decl.func, hir, contexts);
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            // `local function f() ... end` 里的 `f` 在函数体内也是可见的，
            // 所以要先把它放进当前作用域，再收集子函数的词法上下文。
            declare_ast_binding(
                function,
                local_function_decl.name,
                scopes,
                contexts.next_definition_position,
            );
            collect_nested_function_context(&local_function_decl.func, hir, contexts);
        }
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => {}
    }
}

fn collect_local_decl_context(
    function: HirProtoRef,
    local_decl: &AstLocalDecl,
    hir: &HirModule,
    contexts: &mut LexicalContexts,
    scopes: &mut PendingScopes,
) {
    for value in &local_decl.values {
        collect_expr_context(value, hir, contexts);
    }
    for binding in &local_decl.bindings {
        declare_ast_binding(
            function,
            binding.id,
            scopes,
            contexts.next_definition_position,
        );
    }
}

fn collect_nested_function_context(
    function_expr: &AstFunctionExpr,
    hir: &HirModule,
    contexts: &mut LexicalContexts,
) {
    collect_function_context(function_expr.function, &function_expr.body, hir, contexts)
}

fn collect_call_context(call: &AstCallKind, hir: &HirModule, contexts: &mut LexicalContexts) {
    traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        collect_expr_context(expr, hir, contexts);
    });
}

fn collect_lvalue_context(target: &AstLValue, hir: &HirModule, contexts: &mut LexicalContexts) {
    traverse_lvalue_children!(target, borrow = [&], expr(expr) => {
        collect_expr_context(expr, hir, contexts);
    });
}

fn collect_expr_context(expr: &AstExpr, hir: &HirModule, contexts: &mut LexicalContexts) {
    for node in expr_nodes(expr) {
        if let ExprNode::Function(func) = node {
            collect_nested_function_context(func, hir, contexts);
        }
    }
}

fn declare_ast_binding(
    function: HirProtoRef,
    binding: AstBindingRef,
    scopes: &mut [Vec<(VisibleBinding, usize)>],
    start: usize,
) {
    match binding {
        AstBindingRef::Local(local) => {
            declare_binding(scopes, VisibleBinding::Local { function, local }, start);
        }
        AstBindingRef::SyntheticLocal(local) => {
            declare_binding(
                scopes,
                VisibleBinding::SyntheticLocal { function, local },
                start,
            );
        }
        AstBindingRef::Temp(_) => unreachable!(
            "readability output must not leak raw temp bindings into naming lexical analysis"
        ),
    }
}

/// 每个活动 scope 只保留自己尚未闭合的声明，离域时一次性发布区间。
type PendingScopes = Vec<Vec<(VisibleBinding, usize)>>;

fn declare_binding(
    scopes: &mut [Vec<(VisibleBinding, usize)>],
    binding: VisibleBinding,
    start: usize,
) {
    scopes
        .last_mut()
        .expect("lexical context must always keep at least one scope")
        .push((binding, start));
}

fn close_scope(function: HirProtoRef, contexts: &mut LexicalContexts, scopes: &mut PendingScopes) {
    let end = contexts.next_definition_position;
    let scope = scopes
        .pop()
        .expect("lexical scope must exist before closing");
    contexts.functions[function.index()]
        .visible_bindings
        .extend(
            scope
                .into_iter()
                .map(|(binding, start)| (binding, start..end)),
        );
}

fn with_nested_scope(
    function: HirProtoRef,
    contexts: &mut LexicalContexts,
    scopes: &mut PendingScopes,
    f: impl FnOnce(&mut LexicalContexts, &mut PendingScopes),
) {
    scopes.push(Vec::new());
    f(contexts, scopes);
    close_scope(function, contexts, scopes);
}
