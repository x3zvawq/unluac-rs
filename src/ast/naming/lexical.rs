//! 从最终 AST 发布闭包定义点与 binding 可见区间。
//!
//! 消费当前声明和词法作用域，供 Naming 关联最终名字。

use std::ops::Range;

use crate::ast::traverse::{traverse_call_children, traverse_lvalue_children};
use crate::ast::visit::{ExprNode, expr_nodes};
use crate::ast::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstLocalDecl,
    AstModule, AstStmt, AstSyntheticLocalId, LocalId, ParamId, ProtoId, UpvalueId,
};

/// 按函数记录最终 AST 定义点与本函数声明的可见区间。
#[derive(Debug, Clone, Default)]
pub(crate) struct LexicalContexts {
    pub(crate) functions: Vec<FunctionLexicalContext>,
    next_definition_position: usize,
}

impl LexicalContexts {
    pub(crate) fn function(&self, function: ProtoId) -> Option<&FunctionLexicalContext> {
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
        function: ProtoId,
        param: ParamId,
    },
    Local {
        function: ProtoId,
        local: LocalId,
    },
    SyntheticLocal {
        function: ProtoId,
        local: AstSyntheticLocalId,
    },
    Upvalue {
        function: ProtoId,
        upvalue: UpvalueId,
    },
}

/// 从已通过 Naming 入口身份校验的 AST 推导最终词法上下文。
pub(super) fn collect_lexical_contexts(module: &AstModule) -> LexicalContexts {
    let mut contexts = LexicalContexts {
        functions: vec![FunctionLexicalContext::default(); module.protos.len()],
        next_definition_position: 0,
    };
    collect_function_context(module.entry_function, &module.body, module, &mut contexts);
    contexts
}

fn collect_function_context(
    function: ProtoId,
    body: &AstBlock,
    module: &AstModule,
    contexts: &mut LexicalContexts,
) {
    let proto = &module.protos[function.index()];
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

    collect_block_context(function, body, module, contexts, &mut scopes);
    close_scope(function, contexts, &mut scopes);
}

fn collect_block_context(
    function: ProtoId,
    block: &AstBlock,
    module: &AstModule,
    contexts: &mut LexicalContexts,
    scopes: &mut PendingScopes,
) {
    for stmt in &block.stmts {
        collect_stmt_context(function, stmt, module, contexts, scopes);
    }
}

fn collect_stmt_context(
    function: ProtoId,
    stmt: &AstStmt,
    module: &AstModule,
    contexts: &mut LexicalContexts,
    scopes: &mut PendingScopes,
) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            collect_local_decl_context(function, local_decl, module, contexts, scopes);
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_expr_context(value, module, contexts);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_context(target, module, contexts);
            }
            for value in &assign.values {
                collect_expr_context(value, module, contexts);
            }
        }
        AstStmt::CallStmt(call_stmt) => {
            collect_call_context(&call_stmt.call, module, contexts);
        }
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_context(value, module, contexts);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_expr_context(&if_stmt.cond, module, contexts);
            with_nested_scope(function, contexts, scopes, |contexts, scopes| {
                collect_block_context(function, &if_stmt.then_block, module, contexts, scopes)
            });
            if let Some(else_block) = &if_stmt.else_block {
                with_nested_scope(function, contexts, scopes, |contexts, scopes| {
                    collect_block_context(function, else_block, module, contexts, scopes)
                });
            }
        }
        AstStmt::While(while_stmt) => {
            collect_expr_context(&while_stmt.cond, module, contexts);
            with_nested_scope(function, contexts, scopes, |contexts, scopes| {
                collect_block_context(function, &while_stmt.body, module, contexts, scopes)
            });
        }
        AstStmt::Repeat(repeat_stmt) => {
            // `repeat ... until cond` 的条件仍处在同一个词法块里。
            with_nested_scope(function, contexts, scopes, |contexts, scopes| {
                collect_block_context(function, &repeat_stmt.body, module, contexts, scopes);
                collect_expr_context(&repeat_stmt.cond, module, contexts)
            });
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_expr_context(&numeric_for.start, module, contexts);
            collect_expr_context(&numeric_for.limit, module, contexts);
            collect_expr_context(&numeric_for.step, module, contexts);
            with_nested_scope(function, contexts, scopes, |contexts, scopes| {
                declare_ast_binding(
                    function,
                    numeric_for.binding,
                    scopes,
                    contexts.next_definition_position,
                );
                collect_block_context(function, &numeric_for.body, module, contexts, scopes)
            });
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_expr_context(expr, module, contexts);
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
                collect_block_context(function, &generic_for.body, module, contexts, scopes)
            });
        }
        AstStmt::DoBlock(block) => {
            with_nested_scope(function, contexts, scopes, |contexts, scopes| {
                collect_block_context(function, block, module, contexts, scopes)
            });
        }
        AstStmt::FunctionDecl(function_decl) => {
            collect_nested_function_context(&function_decl.func, module, contexts);
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            declare_ast_binding(
                function,
                local_function_decl.name,
                scopes,
                contexts.next_definition_position,
            );
            collect_nested_function_context(&local_function_decl.func, module, contexts);
        }
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => {}
    }
}

fn collect_local_decl_context(
    function: ProtoId,
    local_decl: &AstLocalDecl,
    module: &AstModule,
    contexts: &mut LexicalContexts,
    scopes: &mut PendingScopes,
) {
    for value in &local_decl.values {
        collect_expr_context(value, module, contexts);
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
    module: &AstModule,
    contexts: &mut LexicalContexts,
) {
    collect_function_context(function_expr.function, &function_expr.body, module, contexts)
}

fn collect_call_context(call: &AstCallKind, module: &AstModule, contexts: &mut LexicalContexts) {
    traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        collect_expr_context(expr, module, contexts);
    });
}

fn collect_lvalue_context(target: &AstLValue, module: &AstModule, contexts: &mut LexicalContexts) {
    traverse_lvalue_children!(target, borrow = [&], expr(expr) => {
        collect_expr_context(expr, module, contexts);
    });
}

fn collect_expr_context(expr: &AstExpr, module: &AstModule, contexts: &mut LexicalContexts) {
    for node in expr_nodes(expr) {
        if let ExprNode::Function(func) = node {
            collect_nested_function_context(func, module, contexts);
        }
    }
}

fn declare_ast_binding(
    function: ProtoId,
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

fn close_scope(function: ProtoId, contexts: &mut LexicalContexts, scopes: &mut PendingScopes) {
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
    function: ProtoId,
    contexts: &mut LexicalContexts,
    scopes: &mut PendingScopes,
    f: impl FnOnce(&mut LexicalContexts, &mut PendingScopes),
) {
    scopes.push(Vec::new());
    f(contexts, scopes);
    close_scope(function, contexts, scopes);
}
