//! 这个文件负责从 AST 重建 Naming 需要的词法可见域信息。
//!
//! Naming 不能假定前层已经单独导出 scope facts，所以这里显式记录：
//! “某个函数在定义点到底能看到哪些外层绑定”。这样后续参数命名就能避开
//! 祖先作用域里当前可见的自动生成名字，而不是退化成全局禁名或拍脑袋加后缀。

use crate::ast::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue,
    AstLocalDecl, AstModule, AstStmt, AstSyntheticLocalId,
};
use crate::ast::traverse::{
    traverse_call_children, traverse_expr_children, traverse_lvalue_children,
};
use crate::hir::{HirModule, HirProtoRef, LocalId, ParamId, UpvalueId};

use super::NamingError;

/// 按函数记录其定义点能看到的外层绑定。
#[derive(Debug, Clone, Default)]
pub(crate) struct LexicalContexts {
    pub(crate) functions: Vec<FunctionLexicalContext>,
}

impl LexicalContexts {
    pub(crate) fn function(&self, function: HirProtoRef) -> Option<&FunctionLexicalContext> {
        self.functions.get(function.index())
    }
}

/// 单个函数的词法上下文。
#[derive(Debug, Clone, Default)]
pub(crate) struct FunctionLexicalContext {
    pub(crate) outer_visible_bindings: Vec<VisibleBinding>,
}

/// 在函数定义点可见的外层绑定。
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

/// 从 AST 结构推导词法上下文。
pub(crate) fn collect_lexical_contexts(
    module: &AstModule,
    hir: &HirModule,
) -> Result<LexicalContexts, NamingError> {
    let mut contexts = LexicalContexts {
        functions: vec![FunctionLexicalContext::default(); hir.protos.len()],
    };
    collect_function_context(module.entry_function, &module.body, hir, &mut contexts, &[])?;
    Ok(contexts)
}

fn collect_function_context(
    function: HirProtoRef,
    body: &AstBlock,
    hir: &HirModule,
    contexts: &mut LexicalContexts,
    outer_visible_bindings: &[VisibleBinding],
) -> Result<(), NamingError> {
    let Some(proto) = hir.protos.get(function.index()) else {
        return Err(NamingError::MissingFunction {
            function: function.index(),
        });
    };
    contexts.functions[function.index()].outer_visible_bindings = outer_visible_bindings.to_vec();

    let mut scopes = vec![Vec::new()];
    for &param in &proto.params {
        declare_binding(&mut scopes, VisibleBinding::Param { function, param });
    }
    if proto.signature.has_vararg_param_reg
        && let Some(&local) = proto.locals.first()
    {
        declare_binding(&mut scopes, VisibleBinding::Local { function, local });
    }
    for &upvalue in &proto.upvalues {
        declare_binding(&mut scopes, VisibleBinding::Upvalue { function, upvalue });
    }

    collect_block_context(
        function,
        body,
        hir,
        contexts,
        outer_visible_bindings,
        &mut scopes,
    )
}

fn collect_block_context(
    function: HirProtoRef,
    block: &AstBlock,
    hir: &HirModule,
    contexts: &mut LexicalContexts,
    outer_visible_bindings: &[VisibleBinding],
    scopes: &mut Vec<Vec<VisibleBinding>>,
) -> Result<(), NamingError> {
    for stmt in &block.stmts {
        collect_stmt_context(
            function,
            stmt,
            hir,
            contexts,
            outer_visible_bindings,
            scopes,
        )?;
    }
    Ok(())
}

fn collect_stmt_context(
    function: HirProtoRef,
    stmt: &AstStmt,
    hir: &HirModule,
    contexts: &mut LexicalContexts,
    outer_visible_bindings: &[VisibleBinding],
    scopes: &mut Vec<Vec<VisibleBinding>>,
) -> Result<(), NamingError> {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            collect_local_decl_context(
                function,
                local_decl,
                hir,
                contexts,
                outer_visible_bindings,
                scopes,
            )?;
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_expr_context(value, hir, contexts, outer_visible_bindings, scopes)?;
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_context(target, hir, contexts, outer_visible_bindings, scopes)?;
            }
            for value in &assign.values {
                collect_expr_context(value, hir, contexts, outer_visible_bindings, scopes)?;
            }
        }
        AstStmt::CallStmt(call_stmt) => {
            collect_call_context(
                &call_stmt.call,
                hir,
                contexts,
                outer_visible_bindings,
                scopes,
            )?;
        }
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_context(value, hir, contexts, outer_visible_bindings, scopes)?;
            }
        }
        AstStmt::If(if_stmt) => {
            collect_expr_context(&if_stmt.cond, hir, contexts, outer_visible_bindings, scopes)?;
            with_nested_scope(scopes, |scopes| {
                collect_block_context(
                    function,
                    &if_stmt.then_block,
                    hir,
                    contexts,
                    outer_visible_bindings,
                    scopes,
                )
            })?;
            if let Some(else_block) = &if_stmt.else_block {
                with_nested_scope(scopes, |scopes| {
                    collect_block_context(
                        function,
                        else_block,
                        hir,
                        contexts,
                        outer_visible_bindings,
                        scopes,
                    )
                })?;
            }
        }
        AstStmt::While(while_stmt) => {
            collect_expr_context(
                &while_stmt.cond,
                hir,
                contexts,
                outer_visible_bindings,
                scopes,
            )?;
            with_nested_scope(scopes, |scopes| {
                collect_block_context(
                    function,
                    &while_stmt.body,
                    hir,
                    contexts,
                    outer_visible_bindings,
                    scopes,
                )
            })?;
        }
        AstStmt::Repeat(repeat_stmt) => {
            // `repeat ... until cond` 的条件仍处在同一个词法块里。
            // 这里不能像 while 一样先跑 body 再弹 scope，否则会丢掉 body 中局部对 cond 的可见性。
            with_nested_scope(scopes, |scopes| {
                collect_block_context(
                    function,
                    &repeat_stmt.body,
                    hir,
                    contexts,
                    outer_visible_bindings,
                    scopes,
                )?;
                collect_expr_context(
                    &repeat_stmt.cond,
                    hir,
                    contexts,
                    outer_visible_bindings,
                    scopes,
                )
            })?;
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_expr_context(
                &numeric_for.start,
                hir,
                contexts,
                outer_visible_bindings,
                scopes,
            )?;
            collect_expr_context(
                &numeric_for.limit,
                hir,
                contexts,
                outer_visible_bindings,
                scopes,
            )?;
            collect_expr_context(
                &numeric_for.step,
                hir,
                contexts,
                outer_visible_bindings,
                scopes,
            )?;
            with_nested_scope(scopes, |scopes| {
                declare_ast_binding(function, numeric_for.binding, scopes);
                collect_block_context(
                    function,
                    &numeric_for.body,
                    hir,
                    contexts,
                    outer_visible_bindings,
                    scopes,
                )
            })?;
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_expr_context(expr, hir, contexts, outer_visible_bindings, scopes)?;
            }
            with_nested_scope(scopes, |scopes| {
                for &binding in &generic_for.bindings {
                    declare_ast_binding(function, binding, scopes);
                }
                collect_block_context(
                    function,
                    &generic_for.body,
                    hir,
                    contexts,
                    outer_visible_bindings,
                    scopes,
                )
            })?;
        }
        AstStmt::DoBlock(block) => {
            with_nested_scope(scopes, |scopes| {
                collect_block_context(
                    function,
                    block,
                    hir,
                    contexts,
                    outer_visible_bindings,
                    scopes,
                )
            })?;
        }
        AstStmt::FunctionDecl(function_decl) => {
            collect_nested_function_context(
                &function_decl.func,
                hir,
                contexts,
                outer_visible_bindings,
                scopes,
            )?;
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            // `local function f() ... end` 里的 `f` 在函数体内也是可见的，
            // 所以要先把它放进当前作用域，再收集子函数的词法上下文。
            declare_ast_binding(function, local_function_decl.name, scopes);
            collect_nested_function_context(
                &local_function_decl.func,
                hir,
                contexts,
                outer_visible_bindings,
                scopes,
            )?;
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) | AstStmt::Error(_) => {}
    }
    Ok(())
}

fn collect_local_decl_context(
    function: HirProtoRef,
    local_decl: &AstLocalDecl,
    hir: &HirModule,
    contexts: &mut LexicalContexts,
    outer_visible_bindings: &[VisibleBinding],
    scopes: &mut Vec<Vec<VisibleBinding>>,
) -> Result<(), NamingError> {
    for value in &local_decl.values {
        collect_expr_context(value, hir, contexts, outer_visible_bindings, scopes)?;
    }
    for binding in &local_decl.bindings {
        declare_ast_binding(function, binding.id, scopes);
    }
    Ok(())
}

fn collect_nested_function_context(
    function_expr: &AstFunctionExpr,
    hir: &HirModule,
    contexts: &mut LexicalContexts,
    outer_visible_bindings: &[VisibleBinding],
    scopes: &[Vec<VisibleBinding>],
) -> Result<(), NamingError> {
    let child_outer_visible = visible_snapshot(outer_visible_bindings, scopes);
    collect_function_context(
        function_expr.function,
        &function_expr.body,
        hir,
        contexts,
        &child_outer_visible,
    )
}

fn collect_call_context(
    call: &AstCallKind,
    hir: &HirModule,
    contexts: &mut LexicalContexts,
    outer_visible_bindings: &[VisibleBinding],
    scopes: &mut Vec<Vec<VisibleBinding>>,
) -> Result<(), NamingError> {
    traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        collect_expr_context(expr, hir, contexts, outer_visible_bindings, scopes)?;
    });
    Ok(())
}

fn collect_lvalue_context(
    target: &AstLValue,
    hir: &HirModule,
    contexts: &mut LexicalContexts,
    outer_visible_bindings: &[VisibleBinding],
    scopes: &mut Vec<Vec<VisibleBinding>>,
) -> Result<(), NamingError> {
    traverse_lvalue_children!(target, borrow = [&], expr(expr) => {
        collect_expr_context(expr, hir, contexts, outer_visible_bindings, scopes)?;
    });
    Ok(())
}

fn collect_expr_context(
    expr: &AstExpr,
    hir: &HirModule,
    contexts: &mut LexicalContexts,
    outer_visible_bindings: &[VisibleBinding],
    scopes: &mut Vec<Vec<VisibleBinding>>,
) -> Result<(), NamingError> {
    traverse_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(child) => {
            collect_expr_context(child, hir, contexts, outer_visible_bindings, scopes)?;
        },
        function(func) => {
            collect_nested_function_context(func, hir, contexts, outer_visible_bindings, scopes)?;
        }
    );
    Ok(())
}

fn declare_ast_binding(
    function: HirProtoRef,
    binding: AstBindingRef,
    scopes: &mut [Vec<VisibleBinding>],
) {
    match binding {
        AstBindingRef::Local(local) => {
            declare_binding(scopes, VisibleBinding::Local { function, local });
        }
        AstBindingRef::SyntheticLocal(local) => {
            declare_binding(scopes, VisibleBinding::SyntheticLocal { function, local });
        }
        AstBindingRef::Temp(_) => unreachable!(
            "readability output must not leak raw temp bindings into naming lexical analysis"
        ),
    }
}

fn declare_binding(scopes: &mut [Vec<VisibleBinding>], binding: VisibleBinding) {
    scopes
        .last_mut()
        .expect("lexical context must always keep at least one scope")
        .push(binding);
}

fn visible_snapshot(
    outer_visible_bindings: &[VisibleBinding],
    scopes: &[Vec<VisibleBinding>],
) -> Vec<VisibleBinding> {
    let mut visible = Vec::with_capacity(
        outer_visible_bindings.len() + scopes.iter().map(Vec::len).sum::<usize>(),
    );
    visible.extend_from_slice(outer_visible_bindings);
    for scope in scopes {
        visible.extend_from_slice(scope);
    }
    visible
}

fn with_nested_scope<T, F>(scopes: &mut Vec<Vec<VisibleBinding>>, f: F) -> Result<T, NamingError>
where
    F: FnOnce(&mut Vec<Vec<VisibleBinding>>) -> Result<T, NamingError>,
{
    scopes.push(Vec::new());
    let result = f(scopes);
    let popped = scopes.pop();
    debug_assert!(popped.is_some(), "nested lexical scope should exist");
    result
}
