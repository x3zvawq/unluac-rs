//! 最终 AST 的 goto/label 词法作用域校验。
//!
//! Readability 可能移动或物化 local，因此只有在它收敛后，才能按最终源码形状判断
//! goto 是否跳进了新的 local（尤其是 `<close>`）作用域。每个函数独立建 block tree 与
//! 持久化 local-scope tree；label 只对同函数的同层/子 block 可见，且目标 local 集合
//! 必须是源 local 集合的子集。

use std::collections::BTreeMap;

use super::traverse::{traverse_call_children, traverse_expr_children, traverse_lvalue_children};
use super::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstLabelId,
    AstLocalAttr, AstModule, AstStmt,
};
use crate::generate::GenerateMode;

use super::AstLowerError;

#[derive(Debug, Clone, Copy)]
struct Site {
    block: usize,
    scope: usize,
}

#[derive(Debug, Clone, Copy)]
struct ScopeBinding {
    id: AstBindingRef,
    to_be_closed: bool,
}

#[derive(Debug, Clone, Copy)]
struct ScopeNode {
    parent: Option<usize>,
    binding: Option<ScopeBinding>,
}

struct FunctionVerifier {
    function: usize,
    block_parents: Vec<Option<usize>>,
    scopes: Vec<ScopeNode>,
    labels: BTreeMap<AstLabelId, Site>,
    gotos: Vec<(AstLabelId, Site)>,
}

pub(super) fn verify_or_diagnose(
    module: &mut AstModule,
    mode: GenerateMode,
) -> Result<(), AstLowerError> {
    let result = verify_function(module.entry_function.index(), &module.body);
    match (mode, result) {
        (_, Ok(())) => Ok(()),
        (GenerateMode::Strict, Err(error)) => Err(error),
        (GenerateMode::Permissive, Err(error)) => {
            module
                .body
                .stmts
                .insert(0, AstStmt::Error(error.to_string()));
            Ok(())
        }
    }
}

fn verify_function(function: usize, body: &AstBlock) -> Result<(), AstLowerError> {
    let mut verifier = FunctionVerifier {
        function,
        block_parents: Vec::new(),
        scopes: vec![ScopeNode {
            parent: None,
            binding: None,
        }],
        labels: BTreeMap::new(),
        gotos: Vec::new(),
    };
    verifier.visit_block(body, None, 0)?;
    verifier.finish()
}

impl FunctionVerifier {
    fn visit_block(
        &mut self,
        block: &AstBlock,
        parent: Option<usize>,
        entry_scope: usize,
    ) -> Result<(), AstLowerError> {
        let block_id = self.block_parents.len();
        self.block_parents.push(parent);
        let trailing_labels = block
            .stmts
            .iter()
            .rposition(|stmt| !matches!(stmt, AstStmt::Label(_) | AstStmt::Error(_)))
            .map_or(0, |index| index + 1);
        let mut scope = entry_scope;

        for (index, stmt) in block.stmts.iter().enumerate() {
            match stmt {
                AstStmt::LocalDecl(decl) => {
                    self.visit_exprs(&decl.values)?;
                    for binding in &decl.bindings {
                        scope =
                            self.push_scope(scope, binding.id, binding.attr == AstLocalAttr::Close);
                    }
                }
                AstStmt::GlobalDecl(decl) => self.visit_exprs(&decl.values)?,
                AstStmt::Assign(assign) => {
                    for target in &assign.targets {
                        self.visit_lvalue(target)?;
                    }
                    self.visit_exprs(&assign.values)?;
                }
                AstStmt::CallStmt(call) => self.visit_call(&call.call)?,
                AstStmt::Return(ret) => self.visit_exprs(&ret.values)?,
                AstStmt::If(branch) => {
                    self.visit_expr(&branch.cond)?;
                    self.visit_block(&branch.then_block, Some(block_id), scope)?;
                    if let Some(else_block) = &branch.else_block {
                        self.visit_block(else_block, Some(block_id), scope)?;
                    }
                }
                AstStmt::While(loop_) => {
                    self.visit_expr(&loop_.cond)?;
                    self.visit_block(&loop_.body, Some(block_id), scope)?;
                }
                AstStmt::Repeat(loop_) => {
                    self.visit_block(&loop_.body, Some(block_id), scope)?;
                    self.visit_expr(&loop_.cond)?;
                }
                AstStmt::NumericFor(loop_) => {
                    self.visit_expr(&loop_.start)?;
                    self.visit_expr(&loop_.limit)?;
                    self.visit_expr(&loop_.step)?;
                    let body_scope = self.push_scope(scope, loop_.binding, false);
                    self.visit_block(&loop_.body, Some(block_id), body_scope)?;
                }
                AstStmt::GenericFor(loop_) => {
                    self.visit_exprs(&loop_.iterator)?;
                    let mut body_scope = scope;
                    for binding in &loop_.bindings {
                        body_scope = self.push_scope(body_scope, *binding, false);
                    }
                    self.visit_block(&loop_.body, Some(block_id), body_scope)?;
                }
                AstStmt::Goto(goto_) => self.gotos.push((
                    goto_.target,
                    Site {
                        block: block_id,
                        scope,
                    },
                )),
                AstStmt::Label(label) => {
                    // Lua 把块末尾的 label 视为位于本 block 新增 local 的作用域之外；
                    // 这是 `goto continue` 越过尾部局部声明仍可编译的关键规则。
                    let label_scope = if index >= trailing_labels {
                        entry_scope
                    } else {
                        scope
                    };
                    if self
                        .labels
                        .insert(
                            label.id,
                            Site {
                                block: block_id,
                                scope: label_scope,
                            },
                        )
                        .is_some()
                    {
                        return Err(AstLowerError::DuplicateGotoLabel {
                            function: self.function,
                            label: label.id.index(),
                        });
                    }
                }
                AstStmt::DoBlock(body) => {
                    self.visit_block(body, Some(block_id), scope)?;
                }
                AstStmt::FunctionDecl(decl) => self.visit_function(&decl.func)?,
                AstStmt::LocalFunctionDecl(decl) => {
                    self.visit_function(&decl.func)?;
                    scope = self.push_scope(scope, decl.name, false);
                }
                AstStmt::Break | AstStmt::Continue | AstStmt::Error(_) => {}
            }
        }
        Ok(())
    }

    fn push_scope(&mut self, parent: usize, id: AstBindingRef, to_be_closed: bool) -> usize {
        let scope = self.scopes.len();
        self.scopes.push(ScopeNode {
            parent: Some(parent),
            binding: Some(ScopeBinding { id, to_be_closed }),
        });
        scope
    }

    fn visit_function(&self, function: &AstFunctionExpr) -> Result<(), AstLowerError> {
        verify_function(function.function.index(), &function.body)
    }

    fn visit_exprs(&self, exprs: &[AstExpr]) -> Result<(), AstLowerError> {
        for expr in exprs {
            self.visit_expr(expr)?;
        }
        Ok(())
    }

    fn visit_call(&self, call: &AstCallKind) -> Result<(), AstLowerError> {
        traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
            self.visit_expr(expr)?;
        });
        Ok(())
    }

    fn visit_lvalue(&self, target: &AstLValue) -> Result<(), AstLowerError> {
        traverse_lvalue_children!(target, borrow = [&], expr(expr) => {
            self.visit_expr(expr)?;
        });
        Ok(())
    }

    fn visit_expr(&self, expr: &AstExpr) -> Result<(), AstLowerError> {
        traverse_expr_children!(
            expr,
            iter = iter,
            borrow = [&],
            expr(child) => {
                self.visit_expr(child)?;
            },
            function(function) => {
                self.visit_function(function)?;
            }
        );
        Ok(())
    }

    fn finish(self) -> Result<(), AstLowerError> {
        let block_intervals = TreeIntervals::new(&self.block_parents);
        let scope_parents = self
            .scopes
            .iter()
            .map(|scope| scope.parent)
            .collect::<Vec<_>>();
        let scope_intervals = TreeIntervals::new(&scope_parents);

        for &(target, source) in &self.gotos {
            let label =
                self.labels
                    .get(&target)
                    .copied()
                    .ok_or(AstLowerError::MissingGotoLabel {
                        function: self.function,
                        label: target.index(),
                    })?;
            if !block_intervals.contains(label.block, source.block) {
                return Err(AstLowerError::InvisibleGotoLabel {
                    function: self.function,
                    label: target.index(),
                });
            }
            if !scope_intervals.contains(label.scope, source.scope) {
                let binding = self
                    .missing_target_binding(label.scope, source.scope, &scope_intervals)
                    .ok_or(AstLowerError::InvalidGotoScopeTree {
                        function: self.function,
                    })?;
                return Err(if binding.to_be_closed {
                    AstLowerError::GotoEntersToBeClosedScope {
                        function: self.function,
                        label: target.index(),
                        binding: binding.id,
                    }
                } else {
                    AstLowerError::GotoEntersLocalScope {
                        function: self.function,
                        label: target.index(),
                        binding: binding.id,
                    }
                });
            }
        }
        Ok(())
    }

    fn missing_target_binding(
        &self,
        mut target_scope: usize,
        source_scope: usize,
        intervals: &TreeIntervals,
    ) -> Option<ScopeBinding> {
        while let Some(node) = self.scopes.get(target_scope) {
            if intervals.contains(target_scope, source_scope) {
                break;
            }
            if let Some(binding) = node.binding {
                return Some(binding);
            }
            let Some(parent) = node.parent else {
                break;
            };
            target_scope = parent;
        }
        None
    }
}

struct TreeIntervals {
    enter: Vec<usize>,
    exit: Vec<usize>,
}

impl TreeIntervals {
    fn new(parents: &[Option<usize>]) -> Self {
        let mut children = vec![Vec::new(); parents.len()];
        for (node, parent) in parents.iter().copied().enumerate().skip(1) {
            if let Some(parent) = parent.and_then(|parent| children.get_mut(parent)) {
                parent.push(node);
            }
        }
        let mut enter = vec![0; parents.len()];
        let mut exit = vec![0; parents.len()];
        let mut clock = 0;
        let mut pending = (!parents.is_empty())
            .then_some((0, false))
            .into_iter()
            .collect::<Vec<_>>();
        while let Some((node, leaving)) = pending.pop() {
            if leaving {
                exit[node] = clock;
                clock += 1;
                continue;
            }
            enter[node] = clock;
            clock += 1;
            pending.push((node, true));
            pending.extend(children[node].iter().rev().map(|child| (*child, false)));
        }
        Self { enter, exit }
    }

    fn contains(&self, ancestor: usize, node: usize) -> bool {
        self.enter
            .get(ancestor)
            .zip(self.enter.get(node))
            .zip(self.exit.get(ancestor).zip(self.exit.get(node)))
            .is_some_and(
                |((ancestor_enter, node_enter), (ancestor_exit, node_exit))| {
                    ancestor_enter <= node_enter && node_exit <= ancestor_exit
                },
            )
    }
}
