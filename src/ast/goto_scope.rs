//! 校验最终 AST 的 goto/label 词法作用域。
//!
//! 消费 Readability 后的声明和跳转位置，报告不合法的跨作用域进入。

use std::collections::BTreeMap;

use super::traverse::{traverse_call_children, traverse_lvalue_children};
use super::visit::{ExprNode, expr_nodes};
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
    verify_or_diagnose_function(module.entry_function.index(), &mut module.body, mode)
}

fn verify_or_diagnose_function(
    function: usize,
    body: &mut AstBlock,
    mode: GenerateMode,
) -> Result<(), AstLowerError> {
    let result = verify_function_shallow(function, body);
    match (mode, result) {
        (_, Ok(())) => {}
        (GenerateMode::Strict, Err(error)) => return Err(error),
        (GenerateMode::Permissive, Err(error)) => {
            body.stmts.insert(0, AstStmt::Error(error.to_string()));
        }
    }
    verify_or_diagnose_nested_in_block(body, mode)
}

fn verify_or_diagnose_nested_in_block(
    block: &mut AstBlock,
    mode: GenerateMode,
) -> Result<(), AstLowerError> {
    for stmt in &mut block.stmts {
        verify_or_diagnose_nested_in_stmt(stmt, mode)?;
    }
    Ok(())
}

fn verify_or_diagnose_nested_in_stmt(
    stmt: &mut AstStmt,
    mode: GenerateMode,
) -> Result<(), AstLowerError> {
    match stmt {
        AstStmt::LocalDecl(d) => {
            for v in &mut d.values {
                verify_or_diagnose_nested_in_expr(v, mode)?;
            }
        }
        AstStmt::GlobalDecl(d) => {
            for v in &mut d.values {
                verify_or_diagnose_nested_in_expr(v, mode)?;
            }
        }
        AstStmt::Assign(a) => {
            for t in &mut a.targets {
                verify_or_diagnose_nested_in_lvalue(t, mode)?;
            }
            for v in &mut a.values {
                verify_or_diagnose_nested_in_expr(v, mode)?;
            }
        }
        AstStmt::CallStmt(c) => verify_or_diagnose_nested_in_call(&mut c.call, mode)?,
        AstStmt::Return(r) => {
            for v in &mut r.values {
                verify_or_diagnose_nested_in_expr(v, mode)?;
            }
        }
        AstStmt::If(branch) => {
            verify_or_diagnose_nested_in_expr(&mut branch.cond, mode)?;
            verify_or_diagnose_nested_in_block(&mut branch.then_block, mode)?;
            if let Some(else_block) = &mut branch.else_block {
                verify_or_diagnose_nested_in_block(else_block, mode)?;
            }
        }
        AstStmt::While(w) => {
            verify_or_diagnose_nested_in_expr(&mut w.cond, mode)?;
            verify_or_diagnose_nested_in_block(&mut w.body, mode)?;
        }
        AstStmt::Repeat(r) => {
            verify_or_diagnose_nested_in_block(&mut r.body, mode)?;
            verify_or_diagnose_nested_in_expr(&mut r.cond, mode)?;
        }
        AstStmt::NumericFor(nf) => {
            verify_or_diagnose_nested_in_expr(&mut nf.start, mode)?;
            verify_or_diagnose_nested_in_expr(&mut nf.limit, mode)?;
            verify_or_diagnose_nested_in_expr(&mut nf.step, mode)?;
            verify_or_diagnose_nested_in_block(&mut nf.body, mode)?;
        }
        AstStmt::GenericFor(gf) => {
            for e in &mut gf.iterator {
                verify_or_diagnose_nested_in_expr(e, mode)?;
            }
            verify_or_diagnose_nested_in_block(&mut gf.body, mode)?;
        }
        AstStmt::DoBlock(b) => verify_or_diagnose_nested_in_block(b, mode)?,
        AstStmt::FunctionDecl(d) => {
            verify_or_diagnose_function(d.func.function.index(), &mut d.func.body, mode)?;
        }
        AstStmt::LocalFunctionDecl(d) => {
            verify_or_diagnose_function(d.func.function.index(), &mut d.func.body, mode)?;
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) | AstStmt::Error(_) => {}
    }
    Ok(())
}

fn verify_or_diagnose_nested_in_lvalue(
    target: &mut AstLValue,
    mode: GenerateMode,
) -> Result<(), AstLowerError> {
    match target {
        AstLValue::Name(_) => Ok(()),
        AstLValue::FieldAccess(f) => verify_or_diagnose_nested_in_expr(&mut f.base, mode),
        AstLValue::IndexAccess(ia) => {
            verify_or_diagnose_nested_in_expr(&mut ia.base, mode)?;
            verify_or_diagnose_nested_in_expr(&mut ia.index, mode)
        }
    }
}

fn verify_or_diagnose_nested_in_call(
    call: &mut AstCallKind,
    mode: GenerateMode,
) -> Result<(), AstLowerError> {
    match call {
        AstCallKind::Call(c) => {
            verify_or_diagnose_nested_in_expr(&mut c.callee, mode)?;
            for arg in &mut c.args {
                verify_or_diagnose_nested_in_expr(arg, mode)?;
            }
        }
        AstCallKind::MethodCall(m) => {
            verify_or_diagnose_nested_in_expr(&mut m.receiver, mode)?;
            for arg in &mut m.args {
                verify_or_diagnose_nested_in_expr(arg, mode)?;
            }
        }
    }
    Ok(())
}

fn verify_or_diagnose_nested_in_expr(
    expr: &mut AstExpr,
    mode: GenerateMode,
) -> Result<(), AstLowerError> {
    match expr {
        AstExpr::FunctionExpr(func) => {
            verify_or_diagnose_function(func.function.index(), &mut func.body, mode)
        }
        AstExpr::Unary(u) => verify_or_diagnose_nested_in_expr(&mut u.expr, mode),
        AstExpr::Binary(b) => {
            verify_or_diagnose_nested_in_expr(&mut b.lhs, mode)?;
            verify_or_diagnose_nested_in_expr(&mut b.rhs, mode)
        }
        AstExpr::LogicalAnd(l) | AstExpr::LogicalOr(l) => {
            verify_or_diagnose_nested_in_expr(&mut l.lhs, mode)?;
            verify_or_diagnose_nested_in_expr(&mut l.rhs, mode)
        }
        AstExpr::IfExpr(ie) => {
            verify_or_diagnose_nested_in_expr(&mut ie.cond, mode)?;
            verify_or_diagnose_nested_in_expr(&mut ie.then_expr, mode)?;
            verify_or_diagnose_nested_in_expr(&mut ie.else_expr, mode)
        }
        AstExpr::FieldAccess(f) => verify_or_diagnose_nested_in_expr(&mut f.base, mode),
        AstExpr::IndexAccess(ia) => {
            verify_or_diagnose_nested_in_expr(&mut ia.base, mode)?;
            verify_or_diagnose_nested_in_expr(&mut ia.index, mode)
        }
        AstExpr::Call(c) => {
            verify_or_diagnose_nested_in_expr(&mut c.callee, mode)?;
            for arg in &mut c.args {
                verify_or_diagnose_nested_in_expr(arg, mode)?;
            }
            Ok(())
        }
        AstExpr::MethodCall(m) => {
            verify_or_diagnose_nested_in_expr(&mut m.receiver, mode)?;
            for arg in &mut m.args {
                verify_or_diagnose_nested_in_expr(arg, mode)?;
            }
            Ok(())
        }
        AstExpr::TableConstructor(tc) => {
            for field in &mut tc.fields {
                match field {
                    super::AstTableField::Array(e) => {
                        verify_or_diagnose_nested_in_expr(e, mode)?;
                    }
                    super::AstTableField::Record(r) => {
                        if let super::AstTableKey::Expr(k) = &mut r.key {
                            verify_or_diagnose_nested_in_expr(k, mode)?;
                        }
                        verify_or_diagnose_nested_in_expr(&mut r.value, mode)?;
                    }
                }
            }
            Ok(())
        }
        AstExpr::SingleValue(inner) => verify_or_diagnose_nested_in_expr(inner, mode),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Number(_)
        | AstExpr::Vector(_)
        | AstExpr::String(_)
        | AstExpr::VarArg
        | AstExpr::Var(_)
        | AstExpr::Error(_) => Ok(()),
    }
}

pub(super) fn verify_function_only(function: usize, body: &AstBlock) -> Result<(), AstLowerError> {
    verify_function_shallow(function, body)
}

fn verify_function_shallow(function: usize, body: &AstBlock) -> Result<(), AstLowerError> {
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
                            label: label.id,
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

    fn visit_function(&self, _function: &AstFunctionExpr) -> Result<(), AstLowerError> {
        Ok(())
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
        for node in expr_nodes(expr) {
            if let ExprNode::Function(function) = node {
                self.visit_function(function)?;
            }
        }
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
                        label: target,
                    })?;
            if !block_intervals.contains(label.block, source.block) {
                return Err(AstLowerError::InvisibleGotoLabel {
                    function: self.function,
                    label: target,
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
                        label: target,
                        binding: binding.id,
                    }
                } else {
                    AstLowerError::GotoEntersLocalScope {
                        function: self.function,
                        label: target,
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

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;
    use crate::ast::{
        AstGoto, AstLabel, AstLocalBinding, AstLocalDecl, AstLocalFunctionDecl, AstReturn, LocalId,
        ProtoId,
    };

    fn make_module_with_broken_child_goto() -> AstModule {
        let child_body = AstBlock {
            stmts: vec![
                AstStmt::Goto(Box::new(AstGoto {
                    target: AstLabelId(0),
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(0)),
                        attr: AstLocalAttr::None,
                        is_debug_hinted: false,
                    }],
                    values: vec![AstExpr::Integer(1)],
                })),
                AstStmt::Label(Box::new(AstLabel { id: AstLabelId(0) })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Integer(2)],
                })),
            ],
        };
        let child_func = AstFunctionExpr {
            function: ProtoId(1),
            params: Vec::new(),
            is_vararg: false,
            named_vararg: None,
            body: child_body,
            captured_bindings: BTreeSet::new(),
            captured_params: BTreeSet::new(),
            capture_write_names: BTreeSet::new(),
        };
        AstModule {
            entry_function: ProtoId(0),
            body: AstBlock {
                stmts: vec![AstStmt::LocalFunctionDecl(Box::new(
                    AstLocalFunctionDecl {
                        name: AstBindingRef::Local(LocalId(0)),
                        func: child_func,
                    },
                ))],
            },
            ..AstModule::default()
        }
    }

    #[test]
    fn permissive_inserts_goto_scope_error_into_offending_child_function() {
        let mut module = make_module_with_broken_child_goto();
        verify_or_diagnose(&mut module, GenerateMode::Permissive).expect("permissive succeeds");
        assert!(
            !matches!(module.body.stmts.first(), Some(AstStmt::Error(_))),
            "root function should stay clean"
        );
        let AstStmt::LocalFunctionDecl(decl) = &module.body.stmts[0] else {
            panic!("expected local function decl");
        };
        assert!(
            matches!(decl.func.body.stmts.first(), Some(AstStmt::Error(msg)) if msg.contains("proto#1")),
            "expected diagnostic inserted at start of child function body, got {:?}",
            decl.func.body.stmts.first()
        );
    }

    #[test]
    fn strict_rejects_child_goto_entering_local_scope() {
        let mut module = make_module_with_broken_child_goto();
        let err = verify_or_diagnose(&mut module, GenerateMode::Strict)
            .expect_err("strict must reject");
        assert!(matches!(
            err,
            AstLowerError::GotoEntersLocalScope { function: 1, .. }
        ));
    }
}
