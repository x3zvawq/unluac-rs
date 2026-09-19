//! 这个文件负责从最终 AST 收集 naming 需要的“成品结构事实”。
//!
//! Naming 发生在 Readability 之后，所以像“哪些 binding 还真实留在 AST 里”
//! “哪些 synthetic local 最终其实只是丢弃位”这类信息，不能再靠 HIR/Raw 的原始槽位推断。
//! 这里直接基于最终 AST 建一份轻量事实表，让命名阶段能按成品结构做决定。
//! 全局名字按函数后序位置发布，函数只持有其最终 AST 子树区间，不沿 HIR children
//! 复制后代集合。名字载荷借用该只读 AST，仅在本次命名内存活。例如兄弟函数分别
//! 引用 x/y，父函数避让两者，各子函数只避让自己的名字。

use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Range,
};

use crate::ast::traverse::{
    traverse_call_children, traverse_lvalue_children, traverse_stmt_children,
};
use crate::ast::visit::{ExprNode, expr_nodes};
use crate::ast::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName,
    AstGlobalBindingTarget, AstLValue, AstModule, AstNameRef, AstStmt, AstSyntheticLocalId,
};
use crate::graph::PositionIndex;
use crate::hir::{HirModule, HirProtoRef};

#[derive(Default)]
pub(super) struct AstNamingFacts<'ast> {
    pub(super) functions: Vec<FunctionAstNamingFacts>,
    global_names: PositionIndex<&'ast str>,
    next_function_position: usize,
}

impl AstNamingFacts<'_> {
    pub(super) fn reserves_global_name(&self, function: HirProtoRef, name: &str) -> bool {
        self.global_names
            .last_in(
                name,
                self.functions[function.index()].global_name_range.clone(),
            )
            .is_some()
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct FunctionAstNamingFacts {
    pub(super) used_params: BTreeSet<crate::hir::ParamId>,
    pub(super) debug_like_binding_order: BTreeMap<AstBindingRef, usize>,
    pub(super) unused_synthetic_locals: BTreeSet<AstSyntheticLocalId>,
    global_name_range: Range<usize>,
}

pub(super) fn collect_ast_naming_facts<'ast>(
    module: &'ast AstModule,
    hir: &HirModule,
) -> AstNamingFacts<'ast> {
    let mut facts = AstNamingFacts {
        functions: vec![FunctionAstNamingFacts::default(); hir.protos.len()],
        ..AstNamingFacts::default()
    };
    collect_function_facts(module.entry_function, &module.body, hir, &mut facts);
    facts
}

#[derive(Debug, Default)]
struct FunctionAstCollector<'ast> {
    used_params: BTreeSet<crate::hir::ParamId>,
    binding_order: BTreeMap<AstBindingRef, usize>,
    declared_synthetic_locals: BTreeSet<AstSyntheticLocalId>,
    mentioned_synthetic_locals: BTreeSet<AstSyntheticLocalId>,
    global_names: BTreeSet<&'ast str>,
}

impl<'ast> FunctionAstCollector<'ast> {
    fn note_binding(&mut self, binding: AstBindingRef) {
        let next = self.binding_order.len();
        self.binding_order.entry(binding).or_insert(next);
        if let AstBindingRef::SyntheticLocal(local) = binding {
            self.declared_synthetic_locals.insert(local);
        }
    }

    fn note_name_ref(&mut self, name: &'ast AstNameRef) {
        if let AstNameRef::Param(param) = name {
            self.used_params.insert(*param);
        }
        match AstBindingRef::from_name_ref(name) {
            Some(AstBindingRef::Local(local)) => self.note_binding(AstBindingRef::Local(local)),
            Some(AstBindingRef::SyntheticLocal(local)) => {
                self.note_binding(AstBindingRef::SyntheticLocal(local));
                self.mentioned_synthetic_locals.insert(local);
            }
            Some(AstBindingRef::Temp(_)) => {}
            None => {
                if let AstNameRef::Global(global) = name {
                    self.global_names.insert(global.text.as_str());
                }
            }
        }
    }

    fn finish(
        self,
        global_name_range: Range<usize>,
        global_names: &mut PositionIndex<&'ast str>,
    ) -> FunctionAstNamingFacts {
        for name in self.global_names {
            global_names.record(name, global_name_range.end - 1);
        }
        let unused_synthetic_locals = self
            .declared_synthetic_locals
            .difference(&self.mentioned_synthetic_locals)
            .copied()
            .collect();

        FunctionAstNamingFacts {
            used_params: self.used_params,
            debug_like_binding_order: self.binding_order,
            unused_synthetic_locals,
            global_name_range,
        }
    }
}

fn collect_function_facts<'ast>(
    function: HirProtoRef,
    body: &'ast AstBlock,
    hir: &HirModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    let start = facts.next_function_position;
    let mut collector = FunctionAstCollector::default();
    note_named_vararg_binding(function, hir, &mut collector);
    collect_block_facts(body, &mut collector, hir, facts);
    facts.next_function_position += 1;
    facts.functions[function.index()] =
        collector.finish(start..facts.next_function_position, &mut facts.global_names);
}

fn note_named_vararg_binding(
    function: HirProtoRef,
    hir: &HirModule,
    collector: &mut FunctionAstCollector<'_>,
) {
    let proto = &hir.protos[function.index()];
    if let Some(local) = proto.vararg_param_local {
        collector.note_binding(AstBindingRef::Local(local));
    }
}

fn collect_block_facts<'ast>(
    block: &'ast AstBlock,
    collector: &mut FunctionAstCollector<'ast>,
    hir: &HirModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    for stmt in &block.stmts {
        collect_stmt_facts(stmt, collector, hir, facts);
    }
}

fn collect_stmt_facts<'ast>(
    stmt: &'ast AstStmt,
    collector: &mut FunctionAstCollector<'ast>,
    hir: &HirModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    // 先处理各变体的自定义 binding 收集
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                collector.note_binding(binding.id);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for binding in &global_decl.bindings {
                if let AstGlobalBindingTarget::Name(name) = &binding.target {
                    collector.global_names.insert(name.text.as_str());
                }
            }
        }
        AstStmt::NumericFor(numeric_for) => {
            collector.note_binding(numeric_for.binding);
        }
        AstStmt::GenericFor(generic_for) => {
            for &binding in &generic_for.bindings {
                collector.note_binding(binding);
            }
        }
        AstStmt::FunctionDecl(function_decl) => {
            collect_function_name_facts(&function_decl.target, collector);
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            collector.note_binding(local_function_decl.name);
        }
        _ => {}
    }
    // 子节点递归全部交给宏
    traverse_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(expr) => {
            collect_expr_facts(expr, collector, hir, facts);
        },
        lvalue(lvalue) => {
            collect_lvalue_facts(lvalue, collector, hir, facts);
        },
        block(block) => {
            collect_block_facts(block, collector, hir, facts);
        },
        function(func) => {
            collect_nested_function_facts(func, hir, facts);
        },
        condition(cond) => {
            collect_expr_facts(cond, collector, hir, facts);
        },
        call(call) => {
            collect_call_facts(call, collector, hir, facts);
        }
    );
}

fn collect_nested_function_facts<'ast>(
    function_expr: &'ast AstFunctionExpr,
    hir: &HirModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    collect_function_facts(function_expr.function, &function_expr.body, hir, facts);
}

fn collect_function_name_facts<'ast>(
    target: &'ast AstFunctionName,
    collector: &mut FunctionAstCollector<'ast>,
) {
    let path = match target {
        AstFunctionName::Plain(path) => path,
        AstFunctionName::Method(path, _) => path,
    };
    collector.note_name_ref(&path.root);
}

fn collect_call_facts<'ast>(
    call: &'ast AstCallKind,
    collector: &mut FunctionAstCollector<'ast>,
    hir: &HirModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        collect_expr_facts(expr, collector, hir, facts);
    });
}

fn collect_lvalue_facts<'ast>(
    target: &'ast AstLValue,
    collector: &mut FunctionAstCollector<'ast>,
    hir: &HirModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    if let AstLValue::Name(name) = target {
        collector.note_name_ref(name);
    }
    traverse_lvalue_children!(target, borrow = [&], expr(expr) => {
        collect_expr_facts(expr, collector, hir, facts);
    });
}

fn collect_expr_facts<'ast>(
    expr: &'ast AstExpr,
    collector: &mut FunctionAstCollector<'ast>,
    hir: &HirModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    for node in expr_nodes(expr) {
        match node {
            ExprNode::Expr(AstExpr::Var(name)) => collector.note_name_ref(name),
            ExprNode::Function(func) => collect_nested_function_facts(func, hir, facts),
            _ => {}
        }
    }
}
