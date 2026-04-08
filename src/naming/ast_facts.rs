//! 这个文件负责从最终 AST 收集 naming 需要的“成品结构事实”。
//!
//! Naming 发生在 Readability 之后，所以像“哪些 binding 还真实留在 AST 里”
//! “哪些 synthetic local 最终其实只是丢弃位”这类信息，不能再靠 HIR/Raw 的原始槽位推断。
//! 这里直接基于最终 AST 建一份轻量事实表，让命名阶段能按成品结构做决定。

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue,
    AstModule, AstNameRef, AstStmt, AstSyntheticLocalId,
};
use crate::ast::traverse::{
    traverse_call_children, traverse_expr_children, traverse_lvalue_children,
    traverse_stmt_children,
};
use crate::hir::{HirModule, HirProtoRef};

#[derive(Debug, Clone, Default)]
pub(super) struct AstNamingFacts {
    pub(super) functions: Vec<FunctionAstNamingFacts>,
}

#[derive(Debug, Clone, Default)]
pub(super) struct FunctionAstNamingFacts {
    pub(super) debug_like_binding_order: BTreeMap<AstBindingRef, usize>,
    pub(super) unused_synthetic_locals: BTreeSet<AstSyntheticLocalId>,
}

pub(super) fn collect_ast_naming_facts(module: &AstModule, hir: &HirModule) -> AstNamingFacts {
    let mut facts = AstNamingFacts {
        functions: vec![FunctionAstNamingFacts::default(); hir.protos.len()],
    };
    collect_function_facts(module.entry_function, &module.body, hir, &mut facts);
    facts
}

#[derive(Debug, Default)]
struct FunctionAstCollector {
    binding_order: Vec<AstBindingRef>,
    seen_bindings: BTreeSet<AstBindingRef>,
    declared_synthetic_locals: BTreeSet<AstSyntheticLocalId>,
    mentioned_synthetic_locals: BTreeSet<AstSyntheticLocalId>,
}

impl FunctionAstCollector {
    fn note_binding(&mut self, binding: AstBindingRef) {
        if self.seen_bindings.insert(binding) {
            self.binding_order.push(binding);
        }
        if let AstBindingRef::SyntheticLocal(local) = binding {
            self.declared_synthetic_locals.insert(local);
        }
    }

    fn note_name_ref(&mut self, name: &AstNameRef) {
        match name {
            AstNameRef::Local(local) => self.note_binding(AstBindingRef::Local(*local)),
            AstNameRef::SyntheticLocal(local) => {
                self.note_binding(AstBindingRef::SyntheticLocal(*local));
                self.mentioned_synthetic_locals.insert(*local);
            }
            AstNameRef::Param(_)
            | AstNameRef::Temp(_)
            | AstNameRef::Upvalue(_)
            | AstNameRef::Global(_) => {}
        }
    }

    fn finish(self) -> FunctionAstNamingFacts {
        let debug_like_binding_order = self
            .binding_order
            .into_iter()
            .enumerate()
            .map(|(index, binding)| (binding, index))
            .collect();
        let unused_synthetic_locals = self
            .declared_synthetic_locals
            .difference(&self.mentioned_synthetic_locals)
            .copied()
            .collect();

        FunctionAstNamingFacts {
            debug_like_binding_order,
            unused_synthetic_locals,
        }
    }
}

fn collect_function_facts(
    function: HirProtoRef,
    body: &AstBlock,
    hir: &HirModule,
    facts: &mut AstNamingFacts,
) {
    let mut collector = FunctionAstCollector::default();
    note_named_vararg_binding(function, hir, &mut collector);
    collect_block_facts(body, &mut collector, hir, facts);
    facts.functions[function.index()] = collector.finish();
}

fn note_named_vararg_binding(
    function: HirProtoRef,
    hir: &HirModule,
    collector: &mut FunctionAstCollector,
) {
    let Some(proto) = hir.protos.get(function.index()) else {
        return;
    };
    if proto.signature.has_vararg_param_reg
        && let Some(&local) = proto.locals.first()
    {
        collector.note_binding(AstBindingRef::Local(local));
    }
}

fn collect_block_facts(
    block: &AstBlock,
    collector: &mut FunctionAstCollector,
    hir: &HirModule,
    facts: &mut AstNamingFacts,
) {
    for stmt in &block.stmts {
        collect_stmt_facts(stmt, collector, hir, facts);
    }
}

fn collect_stmt_facts(
    stmt: &AstStmt,
    collector: &mut FunctionAstCollector,
    hir: &HirModule,
    facts: &mut AstNamingFacts,
) {
    // 先处理各变体的自定义 binding 收集
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                collector.note_binding(binding.id);
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

fn collect_nested_function_facts(
    function_expr: &AstFunctionExpr,
    hir: &HirModule,
    facts: &mut AstNamingFacts,
) {
    collect_function_facts(function_expr.function, &function_expr.body, hir, facts);
}

fn collect_function_name_facts(target: &AstFunctionName, collector: &mut FunctionAstCollector) {
    let path = match target {
        AstFunctionName::Plain(path) => path,
        AstFunctionName::Method(path, _) => path,
    };
    collector.note_name_ref(&path.root);
}

fn collect_call_facts(
    call: &AstCallKind,
    collector: &mut FunctionAstCollector,
    hir: &HirModule,
    facts: &mut AstNamingFacts,
) {
    traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        collect_expr_facts(expr, collector, hir, facts);
    });
}

fn collect_lvalue_facts(
    target: &AstLValue,
    collector: &mut FunctionAstCollector,
    hir: &HirModule,
    facts: &mut AstNamingFacts,
) {
    if let AstLValue::Name(name) = target {
        collector.note_name_ref(name);
    }
    traverse_lvalue_children!(target, borrow = [&], expr(expr) => {
        collect_expr_facts(expr, collector, hir, facts);
    });
}

fn collect_expr_facts(
    expr: &AstExpr,
    collector: &mut FunctionAstCollector,
    hir: &HirModule,
    facts: &mut AstNamingFacts,
) {
    if let AstExpr::Var(name) = expr {
        collector.note_name_ref(name);
    }
    traverse_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(child) => {
            collect_expr_facts(child, collector, hir, facts);
        },
        function(func) => {
            collect_nested_function_facts(func, hir, facts);
        }
    );
}
