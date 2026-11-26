//! 从最终 AST 收集 Naming 所需的绑定与全局名字事实。
//!
//! 事实借用当前成品结构，仅在本次命名内有效；原始槽位不替代最终词法身份。

use std::{
    borrow::Borrow,
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
    ParamId, ProtoId,
};

/// 按身份索引当前快照中的有序出现位置，用于查询词法范围内的全局名冲突。
struct PositionIndex<K>(BTreeMap<K, Vec<usize>>);

impl<K> Default for PositionIndex<K> {
    fn default() -> Self {
        Self(BTreeMap::new())
    }
}

impl<K: Ord> PositionIndex<K> {
    fn record(&mut self, key: K, position: usize) {
        let positions = self.0.entry(key).or_default();
        if positions.last() != Some(&position) {
            positions.push(position);
        }
    }

    fn last_in<Q: Ord + ?Sized>(&self, key: &Q, range: Range<usize>) -> Option<usize>
    where
        K: Borrow<Q>,
    {
        let positions = self.0.get(key)?;
        let end = positions.partition_point(|&position| position < range.end);
        positions[..end]
            .last()
            .copied()
            .filter(|&position| position >= range.start)
    }
}

#[derive(Default)]
pub(super) struct AstNamingFacts<'ast> {
    pub(super) functions: Vec<FunctionAstNamingFacts>,
    global_names: PositionIndex<&'ast str>,
    next_function_position: usize,
}

impl AstNamingFacts<'_> {
    pub(super) fn reserves_global_name(&self, function: ProtoId, name: &str) -> bool {
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
    pub(super) used_params: BTreeSet<ParamId>,
    pub(super) debug_like_binding_order: BTreeMap<AstBindingRef, usize>,
    pub(super) unused_synthetic_locals: BTreeSet<AstSyntheticLocalId>,
    /// 在当前函数中实际被表达式/赋值读取或写入（或被子闭包捕获）的局部绑定集合。
    pub(super) mentioned_bindings: BTreeSet<AstBindingRef>,
    /// 每个局部绑定在当前函数词法块树中的严格生命周期区间 `[enter, exit)`，
    /// 供 Naming 在严格不相交的作用域间安全复用同一局部/循环变量名（消除 `i2`/`i3` 漂移）。
    pub(super) binding_scope_intervals: BTreeMap<AstBindingRef, Range<usize>>,
    /// 在其词法作用域内存在依赖外层 `_ENV` 的全局/环境访问的局部绑定，禁止取名为 `_ENV`。
    pub(super) forbids_env_bindings: BTreeSet<AstBindingRef>,
    /// 函数体内存在依赖外层 `_ENV` 的全局/环境访问的形参，禁止取名为 `_ENV`。
    pub(super) forbids_env_params: BTreeSet<ParamId>,
    /// 本函数或其嵌套子函数是否读取/写入来自外层的 `_ENV`。
    pub(super) uses_outer_env: bool,
    global_name_range: Range<usize>,
}

impl FunctionAstNamingFacts {
    /// 判断该函数是否在最终 AST 中实际可达（排除 Luau `-O2` 内联后遗留的死 proto 槽位）。
    pub(super) fn is_reachable(&self) -> bool {
        !self.global_name_range.is_empty()
    }
}

pub(super) fn collect_ast_naming_facts(module: &AstModule) -> AstNamingFacts<'_> {
    let mut facts = AstNamingFacts {
        functions: vec![FunctionAstNamingFacts::default(); module.protos.len()],
        ..AstNamingFacts::default()
    };
    collect_function_facts(module.entry_function, &module.body, module, &mut facts);
    facts
}

#[derive(Debug, Default)]
struct FunctionAstCollector<'ast> {
    used_params: BTreeSet<ParamId>,
    binding_order: BTreeMap<AstBindingRef, usize>,
    declared_synthetic_locals: BTreeSet<AstSyntheticLocalId>,
    mentioned_synthetic_locals: BTreeSet<AstSyntheticLocalId>,
    mentioned_bindings: BTreeSet<AstBindingRef>,
    global_names: BTreeSet<&'ast str>,
    has_lexical_env: bool,
    active_params: Vec<ParamId>,
    /// 当前词法作用域栈：每层保存 `(binding, decl_clock)`，在离开块时统一收口生命周期终点。
    active_bindings: Vec<Vec<(AstBindingRef, usize)>>,
    binding_scope_intervals: BTreeMap<AstBindingRef, Range<usize>>,
    scope_clock: usize,
    forbids_env_bindings: BTreeSet<AstBindingRef>,
    forbids_env_params: BTreeSet<ParamId>,
    uses_outer_env: bool,
}

impl<'ast> FunctionAstCollector<'ast> {
    fn tick(&mut self) -> usize {
        let now = self.scope_clock;
        self.scope_clock += 1;
        now
    }

    fn note_binding(&mut self, binding: AstBindingRef) {
        let next = self.binding_order.len();
        self.binding_order.entry(binding).or_insert(next);
        if let AstBindingRef::SyntheticLocal(local) = binding {
            self.declared_synthetic_locals.insert(local);
        }
    }

    fn push_scope(&mut self) {
        self.tick();
        self.active_bindings.push(Vec::new());
    }

    fn pop_scope(&mut self) {
        let end = self.tick();
        if let Some(frame) = self.active_bindings.pop() {
            for (binding, start) in frame {
                self.binding_scope_intervals
                    .entry(binding)
                    .and_modify(|range| {
                        range.start = range.start.min(start);
                        range.end = range.end.max(end);
                    })
                    .or_insert(start..end);
            }
        }
    }

    fn declare_in_scope(&mut self, binding: AstBindingRef) {
        let start = self.tick();
        if let Some(scope) = self.active_bindings.last_mut() {
            scope.push((binding, start));
        }
    }

    fn mark_outer_env_use(&mut self) {
        if !self.has_lexical_env {
            return;
        }
        self.uses_outer_env = true;
        for &param in &self.active_params {
            self.forbids_env_params.insert(param);
        }
        for scope in &self.active_bindings {
            for &(binding, _) in scope {
                self.forbids_env_bindings.insert(binding);
            }
        }
    }

    fn note_name_ref(&mut self, name: &'ast AstNameRef) {
        if let AstNameRef::Param(param) = name {
            self.used_params.insert(*param);
        }
        match AstBindingRef::from_name_ref(name) {
            Some(AstBindingRef::Local(local)) => {
                let b = AstBindingRef::Local(local);
                self.note_binding(b);
                self.mentioned_bindings.insert(b);
            }
            Some(AstBindingRef::SyntheticLocal(local)) => {
                let b = AstBindingRef::SyntheticLocal(local);
                self.note_binding(b);
                self.mentioned_bindings.insert(b);
                self.mentioned_synthetic_locals.insert(local);
            }
            None => match name {
                AstNameRef::Global(global) => {
                    self.global_names.insert(global.text.as_str());
                    self.mark_outer_env_use();
                }
                AstNameRef::Environment => {
                    self.mark_outer_env_use();
                }
                _ => {}
            },
        }
    }

    fn finish(
        mut self,
        global_name_range: Range<usize>,
        global_names: &mut PositionIndex<&'ast str>,
    ) -> FunctionAstNamingFacts {
        while !self.active_bindings.is_empty() {
            self.pop_scope();
        }
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
            mentioned_bindings: self.mentioned_bindings,
            binding_scope_intervals: self.binding_scope_intervals,
            forbids_env_bindings: self.forbids_env_bindings,
            forbids_env_params: self.forbids_env_params,
            uses_outer_env: self.uses_outer_env,
            global_name_range,
        }
    }
}

fn collect_function_facts<'ast>(
    function: ProtoId,
    body: &'ast AstBlock,
    module: &'ast AstModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    let start = facts.next_function_position;
    let has_lexical_env = module.target_dialect.is_none_or(|d| {
        matches!(
            d,
            crate::decompile::DecompileDialect::Lua52
                | crate::decompile::DecompileDialect::Lua53
                | crate::decompile::DecompileDialect::Lua54
                | crate::decompile::DecompileDialect::Lua55
        )
    });
    let proto = &module.protos[function.index()];
    let mut collector = FunctionAstCollector {
        has_lexical_env,
        active_params: proto.params.clone(),
        active_bindings: vec![Vec::new()],
        ..FunctionAstCollector::default()
    };
    note_named_vararg_binding(function, module, &mut collector);
    if let Some(local) = proto.vararg_param_local {
        collector.declare_in_scope(AstBindingRef::Local(local));
    }
    collect_block_facts(body, &mut collector, module, facts);
    facts.next_function_position += 1;
    facts.functions[function.index()] =
        collector.finish(start..facts.next_function_position, &mut facts.global_names);
}

fn note_named_vararg_binding(
    function: ProtoId,
    module: &AstModule,
    collector: &mut FunctionAstCollector<'_>,
) {
    let proto = &module.protos[function.index()];
    if let Some(local) = proto.vararg_param_local {
        collector.note_binding(AstBindingRef::Local(local));
    }
}

fn collect_block_facts<'ast>(
    block: &'ast AstBlock,
    collector: &mut FunctionAstCollector<'ast>,
    module: &'ast AstModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    collector.push_scope();
    for stmt in &block.stmts {
        collect_stmt_facts(stmt, collector, module, facts);
    }
    collector.pop_scope();
}

fn collect_stmt_facts<'ast>(
    stmt: &'ast AstStmt,
    collector: &mut FunctionAstCollector<'ast>,
    module: &'ast AstModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                collector.note_binding(binding.id);
            }
            for value in &local_decl.values {
                collect_expr_facts(value, collector, module, facts);
            }
            // Lua 规则：`local x = expr` 在 RHS 求值完毕后 `x` 才进入当前块作用域。
            for binding in &local_decl.bindings {
                collector.declare_in_scope(binding.id);
            }
            return;
        }
        AstStmt::GlobalDecl(global_decl) => {
            collector.mark_outer_env_use();
            for binding in &global_decl.bindings {
                if let AstGlobalBindingTarget::Name(name) = &binding.target {
                    collector.global_names.insert(name.text.as_str());
                }
            }
        }
        AstStmt::Repeat(repeat_stmt) => {
            // `repeat ... until cond` 的条件位于循环体词法作用域内。
            collector.push_scope();
            for inner in &repeat_stmt.body.stmts {
                collect_stmt_facts(inner, collector, module, facts);
            }
            collect_expr_facts(&repeat_stmt.cond, collector, module, facts);
            collector.pop_scope();
            return;
        }
        AstStmt::NumericFor(numeric_for) => {
            collector.note_binding(numeric_for.binding);
            collect_expr_facts(&numeric_for.start, collector, module, facts);
            collect_expr_facts(&numeric_for.limit, collector, module, facts);
            collect_expr_facts(&numeric_for.step, collector, module, facts);
            collector.push_scope();
            collector.declare_in_scope(numeric_for.binding);
            for inner in &numeric_for.body.stmts {
                collect_stmt_facts(inner, collector, module, facts);
            }
            collector.pop_scope();
            return;
        }
        AstStmt::GenericFor(generic_for) => {
            for &binding in &generic_for.bindings {
                collector.note_binding(binding);
            }
            for expr in &generic_for.iterator {
                collect_expr_facts(expr, collector, module, facts);
            }
            collector.push_scope();
            for &binding in &generic_for.bindings {
                collector.declare_in_scope(binding);
            }
            for inner in &generic_for.body.stmts {
                collect_stmt_facts(inner, collector, module, facts);
            }
            collector.pop_scope();
            return;
        }
        AstStmt::FunctionDecl(function_decl) => {
            collect_function_name_facts(&function_decl.target, collector);
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            collector.note_binding(local_function_decl.name);
            collector.declare_in_scope(local_function_decl.name);
        }
        _ => {}
    }
    traverse_stmt_children!(
        stmt,
        iter = iter,
        opt = as_ref,
        borrow = [&],
        expr(expr) => {
            collect_expr_facts(expr, collector, module, facts);
        },
        lvalue(lvalue) => {
            collect_lvalue_facts(lvalue, collector, module, facts);
        },
        block(block) => {
            collect_block_facts(block, collector, module, facts);
        },
        function(func) => {
            collect_nested_function_facts(func, collector, module, facts);
        },
        condition(cond) => {
            collect_expr_facts(cond, collector, module, facts);
        },
        call(call) => {
            collect_call_facts(call, collector, module, facts);
        }
    );
}

fn collect_nested_function_facts<'ast>(
    function_expr: &'ast AstFunctionExpr,
    parent_collector: &mut FunctionAstCollector<'ast>,
    module: &'ast AstModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    collect_function_facts(function_expr.function, &function_expr.body, module, facts);
    let child_uses_outer_env = facts.functions[function_expr.function.index()].uses_outer_env;
    let child_proto = &module.protos[function_expr.function.index()];
    if child_uses_outer_env && child_proto.lexical_environment_local.is_none() {
        parent_collector.mark_outer_env_use();
    }
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
    module: &'ast AstModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    traverse_call_children!(call, iter = iter, borrow = [&], expr(expr) => {
        collect_expr_facts(expr, collector, module, facts);
    });
}

fn collect_lvalue_facts<'ast>(
    target: &'ast AstLValue,
    collector: &mut FunctionAstCollector<'ast>,
    module: &'ast AstModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    if let AstLValue::Name(name) = target {
        collector.note_name_ref(name);
    }
    traverse_lvalue_children!(target, borrow = [&], expr(expr) => {
        collect_expr_facts(expr, collector, module, facts);
    });
}

fn collect_expr_facts<'ast>(
    expr: &'ast AstExpr,
    collector: &mut FunctionAstCollector<'ast>,
    module: &'ast AstModule,
    facts: &mut AstNamingFacts<'ast>,
) {
    for node in expr_nodes(expr) {
        match node {
            ExprNode::Expr(AstExpr::Var(name)) => collector.note_name_ref(name),
            ExprNode::Function(func) => {
                collect_nested_function_facts(func, collector, module, facts);
            }
            _ => {}
        }
    }
}
