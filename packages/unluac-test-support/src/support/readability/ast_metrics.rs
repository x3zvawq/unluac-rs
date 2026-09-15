//! 最终 readability AST 的只读指标收集。
//!
//! 这里的事实来自 `DecompileState::readability`，不从生成文本猜测 local、函数或控制流。
//! 全模块计数包含所有 child function；`@proto=N` 则只计该 proto 自身的函数体，不进入其
//! child function。例如根 proto#0 声明一个 child proto#1，root 的 `function` 为 1，
//! 但 proto#0 不计 child body 中的 `if`，proto#1 才计该 `if`。一次遍历同时建立全模块和
//! 各 proto 的指标，供同一 case 的多个 AST 断言复用。
//! repeat 条件的局部绑定关系使用当前循环直属声明的身份集，不把显示名称或子函数同号
//! Local 当作条件来源；例如 `repeat local done = step() until done` 计一个绑定。

use std::collections::{BTreeMap, BTreeSet};

use unluac::ast::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstLValue, AstLocalAttr,
    AstModule, AstStmt,
};

use super::super::ReadabilityAstMetric;

const AST_METRIC_COUNT: usize = 25;

#[derive(Clone, Default)]
struct AstMetricCounts([usize; AST_METRIC_COUNT]);

impl AstMetricCounts {
    fn increment(&mut self, metric: ReadabilityAstMetric) {
        self.0[metric.index()] += 1;
    }
}

/// 一次遍历同时保留全模块指标与每个 proto 自身的指标；proto 域不穿透 child function body。
pub(super) struct AstMetricSummary {
    total: AstMetricCounts,
    proto_counts: Vec<AstMetricCounts>,
    proto_indexes: BTreeMap<usize, usize>,
    repeat_condition_locals: BTreeSet<AstBindingRef>,
}

impl AstMetricSummary {
    pub(super) fn collect(module: &AstModule) -> Self {
        let entry_proto = module.entry_function.index();
        let mut summary = Self {
            total: AstMetricCounts::default(),
            proto_counts: vec![AstMetricCounts::default()],
            proto_indexes: BTreeMap::from([(entry_proto, 0)]),
            repeat_condition_locals: BTreeSet::new(),
        };
        summary.visit_block(0, &module.body);
        summary
    }

    pub(super) fn count(&self, proto: Option<usize>) -> Option<&[usize; AST_METRIC_COUNT]> {
        match proto {
            None => Some(&self.total.0),
            Some(proto) => self
                .proto_indexes
                .get(&proto)
                .map(|index| &self.proto_counts[*index].0),
        }
    }

    fn increment(&mut self, scope: usize, metric: ReadabilityAstMetric) {
        self.total.increment(metric);
        self.proto_counts[scope].increment(metric);
    }

    fn visit_block(&mut self, scope: usize, block: &AstBlock) {
        for stmt in &block.stmts {
            self.visit_stmt(scope, stmt);
        }
    }

    fn visit_stmt(&mut self, scope: usize, stmt: &AstStmt) {
        match stmt {
            AstStmt::LocalDecl(decl) => {
                self.increment(scope, ReadabilityAstMetric::LocalDecl);
                if decl.values.is_empty() {
                    self.increment(scope, ReadabilityAstMetric::EmptyLocal);
                }
                for binding in &decl.bindings {
                    if binding.attr == AstLocalAttr::Close {
                        self.increment(scope, ReadabilityAstMetric::CloseBinding);
                    }
                }
                for value in &decl.values {
                    self.visit_expr(scope, value);
                }
            }
            AstStmt::GlobalDecl(decl) => {
                self.increment(scope, ReadabilityAstMetric::GlobalDecl);
                for value in &decl.values {
                    self.visit_expr(scope, value);
                }
            }
            AstStmt::Assign(assign) => {
                for target in &assign.targets {
                    self.visit_lvalue(scope, target);
                }
                for value in &assign.values {
                    self.visit_expr(scope, value);
                }
            }
            AstStmt::CallStmt(call) => self.visit_call(scope, &call.call),
            AstStmt::Return(ret) => {
                for value in &ret.values {
                    self.visit_expr(scope, value);
                }
            }
            AstStmt::If(if_stmt) => {
                self.increment(scope, ReadabilityAstMetric::If);
                self.visit_expr(scope, &if_stmt.cond);
                self.visit_block(scope, &if_stmt.then_block);
                if let Some(else_block) = &if_stmt.else_block {
                    self.visit_block(scope, else_block);
                }
            }
            AstStmt::While(while_stmt) => {
                self.increment(scope, ReadabilityAstMetric::While);
                self.visit_expr(scope, &while_stmt.cond);
                self.visit_block(scope, &while_stmt.body);
            }
            AstStmt::Repeat(repeat_stmt) => {
                self.increment(scope, ReadabilityAstMetric::Repeat);
                self.visit_block(scope, &repeat_stmt.body);
                // 只扫描直属声明；各循环的直属语句不重叠，不为每个候选重扫整个子树。
                self.repeat_condition_locals = repeat_stmt
                    .body
                    .stmts
                    .iter()
                    .filter_map(|stmt| match stmt {
                        AstStmt::LocalDecl(decl) if !decl.values.is_empty() => Some(decl),
                        _ => None,
                    })
                    .flat_map(|decl| decl.bindings.iter().map(|binding| binding.id))
                    .collect();
                self.visit_expr(scope, &repeat_stmt.cond);
                self.repeat_condition_locals.clear();
            }
            AstStmt::NumericFor(for_stmt) => {
                self.increment(scope, ReadabilityAstMetric::NumericFor);
                self.visit_expr(scope, &for_stmt.start);
                self.visit_expr(scope, &for_stmt.limit);
                self.visit_expr(scope, &for_stmt.step);
                self.visit_block(scope, &for_stmt.body);
            }
            AstStmt::GenericFor(for_stmt) => {
                self.increment(scope, ReadabilityAstMetric::GenericFor);
                for iterator in &for_stmt.iterator {
                    self.visit_expr(scope, iterator);
                }
                self.visit_block(scope, &for_stmt.body);
            }
            AstStmt::Break => self.increment(scope, ReadabilityAstMetric::Break),
            AstStmt::Continue => self.increment(scope, ReadabilityAstMetric::Continue),
            AstStmt::Goto(_) => self.increment(scope, ReadabilityAstMetric::Goto),
            AstStmt::Label(_) => self.increment(scope, ReadabilityAstMetric::Label),
            AstStmt::DoBlock(block) => {
                self.increment(scope, ReadabilityAstMetric::DoBlock);
                self.visit_block(scope, block);
            }
            AstStmt::FunctionDecl(decl) => self.visit_function(scope, &decl.func),
            AstStmt::LocalFunctionDecl(decl) => {
                self.increment(scope, ReadabilityAstMetric::LocalFunction);
                self.visit_function(scope, &decl.func);
            }
            AstStmt::Error(_) => self.increment(scope, ReadabilityAstMetric::Error),
        }
    }

    fn visit_lvalue(&mut self, scope: usize, lvalue: &AstLValue) {
        match lvalue {
            AstLValue::Name(_) => {}
            AstLValue::FieldAccess(access) => self.visit_expr(scope, &access.base),
            AstLValue::IndexAccess(access) => {
                self.visit_expr(scope, &access.base);
                self.visit_expr(scope, &access.index);
            }
        }
    }

    fn visit_call(&mut self, scope: usize, call: &AstCallKind) {
        match call {
            AstCallKind::Call(call) => self.visit_call_expr(scope, call),
            AstCallKind::MethodCall(call) => self.visit_method_call_expr(scope, call),
        }
    }

    fn visit_call_expr(&mut self, scope: usize, call: &unluac::ast::AstCallExpr) {
        self.increment(scope, ReadabilityAstMetric::Call);
        self.visit_expr(scope, &call.callee);
        for argument in &call.args {
            self.visit_expr(scope, argument);
        }
    }

    fn visit_method_call_expr(&mut self, scope: usize, call: &unluac::ast::AstMethodCallExpr) {
        self.increment(scope, ReadabilityAstMetric::Call);
        self.increment(scope, ReadabilityAstMetric::MethodCall);
        self.visit_expr(scope, &call.receiver);
        for argument in &call.args {
            self.visit_expr(scope, argument);
        }
    }

    fn visit_expr(&mut self, scope: usize, expr: &AstExpr) {
        match expr {
            AstExpr::FieldAccess(access) => self.visit_expr(scope, &access.base),
            AstExpr::IndexAccess(access) => {
                self.visit_expr(scope, &access.base);
                self.visit_expr(scope, &access.index);
            }
            AstExpr::Unary(unary) => self.visit_expr(scope, &unary.expr),
            AstExpr::Binary(binary) => {
                self.visit_expr(scope, &binary.lhs);
                self.visit_expr(scope, &binary.rhs);
            }
            AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
                self.visit_expr(scope, &logical.lhs);
                self.visit_expr(scope, &logical.rhs);
            }
            AstExpr::Call(call) => self.visit_call_expr(scope, call),
            AstExpr::MethodCall(call) => self.visit_method_call_expr(scope, call),
            AstExpr::SingleValue(inner) => self.visit_expr(scope, inner),
            AstExpr::TableConstructor(table) => {
                self.increment(scope, ReadabilityAstMetric::TableConstructor);
                for field in &table.fields {
                    match field {
                        unluac::ast::AstTableField::Array(value) => {
                            self.increment(scope, ReadabilityAstMetric::TableListField);
                            self.visit_expr(scope, value);
                        }
                        unluac::ast::AstTableField::Record(record) => {
                            self.increment(scope, ReadabilityAstMetric::TableRecordField);
                            if let unluac::ast::AstTableKey::Expr(key) = &record.key {
                                self.visit_expr(scope, key);
                            }
                            self.visit_expr(scope, &record.value);
                        }
                    }
                }
            }
            AstExpr::FunctionExpr(function) => self.visit_function(scope, function),
            AstExpr::Error(_) => self.increment(scope, ReadabilityAstMetric::Error),
            AstExpr::Var(name) => {
                if let Some(binding) = AstBindingRef::from_name_ref(name)
                    && self.repeat_condition_locals.remove(&binding)
                {
                    self.increment(scope, ReadabilityAstMetric::RepeatConditionLocal);
                }
            }
            AstExpr::Nil
            | AstExpr::Boolean(_)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::CaptureInitializer(_)
            | AstExpr::String(_)
            | AstExpr::Int64(_)
            | AstExpr::UInt64(_)
            | AstExpr::Complex { .. }
            | AstExpr::Vector(_)
            | AstExpr::VarArg => {}
        }
    }

    fn visit_function(&mut self, parent_scope: usize, function: &AstFunctionExpr) {
        // 条件中出现函数表达式时，child body 的同号 local 不属于外层 until 的读取。
        let repeat_condition_locals = std::mem::take(&mut self.repeat_condition_locals);
        self.increment(parent_scope, ReadabilityAstMetric::Function);
        if function.named_vararg.is_some() {
            self.increment(parent_scope, ReadabilityAstMetric::NamedVarargFunction);
        }
        if function.body.stmts.is_empty() {
            self.increment(parent_scope, ReadabilityAstMetric::EmptyFunction);
        }
        let proto = function.function.index();
        let scope = match self.proto_indexes.get(&proto) {
            Some(index) => *index,
            None => {
                let index = self.proto_counts.len();
                self.proto_counts.push(AstMetricCounts::default());
                self.proto_indexes.insert(proto, index);
                index
            }
        };
        self.visit_block(scope, &function.body);
        self.repeat_condition_locals = repeat_condition_locals;
    }
}

impl ReadabilityAstMetric {
    pub(super) const fn index(self) -> usize {
        match self {
            Self::EmptyLocal => 0,
            Self::EmptyFunction => 1,
            Self::If => 2,
            Self::While => 3,
            Self::Repeat => 4,
            Self::NumericFor => 5,
            Self::GenericFor => 6,
            Self::Goto => 7,
            Self::Label => 8,
            Self::Break => 9,
            Self::Continue => 10,
            Self::DoBlock => 11,
            Self::Function => 12,
            Self::LocalFunction => 13,
            Self::LocalDecl => 14,
            Self::Call => 15,
            Self::MethodCall => 16,
            Self::Error => 17,
            Self::CloseBinding => 18,
            Self::GlobalDecl => 19,
            Self::NamedVarargFunction => 20,
            Self::TableConstructor => 21,
            Self::TableListField => 22,
            Self::TableRecordField => 23,
            Self::RepeatConditionLocal => 24,
        }
    }

    pub(super) const fn label(self) -> &'static str {
        match self {
            Self::EmptyLocal => "empty-local",
            Self::EmptyFunction => "empty-function",
            Self::If => "if",
            Self::While => "while",
            Self::Repeat => "repeat",
            Self::NumericFor => "numeric-for",
            Self::GenericFor => "generic-for",
            Self::Goto => "goto",
            Self::Label => "label",
            Self::Break => "break",
            Self::Continue => "continue",
            Self::DoBlock => "do-block",
            Self::Function => "function",
            Self::LocalFunction => "local-function",
            Self::LocalDecl => "local-decl",
            Self::Call => "call",
            Self::MethodCall => "method-call",
            Self::Error => "error",
            Self::CloseBinding => "close-binding",
            Self::GlobalDecl => "global-decl",
            Self::NamedVarargFunction => "named-vararg-function",
            Self::TableConstructor => "table-constructor",
            Self::TableListField => "table-list-field",
            Self::TableRecordField => "table-record-field",
            Self::RepeatConditionLocal => "repeat-condition-local",
        }
    }
}
