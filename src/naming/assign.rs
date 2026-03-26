//! AST -> NameMap 命名分配。

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue,
    AstLocalFunctionDecl, AstMethodCallExpr, AstModule, AstNameRef, AstStmt, AstSyntheticLocalId,
    AstTableField, AstTableKey,
};
use crate::hir::{HirModule, HirProto, HirProtoRef, LocalId, ParamId, UpvalueId};
use crate::parser::{RawChunk, RawLocalVar, RawProto, RawString};

use super::NamingError;

/// Naming 模式。
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum NamingMode {
    DebugLike,
    #[default]
    Simple,
    Heuristic,
}

impl NamingMode {
    pub const fn label(self) -> &'static str {
        match self {
            Self::DebugLike => "debug-like",
            Self::Simple => "simple",
            Self::Heuristic => "heuristic",
        }
    }
}

/// Naming 选项。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NamingOptions {
    pub mode: NamingMode,
    pub debug_like_include_function: bool,
}

impl Default for NamingOptions {
    fn default() -> Self {
        Self {
            mode: NamingMode::Simple,
            debug_like_include_function: true,
        }
    }
}

/// 命名来源。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NameSource {
    Debug,
    SelfParam,
    LoopRole,
    FieldName,
    TableShape,
    BoolShape,
    FunctionShape,
    ResultShape,
    DebugLike,
    Simple,
    ConflictFallback,
}

impl NameSource {
    pub const fn label(self) -> &'static str {
        match self {
            Self::Debug => "debug",
            Self::SelfParam => "self-param",
            Self::LoopRole => "loop-role",
            Self::FieldName => "field-name",
            Self::TableShape => "table-shape",
            Self::BoolShape => "bool-shape",
            Self::FunctionShape => "function-shape",
            Self::ResultShape => "result-shape",
            Self::DebugLike => "debug-like",
            Self::Simple => "simple",
            Self::ConflictFallback => "conflict-fallback",
        }
    }
}

/// 单个名字槽位的最终结果。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NameInfo {
    pub text: String,
    pub source: NameSource,
    pub renamed: bool,
}

/// 单个函数上下文的名字表。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FunctionNameMap {
    pub params: Vec<NameInfo>,
    pub locals: Vec<NameInfo>,
    pub synthetic_locals: BTreeMap<AstSyntheticLocalId, NameInfo>,
    pub upvalues: Vec<NameInfo>,
}

/// Naming 阶段产出的整模块名字表。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct NameMap {
    pub entry_function: HirProtoRef,
    pub mode: NamingMode,
    pub functions: Vec<FunctionNameMap>,
}

impl NameMap {
    pub fn function(&self, function: HirProtoRef) -> Option<&FunctionNameMap> {
        self.functions.get(function.index())
    }
}

#[derive(Debug, Clone, Default)]
struct NamingEvidence {
    functions: Vec<FunctionNamingEvidence>,
}

#[derive(Debug, Clone, Default)]
struct FunctionNamingEvidence {
    param_debug_names: Vec<Option<String>>,
    local_debug_names: Vec<Option<String>>,
    upvalue_debug_names: Vec<Option<String>>,
    temp_debug_names: Vec<Option<String>>,
}

#[derive(Debug, Clone, Default)]
struct FunctionHints {
    param_hints: BTreeMap<ParamId, CandidateHint>,
    local_hints: BTreeMap<LocalId, CandidateHint>,
    synthetic_locals: BTreeSet<AstSyntheticLocalId>,
    synthetic_local_hints: BTreeMap<AstSyntheticLocalId, CandidateHint>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CandidateHint {
    text: String,
    source: NameSource,
}

#[derive(Debug, Clone, Copy, Default)]
struct LoopContext {
    numeric_depth: usize,
}

#[derive(Debug, Default)]
struct ModuleNameAllocator {
    function_shape_names: BTreeSet<String>,
    next_function_shape_suffix: BTreeMap<String, usize>,
}

impl ModuleNameAllocator {
    fn reserve_function_shape_name(
        &mut self,
        candidate: CandidateHint,
        used_in_function: &BTreeSet<String>,
        mode: NamingMode,
    ) -> CandidateHint {
        if mode == NamingMode::DebugLike || candidate.source != NameSource::FunctionShape {
            return candidate;
        }

        // `fn` 这类函数形状名如果每个函数都从头开始，会在阅读时迅速失去区分度。
        // 这里单独做模块级递增，只影响函数形状名，不去污染其它局部命名规则。
        let base = candidate.text;
        let mut next_suffix = self
            .next_function_shape_suffix
            .get(&base)
            .copied()
            .unwrap_or(1);

        loop {
            let text = if next_suffix == 1 {
                base.clone()
            } else {
                format!("{base}{next_suffix}")
            };
            if !self.function_shape_names.contains(&text)
                && !used_in_function.contains(&text)
                && !is_lua_keyword(&text)
            {
                self.function_shape_names.insert(text.clone());
                self.next_function_shape_suffix
                    .insert(base, next_suffix.saturating_add(1));
                return CandidateHint {
                    text,
                    source: candidate.source,
                };
            }
            next_suffix = next_suffix.saturating_add(1);
        }
    }
}

/// 对外的 Naming 入口。
pub fn assign_names(
    module: &AstModule,
    hir: &HirModule,
    raw: &RawChunk,
    options: NamingOptions,
) -> Result<NameMap, NamingError> {
    let evidence = build_naming_evidence(raw, hir)?;
    validate_readability_ast(module, module.entry_function, hir)?;
    let mut hints = vec![FunctionHints::default(); hir.protos.len()];
    collect_function_hints(module, hir, &mut hints)?;
    let mut module_names = ModuleNameAllocator::default();

    let functions = hir
        .protos
        .iter()
        .map(|proto| {
            assign_names_for_function(
                proto,
                &evidence.functions[proto.id.index()],
                &hints[proto.id.index()],
                options,
                &mut module_names,
            )
        })
        .collect::<Vec<_>>();

    Ok(NameMap {
        entry_function: module.entry_function,
        mode: options.mode,
        functions,
    })
}

fn build_naming_evidence(raw: &RawChunk, hir: &HirModule) -> Result<NamingEvidence, NamingError> {
    let mut raw_functions = Vec::new();
    collect_raw_functions(&raw.main, &mut raw_functions);
    if raw_functions.len() != hir.protos.len() {
        return Err(NamingError::EvidenceProtoCountMismatch {
            raw_count: raw_functions.len(),
            hir_count: hir.protos.len(),
        });
    }

    let functions = raw_functions
        .into_iter()
        .zip(hir.protos.iter())
        .map(|(raw_proto, hir_proto)| build_function_evidence(raw_proto, hir_proto))
        .collect();
    Ok(NamingEvidence { functions })
}

fn build_function_evidence(raw: &RawProto, hir: &HirProto) -> FunctionNamingEvidence {
    let param_debug_names = (0..hir.params.len())
        .map(|reg| debug_local_name_for_reg_at_pc(raw, reg, 0))
        .collect::<Vec<_>>();

    let mut local_debug_names = vec![None; hir.locals.len()];
    if raw.common.signature.has_vararg_param_reg
        && let Some(slot) = local_debug_names.first_mut()
    {
        *slot = debug_local_name_for_reg_at_pc(raw, hir.params.len(), 0);
    }

    let upvalue_debug_names = hir
        .upvalues
        .iter()
        .map(|upvalue| {
            raw.common
                .debug_info
                .common
                .upvalue_names
                .get(upvalue.index())
                .map(decode_raw_string)
        })
        .collect::<Vec<_>>();

    FunctionNamingEvidence {
        param_debug_names,
        local_debug_names,
        upvalue_debug_names,
        temp_debug_names: hir.temp_debug_locals.clone(),
    }
}

fn collect_raw_functions<'a>(proto: &'a RawProto, functions: &mut Vec<&'a RawProto>) {
    functions.push(proto);
    for child in &proto.common.children {
        collect_raw_functions(child, functions);
    }
}

fn collect_function_hints(
    module: &AstModule,
    hir: &HirModule,
    hints: &mut [FunctionHints],
) -> Result<(), NamingError> {
    ensure_function_exists(hir, module.entry_function)?;
    collect_block_hints(
        module.entry_function,
        &module.body,
        hints,
        LoopContext::default(),
        hir,
    )
}

fn collect_block_hints(
    function: HirProtoRef,
    block: &AstBlock,
    hints: &mut [FunctionHints],
    loop_ctx: LoopContext,
    hir: &HirModule,
) -> Result<(), NamingError> {
    for stmt in &block.stmts {
        collect_stmt_hints(function, stmt, hints, loop_ctx, hir)?;
    }
    Ok(())
}

fn validate_readability_ast(
    module: &AstModule,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    ensure_function_exists(hir, function)?;
    validate_block_has_no_temps(&module.body, function, hir)
}

fn validate_block_has_no_temps(
    block: &AstBlock,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    for stmt in &block.stmts {
        validate_stmt_has_no_temps(stmt, function, hir)?;
    }
    Ok(())
}

fn validate_stmt_has_no_temps(
    stmt: &AstStmt,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                if let AstBindingRef::Temp(temp) = binding.id {
                    return Err(NamingError::UnexpectedTemp {
                        function: function.index(),
                        temp: temp.index(),
                    });
                }
            }
            for value in &local_decl.values {
                validate_expr_has_no_temps(value, function, hir)?;
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                validate_expr_has_no_temps(value, function, hir)?;
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                validate_lvalue_has_no_temps(target, function, hir)?;
            }
            for value in &assign.values {
                validate_expr_has_no_temps(value, function, hir)?;
            }
        }
        AstStmt::CallStmt(call_stmt) => validate_call_has_no_temps(&call_stmt.call, function, hir)?,
        AstStmt::Return(ret) => {
            for value in &ret.values {
                validate_expr_has_no_temps(value, function, hir)?;
            }
        }
        AstStmt::If(if_stmt) => {
            validate_expr_has_no_temps(&if_stmt.cond, function, hir)?;
            validate_block_has_no_temps(&if_stmt.then_block, function, hir)?;
            if let Some(else_block) = &if_stmt.else_block {
                validate_block_has_no_temps(else_block, function, hir)?;
            }
        }
        AstStmt::While(while_stmt) => {
            validate_expr_has_no_temps(&while_stmt.cond, function, hir)?;
            validate_block_has_no_temps(&while_stmt.body, function, hir)?;
        }
        AstStmt::Repeat(repeat_stmt) => {
            validate_block_has_no_temps(&repeat_stmt.body, function, hir)?;
            validate_expr_has_no_temps(&repeat_stmt.cond, function, hir)?;
        }
        AstStmt::NumericFor(numeric_for) => {
            validate_expr_has_no_temps(&numeric_for.start, function, hir)?;
            validate_expr_has_no_temps(&numeric_for.limit, function, hir)?;
            validate_expr_has_no_temps(&numeric_for.step, function, hir)?;
            validate_block_has_no_temps(&numeric_for.body, function, hir)?;
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                validate_expr_has_no_temps(expr, function, hir)?;
            }
            validate_block_has_no_temps(&generic_for.body, function, hir)?;
        }
        AstStmt::DoBlock(block) => validate_block_has_no_temps(block, function, hir)?,
        AstStmt::FunctionDecl(function_decl) => {
            validate_function_name_has_no_temps(&function_decl.target, function)?;
            validate_function_expr_has_no_temps(&function_decl.func, hir)?;
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            if let AstBindingRef::Temp(temp) = local_function_decl.name {
                return Err(NamingError::UnexpectedTemp {
                    function: function.index(),
                    temp: temp.index(),
                });
            }
            validate_function_expr_has_no_temps(&local_function_decl.func, hir)?;
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
    }
    Ok(())
}

fn validate_function_expr_has_no_temps(
    function_expr: &AstFunctionExpr,
    hir: &HirModule,
) -> Result<(), NamingError> {
    ensure_function_exists(hir, function_expr.function)?;
    validate_block_has_no_temps(&function_expr.body, function_expr.function, hir)
}

fn validate_function_name_has_no_temps(
    target: &AstFunctionName,
    function: HirProtoRef,
) -> Result<(), NamingError> {
    let path = match target {
        AstFunctionName::Plain(path) => path,
        AstFunctionName::Method(path, _) => path,
    };
    if let AstNameRef::Temp(temp) = path.root {
        return Err(NamingError::UnexpectedTemp {
            function: function.index(),
            temp: temp.index(),
        });
    }
    Ok(())
}

fn validate_call_has_no_temps(
    call: &AstCallKind,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    match call {
        AstCallKind::Call(call) => {
            validate_expr_has_no_temps(&call.callee, function, hir)?;
            for arg in &call.args {
                validate_expr_has_no_temps(arg, function, hir)?;
            }
        }
        AstCallKind::MethodCall(call) => {
            validate_expr_has_no_temps(&call.receiver, function, hir)?;
            for arg in &call.args {
                validate_expr_has_no_temps(arg, function, hir)?;
            }
        }
    }
    Ok(())
}

fn validate_lvalue_has_no_temps(
    target: &AstLValue,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    match target {
        AstLValue::Name(AstNameRef::Temp(temp)) => Err(NamingError::UnexpectedTemp {
            function: function.index(),
            temp: temp.index(),
        }),
        AstLValue::Name(_) => Ok(()),
        AstLValue::FieldAccess(access) => validate_expr_has_no_temps(&access.base, function, hir),
        AstLValue::IndexAccess(access) => {
            validate_expr_has_no_temps(&access.base, function, hir)?;
            validate_expr_has_no_temps(&access.index, function, hir)
        }
    }
}

fn validate_expr_has_no_temps(
    expr: &AstExpr,
    function: HirProtoRef,
    hir: &HirModule,
) -> Result<(), NamingError> {
    match expr {
        AstExpr::Var(AstNameRef::Temp(temp)) => Err(NamingError::UnexpectedTemp {
            function: function.index(),
            temp: temp.index(),
        }),
        AstExpr::Var(_) | AstExpr::Nil | AstExpr::Boolean(_) | AstExpr::Integer(_)
        | AstExpr::Number(_) | AstExpr::String(_) | AstExpr::VarArg => Ok(()),
        AstExpr::FieldAccess(access) => validate_expr_has_no_temps(&access.base, function, hir),
        AstExpr::IndexAccess(access) => {
            validate_expr_has_no_temps(&access.base, function, hir)?;
            validate_expr_has_no_temps(&access.index, function, hir)
        }
        AstExpr::Unary(unary) => validate_expr_has_no_temps(&unary.expr, function, hir),
        AstExpr::Binary(binary) => {
            validate_expr_has_no_temps(&binary.lhs, function, hir)?;
            validate_expr_has_no_temps(&binary.rhs, function, hir)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            validate_expr_has_no_temps(&logical.lhs, function, hir)?;
            validate_expr_has_no_temps(&logical.rhs, function, hir)
        }
        AstExpr::Call(call) => {
            validate_expr_has_no_temps(&call.callee, function, hir)?;
            for arg in &call.args {
                validate_expr_has_no_temps(arg, function, hir)?;
            }
            Ok(())
        }
        AstExpr::MethodCall(call) => {
            validate_expr_has_no_temps(&call.receiver, function, hir)?;
            for arg in &call.args {
                validate_expr_has_no_temps(arg, function, hir)?;
            }
            Ok(())
        }
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    AstTableField::Array(value) => validate_expr_has_no_temps(value, function, hir)?,
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &record.key {
                            validate_expr_has_no_temps(key, function, hir)?;
                        }
                        validate_expr_has_no_temps(&record.value, function, hir)?;
                    }
                }
            }
            Ok(())
        }
        AstExpr::FunctionExpr(function_expr) => validate_function_expr_has_no_temps(function_expr, hir),
    }
}

fn collect_stmt_hints(
    function: HirProtoRef,
    stmt: &AstStmt,
    hints: &mut [FunctionHints],
    loop_ctx: LoopContext,
    hir: &HirModule,
) -> Result<(), NamingError> {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for value in &local_decl.values {
                collect_expr_hints(function, value, hints, hir)?;
            }
            for binding in &local_decl.bindings {
                record_binding_presence(function, binding.id, hints);
            }
            for (binding, value) in local_decl.bindings.iter().zip(local_decl.values.iter()) {
                register_binding_expr_hint(function, binding.id, value, hints);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            for value in &global_decl.values {
                collect_expr_hints(function, value, hints, hir)?;
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_hints(function, target, hints, hir)?;
            }
            for value in &assign.values {
                collect_expr_hints(function, value, hints, hir)?;
            }
            if let ([AstLValue::Name(name)], [value]) =
                (assign.targets.as_slice(), assign.values.as_slice())
                && let Some(binding) = binding_from_name_ref(name)
            {
                record_binding_presence(function, binding, hints);
                register_binding_expr_hint(function, binding, value, hints);
            }
        }
        AstStmt::CallStmt(call_stmt) => collect_call_hints(function, &call_stmt.call, hints, hir)?,
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_hints(function, value, hints, hir)?;
            }
        }
        AstStmt::If(if_stmt) => {
            collect_expr_hints(function, &if_stmt.cond, hints, hir)?;
            collect_block_hints(function, &if_stmt.then_block, hints, loop_ctx, hir)?;
            if let Some(else_block) = &if_stmt.else_block {
                collect_block_hints(function, else_block, hints, loop_ctx, hir)?;
            }
        }
        AstStmt::While(while_stmt) => {
            collect_expr_hints(function, &while_stmt.cond, hints, hir)?;
            collect_block_hints(function, &while_stmt.body, hints, loop_ctx, hir)?;
        }
        AstStmt::Repeat(repeat_stmt) => {
            collect_block_hints(function, &repeat_stmt.body, hints, loop_ctx, hir)?;
            collect_expr_hints(function, &repeat_stmt.cond, hints, hir)?;
        }
        AstStmt::NumericFor(numeric_for) => {
            let candidate = numeric_loop_name(loop_ctx.numeric_depth);
            register_binding_hint(function, numeric_for.binding, candidate, NameSource::LoopRole, hints);
            collect_expr_hints(function, &numeric_for.start, hints, hir)?;
            collect_expr_hints(function, &numeric_for.limit, hints, hir)?;
            collect_expr_hints(function, &numeric_for.step, hints, hir)?;
            collect_block_hints(
                function,
                &numeric_for.body,
                hints,
                LoopContext {
                    numeric_depth: loop_ctx.numeric_depth + 1,
                },
                hir,
            )?;
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_expr_hints(function, expr, hints, hir)?;
            }
            for (index, binding) in generic_for.bindings.iter().copied().enumerate() {
                let candidate = match index {
                    0 if generic_for.bindings.len() == 1 => "item",
                    0 => "k",
                    1 => "v",
                    _ => "extra",
                };
                register_binding_hint(function, binding, candidate, NameSource::LoopRole, hints);
            }
            collect_block_hints(function, &generic_for.body, hints, loop_ctx, hir)?;
        }
        AstStmt::DoBlock(block) => collect_block_hints(function, block, hints, loop_ctx, hir)?,
        AstStmt::FunctionDecl(function_decl) => {
            if matches!(function_decl.target, AstFunctionName::Method(_, _))
                && let Some(first_param) = function_decl.func.params.first().copied()
            {
                register_param_hint(
                    function_decl.func.function,
                    first_param,
                    "self",
                    NameSource::SelfParam,
                    hints,
                );
            }
            collect_function_expr_hints(&function_decl.func, hints, hir)?;
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            register_binding_hint(
                function,
                local_function_decl.name,
                "fn",
                NameSource::FunctionShape,
                hints,
            );
            collect_local_function_hints(local_function_decl, hints, hir)?;
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {}
    }
    Ok(())
}

fn collect_local_function_hints(
    function_decl: &AstLocalFunctionDecl,
    hints: &mut [FunctionHints],
    hir: &HirModule,
) -> Result<(), NamingError> {
    collect_function_expr_hints(&function_decl.func, hints, hir)
}

fn collect_function_expr_hints(
    function: &AstFunctionExpr,
    hints: &mut [FunctionHints],
    hir: &HirModule,
) -> Result<(), NamingError> {
    ensure_function_exists(hir, function.function)?;
    collect_block_hints(
        function.function,
        &function.body,
        hints,
        LoopContext::default(),
        hir,
    )
}

fn collect_call_hints(
    function: HirProtoRef,
    call: &AstCallKind,
    hints: &mut [FunctionHints],
    hir: &HirModule,
) -> Result<(), NamingError> {
    match call {
        AstCallKind::Call(call) => {
            collect_expr_hints(function, &call.callee, hints, hir)?;
            for arg in &call.args {
                collect_expr_hints(function, arg, hints, hir)?;
            }
        }
        AstCallKind::MethodCall(call) => {
            collect_expr_hints(function, &call.receiver, hints, hir)?;
            for arg in &call.args {
                collect_expr_hints(function, arg, hints, hir)?;
            }
        }
    }
    Ok(())
}

fn collect_lvalue_hints(
    function: HirProtoRef,
    target: &AstLValue,
    hints: &mut [FunctionHints],
    hir: &HirModule,
) -> Result<(), NamingError> {
    match target {
        AstLValue::Name(AstNameRef::SyntheticLocal(local)) => {
            record_synthetic_local(function, *local, hints);
            Ok(())
        }
        AstLValue::Name(_) => Ok(()),
        AstLValue::FieldAccess(access) => collect_expr_hints(function, &access.base, hints, hir),
        AstLValue::IndexAccess(access) => {
            collect_expr_hints(function, &access.base, hints, hir)?;
            collect_expr_hints(function, &access.index, hints, hir)
        }
    }
}

fn collect_expr_hints(
    function: HirProtoRef,
    expr: &AstExpr,
    hints: &mut [FunctionHints],
    hir: &HirModule,
) -> Result<(), NamingError> {
    match expr {
        AstExpr::FieldAccess(access) => collect_expr_hints(function, &access.base, hints, hir),
        AstExpr::IndexAccess(access) => {
            collect_expr_hints(function, &access.base, hints, hir)?;
            collect_expr_hints(function, &access.index, hints, hir)
        }
        AstExpr::Unary(unary) => collect_expr_hints(function, &unary.expr, hints, hir),
        AstExpr::Binary(binary) => {
            collect_expr_hints(function, &binary.lhs, hints, hir)?;
            collect_expr_hints(function, &binary.rhs, hints, hir)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_expr_hints(function, &logical.lhs, hints, hir)?;
            collect_expr_hints(function, &logical.rhs, hints, hir)
        }
        AstExpr::Call(call) => {
            collect_expr_hints(function, &call.callee, hints, hir)?;
            for arg in &call.args {
                collect_expr_hints(function, arg, hints, hir)?;
            }
            Ok(())
        }
        AstExpr::MethodCall(call) => collect_method_call_hints(function, call, hints, hir),
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    AstTableField::Array(value) => collect_expr_hints(function, value, hints, hir)?,
                    AstTableField::Record(record) => {
                        if let AstTableKey::Expr(key) = &record.key {
                            collect_expr_hints(function, key, hints, hir)?;
                        }
                        collect_expr_hints(function, &record.value, hints, hir)?;
                    }
                }
            }
            Ok(())
        }
        AstExpr::FunctionExpr(function_expr) => {
            collect_function_expr_hints(function_expr, hints, hir)
        }
        AstExpr::Var(AstNameRef::SyntheticLocal(local)) => {
            record_synthetic_local(function, *local, hints);
            Ok(())
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => Ok(()),
    }
}

fn collect_method_call_hints(
    function: HirProtoRef,
    call: &AstMethodCallExpr,
    hints: &mut [FunctionHints],
    hir: &HirModule,
) -> Result<(), NamingError> {
    collect_expr_hints(function, &call.receiver, hints, hir)?;
    for arg in &call.args {
        collect_expr_hints(function, arg, hints, hir)?;
    }
    Ok(())
}

fn ensure_function_exists(hir: &HirModule, function: HirProtoRef) -> Result<(), NamingError> {
    if hir.protos.get(function.index()).is_some() {
        Ok(())
    } else {
        Err(NamingError::MissingFunction {
            function: function.index(),
        })
    }
}

fn register_binding_expr_hint(
    function: HirProtoRef,
    binding: AstBindingRef,
    expr: &AstExpr,
    hints: &mut [FunctionHints],
) {
    record_binding_presence(function, binding, hints);
    let Some((candidate, source)) = candidate_from_expr(expr) else {
        return;
    };
    register_binding_hint(function, binding, &candidate, source, hints);
}

fn record_binding_presence(function: HirProtoRef, binding: AstBindingRef, hints: &mut [FunctionHints]) {
    if let AstBindingRef::SyntheticLocal(local) = binding {
        record_synthetic_local(function, local, hints);
    }
}

fn register_binding_hint(
    function: HirProtoRef,
    binding: AstBindingRef,
    candidate: &str,
    source: NameSource,
    hints: &mut [FunctionHints],
) {
    match binding {
        AstBindingRef::Local(local) => {
            register_local_hint(function, local, candidate, source, hints)
        }
        AstBindingRef::SyntheticLocal(local) => {
            register_synthetic_local_hint(function, local, candidate, source, hints)
        }
        AstBindingRef::Temp(_) => unreachable!(
            "readability output must not leak raw temp bindings into naming"
        ),
    }
}

fn register_param_hint(
    function: HirProtoRef,
    param: ParamId,
    candidate: &str,
    source: NameSource,
    hints: &mut [FunctionHints],
) {
    let Some(candidate) = normalize_identifier(candidate) else {
        return;
    };
    let function_hints = &mut hints[function.index()];
    insert_hint(&mut function_hints.param_hints, param, candidate, source);
}

fn register_local_hint(
    function: HirProtoRef,
    local: LocalId,
    candidate: &str,
    source: NameSource,
    hints: &mut [FunctionHints],
) {
    let Some(candidate) = normalize_identifier(candidate) else {
        return;
    };
    let function_hints = &mut hints[function.index()];
    insert_hint(&mut function_hints.local_hints, local, candidate, source);
}

fn register_synthetic_local_hint(
    function: HirProtoRef,
    local: AstSyntheticLocalId,
    candidate: &str,
    source: NameSource,
    hints: &mut [FunctionHints],
) {
    let Some(candidate) = normalize_identifier(candidate) else {
        return;
    };
    let function_hints = &mut hints[function.index()];
    function_hints.synthetic_locals.insert(local);
    insert_hint(
        &mut function_hints.synthetic_local_hints,
        local,
        candidate,
        source,
    );
}

fn record_synthetic_local(function: HirProtoRef, local: AstSyntheticLocalId, hints: &mut [FunctionHints]) {
    hints[function.index()].synthetic_locals.insert(local);
}

fn insert_hint<K>(
    map: &mut BTreeMap<K, CandidateHint>,
    key: K,
    candidate: String,
    source: NameSource,
) where
    K: Ord,
{
    let should_replace = map
        .get(&key)
        .map(|existing| hint_priority(source) > hint_priority(existing.source))
        .unwrap_or(true);
    if should_replace {
        map.insert(
            key,
            CandidateHint {
                text: candidate,
                source,
            },
        );
    }
}

fn hint_priority(source: NameSource) -> usize {
    match source {
        NameSource::Debug => 100,
        NameSource::SelfParam => 90,
        NameSource::LoopRole => 80,
        NameSource::FieldName => 70,
        NameSource::TableShape | NameSource::BoolShape | NameSource::FunctionShape => 60,
        NameSource::ResultShape => 50,
        NameSource::DebugLike | NameSource::Simple | NameSource::ConflictFallback => 10,
    }
}

fn assign_names_for_function(
    proto: &HirProto,
    evidence: &FunctionNamingEvidence,
    hints: &FunctionHints,
    options: NamingOptions,
    module_names: &mut ModuleNameAllocator,
) -> FunctionNameMap {
    let mut used = lua_keywords();
    let params = proto
        .params
        .iter()
        .enumerate()
        .map(|(index, param)| {
            allocate_name(
                module_names.reserve_function_shape_name(
                    choose_param_candidate(proto, *param, index, evidence, hints, options),
                    &used,
                    options.mode,
                ),
                &mut used,
            )
        })
        .collect::<Vec<_>>();
    let locals = proto
        .locals
        .iter()
        .enumerate()
        .map(|(index, local)| {
            allocate_name(
                module_names.reserve_function_shape_name(
                    choose_local_candidate(proto, *local, index, evidence, hints, options),
                    &used,
                    options.mode,
                ),
                &mut used,
            )
        })
        .collect::<Vec<_>>();
    let upvalues = proto
        .upvalues
        .iter()
        .enumerate()
        .map(|(index, upvalue)| {
            allocate_name(
                module_names.reserve_function_shape_name(
                    choose_upvalue_candidate(proto, *upvalue, index, evidence, options),
                    &used,
                    options.mode,
                ),
                &mut used,
            )
        })
        .collect::<Vec<_>>();
    let synthetic_locals = hints
        .synthetic_locals
        .iter()
        .copied()
        .enumerate()
        .map(|(synthetic_order, local)| {
            let info = allocate_name(
                module_names.reserve_function_shape_name(
                    choose_synthetic_local_candidate(
                        proto,
                        local,
                        synthetic_order,
                        evidence,
                        hints,
                        options,
                    ),
                    &used,
                    options.mode,
                ),
                &mut used,
            );
            (local, info)
        })
        .collect::<BTreeMap<_, _>>();

    FunctionNameMap {
        params,
        locals,
        synthetic_locals,
        upvalues,
    }
}

fn choose_param_candidate(
    proto: &HirProto,
    param: ParamId,
    index: usize,
    evidence: &FunctionNamingEvidence,
    hints: &FunctionHints,
    options: NamingOptions,
) -> CandidateHint {
    if options.mode == NamingMode::DebugLike {
        return mode_fallback_candidate(
            options,
            proto.id,
            "p",
            index,
            alphabetical_name(index).unwrap_or_else(|| format!("arg{}", index + 1)),
        );
    }
    if let Some(name) = evidence
        .param_debug_names
        .get(index)
        .and_then(as_valid_name)
    {
        return CandidateHint {
            text: name,
            source: NameSource::Debug,
        };
    }
    if let Some(hint) = hints.param_hints.get(&param) {
        return hint.clone();
    }
    mode_fallback_candidate(
        options,
        proto.id,
        "p",
        index,
        alphabetical_name(index).unwrap_or_else(|| format!("arg{}", index + 1)),
    )
}

fn choose_local_candidate(
    proto: &HirProto,
    local: LocalId,
    index: usize,
    evidence: &FunctionNamingEvidence,
    hints: &FunctionHints,
    options: NamingOptions,
) -> CandidateHint {
    if options.mode == NamingMode::DebugLike {
        return mode_fallback_candidate(options, proto.id, "r", index, "value".to_owned());
    }
    if let Some(name) = evidence
        .local_debug_names
        .get(index)
        .and_then(as_valid_name)
    {
        return CandidateHint {
            text: name,
            source: NameSource::Debug,
        };
    }
    if let Some(hint) = hints.local_hints.get(&local) {
        return hint.clone();
    }
    mode_fallback_candidate(options, proto.id, "l", index, "value".to_owned())
}

fn choose_upvalue_candidate(
    proto: &HirProto,
    _upvalue: UpvalueId,
    index: usize,
    evidence: &FunctionNamingEvidence,
    options: NamingOptions,
) -> CandidateHint {
    if options.mode == NamingMode::DebugLike {
        return mode_fallback_candidate(options, proto.id, "u", index, "up".to_owned());
    }
    if let Some(name) = evidence
        .upvalue_debug_names
        .get(index)
        .and_then(as_valid_name)
    {
        return CandidateHint {
            text: name,
            source: NameSource::Debug,
        };
    }
    mode_fallback_candidate(options, proto.id, "u", index, "up".to_owned())
}

fn choose_synthetic_local_candidate(
    proto: &HirProto,
    local: AstSyntheticLocalId,
    synthetic_order: usize,
    evidence: &FunctionNamingEvidence,
    hints: &FunctionHints,
    options: NamingOptions,
) -> CandidateHint {
    if options.mode == NamingMode::DebugLike {
        // synthetic local 在调试视角里本质上也是“当前函数里的额外局部槽位”，
        // 因此这里让它们和普通 local 共享 `r` 前缀，并排在显式 local 之后连续编号。
        return mode_fallback_candidate(
            options,
            proto.id,
            "r",
            proto.locals.len() + synthetic_order,
            "value".to_owned(),
        );
    }
    let index = local.index();
    if let Some(name) = evidence.temp_debug_names.get(index).and_then(as_valid_name) {
        return CandidateHint {
            text: name,
            source: NameSource::Debug,
        };
    }
    if let Some(hint) = hints.synthetic_local_hints.get(&local) {
        return hint.clone();
    }
    mode_fallback_candidate(options, proto.id, "sl", index, "value".to_owned())
}

fn mode_fallback_candidate(
    options: NamingOptions,
    function: HirProtoRef,
    prefix: &str,
    index: usize,
    simple_base: String,
) -> CandidateHint {
    match options.mode {
        NamingMode::DebugLike => CandidateHint {
            text: debug_like_name(options, function, prefix, index),
            source: NameSource::DebugLike,
        },
        NamingMode::Simple | NamingMode::Heuristic => CandidateHint {
            text: simple_base,
            source: NameSource::Simple,
        },
    }
}

fn debug_like_name(
    options: NamingOptions,
    function: HirProtoRef,
    prefix: &str,
    index: usize,
) -> String {
    if options.debug_like_include_function {
        format!("{prefix}{}_{}", function.index(), index)
    } else {
        format!("{prefix}{index}")
    }
}

fn allocate_name(candidate: CandidateHint, used: &mut BTreeSet<String>) -> NameInfo {
    let base = candidate.text;
    if !used.contains(&base) && !is_lua_keyword(&base) {
        used.insert(base.clone());
        return NameInfo {
            text: base,
            source: candidate.source,
            renamed: false,
        };
    }

    let mut suffix = 2usize;
    loop {
        let renamed = format!("{base}{suffix}");
        if !used.contains(&renamed) && !is_lua_keyword(&renamed) {
            used.insert(renamed.clone());
            return NameInfo {
                text: renamed,
                source: candidate.source,
                renamed: true,
            };
        }
        suffix += 1;
    }
}

fn candidate_from_expr(expr: &AstExpr) -> Option<(String, NameSource)> {
    match expr {
        AstExpr::FieldAccess(access) => {
            Some((normalize_identifier(&access.field)?, NameSource::FieldName))
        }
        AstExpr::IndexAccess(access) => Some((
            normalize_identifier(&candidate_from_index_base(&access.base)?)?,
            NameSource::FieldName,
        )),
        AstExpr::TableConstructor(_) => Some(("tbl".to_owned(), NameSource::TableShape)),
        AstExpr::FunctionExpr(_) => Some(("fn".to_owned(), NameSource::FunctionShape)),
        AstExpr::Call(_) | AstExpr::MethodCall(_) => {
            Some(("result".to_owned(), NameSource::ResultShape))
        }
        AstExpr::Boolean(_)
        | AstExpr::LogicalAnd(_)
        | AstExpr::LogicalOr(_)
        | AstExpr::Unary(_)
        | AstExpr::Binary(_) => Some(("ok".to_owned(), NameSource::BoolShape)),
        AstExpr::Var(AstNameRef::Global(global)) => {
            Some((normalize_identifier(&global.text)?, NameSource::FieldName))
        }
        AstExpr::Nil
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_)
        | AstExpr::VarArg => None,
    }
}

fn candidate_from_index_base(base: &AstExpr) -> Option<String> {
    match base {
        AstExpr::FieldAccess(access) => Some(singularize_field_name(&access.field)),
        AstExpr::IndexAccess(access) => candidate_from_index_base(&access.base),
        AstExpr::Var(AstNameRef::Global(global)) => normalize_identifier(&global.text),
        AstExpr::Var(_) => Some("item".to_owned()),
        _ => None,
    }
}

fn singularize_field_name(field: &str) -> String {
    let singular = if let Some(stem) = field.strip_suffix("ies") {
        format!("{stem}y")
    } else if let Some(stem) = field.strip_suffix("ches") {
        format!("{stem}ch")
    } else if let Some(stem) = field.strip_suffix("shes") {
        format!("{stem}sh")
    } else if let Some(stem) = field.strip_suffix("sses") {
        format!("{stem}ss")
    } else if let Some(stem) = field.strip_suffix("xes") {
        format!("{stem}x")
    } else if field.len() > 1 {
        field.strip_suffix('s').unwrap_or(field).to_owned()
    } else {
        field.to_owned()
    };
    normalize_identifier(&singular).unwrap_or_else(|| "item".to_owned())
}

fn binding_from_name_ref(name: &AstNameRef) -> Option<AstBindingRef> {
    match name {
        AstNameRef::Local(local) => Some(AstBindingRef::Local(*local)),
        AstNameRef::SyntheticLocal(local) => Some(AstBindingRef::SyntheticLocal(*local)),
        AstNameRef::Temp(_) => unreachable!(
            "readability output must not leak raw temp refs into naming"
        ),
        AstNameRef::Param(_) | AstNameRef::Upvalue(_) | AstNameRef::Global(_) => None,
    }
}

fn alphabetical_name(index: usize) -> Option<String> {
    const NAMES: &[&str] = &[
        "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "m", "n", "p", "q", "r", "s", "t",
        "u", "v", "w", "x", "y", "z",
    ];
    NAMES.get(index).map(|name| (*name).to_owned())
}

fn numeric_loop_name(depth: usize) -> &'static str {
    match depth {
        0 => "i",
        1 => "j",
        2 => "k",
        3 => "n",
        _ => "idx",
    }
}

fn as_valid_name(value: &Option<String>) -> Option<String> {
    value.as_deref().and_then(normalize_identifier)
}

fn normalize_identifier(candidate: &str) -> Option<String> {
    if candidate.is_empty() {
        return None;
    }
    if is_valid_identifier(candidate) {
        return Some(candidate.to_owned());
    }

    let mut normalized = String::with_capacity(candidate.len());
    for ch in candidate.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            normalized.push(ch);
        } else if !normalized.ends_with('_') {
            normalized.push('_');
        }
    }

    let normalized = normalized.trim_matches('_');
    if normalized.is_empty() {
        return None;
    }

    let mut result = normalized.to_owned();
    if result
        .chars()
        .next()
        .is_some_and(|first| first.is_ascii_digit())
    {
        result.insert(0, '_');
    }
    if is_valid_identifier(&result) {
        Some(result)
    } else {
        None
    }
}

fn is_valid_identifier(candidate: &str) -> bool {
    let mut chars = candidate.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first.is_ascii_alphabetic() || first == '_') {
        return false;
    }
    chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
}

fn is_lua_keyword(candidate: &str) -> bool {
    matches!(
        candidate,
        "and"
            | "break"
            | "do"
            | "else"
            | "elseif"
            | "end"
            | "false"
            | "for"
            | "function"
            | "goto"
            | "if"
            | "in"
            | "local"
            | "nil"
            | "not"
            | "or"
            | "repeat"
            | "return"
            | "then"
            | "true"
            | "until"
            | "while"
            | "global"
    )
}

fn lua_keywords() -> BTreeSet<String> {
    [
        "and", "break", "do", "else", "elseif", "end", "false", "for", "function", "goto", "if",
        "in", "local", "nil", "not", "or", "repeat", "return", "then", "true", "until", "while",
        "global",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect()
}

fn debug_local_name_for_reg_at_pc(proto: &RawProto, reg: usize, pc: u32) -> Option<String> {
    proto
        .common
        .debug_info
        .common
        .local_vars
        .iter()
        .filter(|local| debug_local_is_active_at_pc(local, pc))
        .nth(reg)
        .map(|local| decode_raw_string(&local.name))
}

fn debug_local_is_active_at_pc(local: &RawLocalVar, pc: u32) -> bool {
    local.start_pc <= pc && pc < local.end_pc
}

fn decode_raw_string(raw: &RawString) -> String {
    raw.text
        .as_ref()
        .map(|text| text.value.clone())
        .unwrap_or_else(|| String::from_utf8_lossy(&raw.bytes).into_owned())
}

#[cfg(test)]
mod tests {
    use crate::ast::{
        AstBindingRef, AstBlock, AstExpr, AstFieldAccess, AstIndexAccess, AstLocalAttr,
        AstLocalBinding, AstLocalDecl, AstModule, AstReturn, AstStmt, AstSyntheticLocalId,
    };
    use crate::hir::{HirModule, HirProto, HirProtoRef, LocalId, ParamId, TempId};
    use crate::parser::{
        ChunkHeader, Dialect, DialectConstPoolExtra, DialectDebugExtra, DialectHeaderExtra,
        DialectProtoExtra, DialectUpvalueExtra, DialectVersion, Endianness, Origin, ProtoLineRange,
        ProtoSignature, RawChunk, RawConstPool, RawConstPoolCommon, RawDebugInfo,
        RawDebugInfoCommon, RawProto, RawProtoCommon, RawUpvalueInfo, RawUpvalueInfoCommon, Span,
    };
    use crate::parser::{
        Lua51ConstPoolExtra, Lua51DebugExtra, Lua51HeaderExtra, Lua51ProtoExtra, Lua51UpvalueExtra,
    };

    use super::{NameSource, NamingMode, NamingOptions, assign_names};

    fn empty_raw_chunk() -> RawChunk {
        let origin = Origin {
            span: Span { offset: 0, size: 0 },
            raw_word: None,
        };
        RawChunk {
            header: ChunkHeader {
                dialect: Dialect::PucLua,
                version: DialectVersion::Lua51,
                format: 0,
                endianness: Endianness::Little,
                integer_size: 4,
                lua_integer_size: None,
                size_t_size: 4,
                instruction_size: 4,
                number_size: 8,
                integral_number: false,
                extra: DialectHeaderExtra::Lua51(Lua51HeaderExtra),
                origin,
            },
            main: RawProto {
                common: RawProtoCommon {
                    source: None,
                    line_range: ProtoLineRange {
                        defined_start: 0,
                        defined_end: 0,
                    },
                    signature: ProtoSignature {
                        num_params: 4,
                        is_vararg: false,
                        has_vararg_param_reg: false,
                        named_vararg_table: false,
                    },
                    frame: crate::parser::ProtoFrameInfo { max_stack_size: 4 },
                    instructions: Vec::new(),
                    constants: RawConstPool {
                        common: RawConstPoolCommon {
                            literals: Vec::new(),
                        },
                        extra: DialectConstPoolExtra::Lua51(Lua51ConstPoolExtra),
                    },
                    upvalues: RawUpvalueInfo {
                        common: RawUpvalueInfoCommon {
                            count: 0,
                            descriptors: Vec::new(),
                        },
                        extra: DialectUpvalueExtra::Lua51(Lua51UpvalueExtra),
                    },
                    debug_info: RawDebugInfo {
                        common: RawDebugInfoCommon {
                            line_info: Vec::new(),
                            local_vars: Vec::new(),
                            upvalue_names: Vec::new(),
                        },
                        extra: DialectDebugExtra::Lua51(Lua51DebugExtra),
                    },
                    children: Vec::new(),
                },
                extra: DialectProtoExtra::Lua51(Lua51ProtoExtra { raw_is_vararg: 0 }),
                origin,
            },
            origin,
        }
    }

    #[test]
    fn heuristic_mode_prefers_field_shape_for_local_chain() {
        let proto = HirProto {
            id: HirProtoRef(0),
            source: None,
            line_range: ProtoLineRange {
                defined_start: 0,
                defined_end: 0,
            },
            signature: ProtoSignature {
                num_params: 4,
                is_vararg: false,
                has_vararg_param_reg: false,
                named_vararg_table: false,
            },
            params: vec![ParamId(0), ParamId(1), ParamId(2), ParamId(3)],
            locals: vec![LocalId(0), LocalId(1)],
            upvalues: Vec::new(),
            temps: Vec::new(),
            temp_debug_locals: Vec::new(),
            body: crate::hir::HirBlock::default(),
            children: Vec::new(),
        };
        let hir = HirModule {
            entry: HirProtoRef(0),
            protos: vec![proto],
        };
        let ast = AstModule {
            entry_function: HirProtoRef(0),
            body: AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: AstBindingRef::Local(LocalId(0)),
                            attr: AstLocalAttr::None,
                        }],
                        values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                            base: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                                base: AstExpr::Var(crate::ast::AstNameRef::Param(ParamId(0))),
                                field: "branches".to_owned(),
                            })),
                            index: AstExpr::Var(crate::ast::AstNameRef::Param(ParamId(1))),
                        }))],
                    })),
                    AstStmt::LocalDecl(Box::new(AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: AstBindingRef::Local(LocalId(1)),
                            attr: AstLocalAttr::None,
                        }],
                        values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                            base: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                                base: AstExpr::Var(crate::ast::AstNameRef::Local(LocalId(0))),
                                field: "items".to_owned(),
                            })),
                            index: AstExpr::Var(crate::ast::AstNameRef::Param(ParamId(2))),
                        }))],
                    })),
                    AstStmt::Return(Box::new(AstReturn {
                        values: vec![AstExpr::Var(crate::ast::AstNameRef::Local(LocalId(1)))],
                    })),
                ],
            },
        };

        let names = assign_names(
            &ast,
            &hir,
            &empty_raw_chunk(),
            NamingOptions {
                mode: NamingMode::Heuristic,
                ..NamingOptions::default()
            },
        )
        .expect("naming should succeed");

        let function = names.function(HirProtoRef(0)).expect("function names");
        assert_eq!(function.locals[0].text, "branch");
        assert_eq!(function.locals[0].source, NameSource::FieldName);
        assert_eq!(function.locals[1].text, "item");
        assert_eq!(function.locals[1].source, NameSource::FieldName);
    }

    #[test]
    fn debug_like_mode_uses_function_qualified_binding_ids() {
        let proto = HirProto {
            id: HirProtoRef(0),
            source: None,
            line_range: ProtoLineRange {
                defined_start: 0,
                defined_end: 0,
            },
            signature: ProtoSignature {
                num_params: 2,
                is_vararg: false,
                has_vararg_param_reg: false,
                named_vararg_table: false,
            },
            params: vec![ParamId(0), ParamId(1)],
            locals: vec![LocalId(0)],
            upvalues: Vec::new(),
            temps: vec![TempId(0)],
            temp_debug_locals: vec![None],
            body: crate::hir::HirBlock::default(),
            children: Vec::new(),
        };
        let hir = HirModule {
            entry: HirProtoRef(0),
            protos: vec![proto],
        };
        let ast = AstModule {
            entry_function: HirProtoRef(0),
            body: AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: AstBindingRef::SyntheticLocal(AstSyntheticLocalId(TempId(0))),
                            attr: AstLocalAttr::None,
                        }],
                        values: vec![AstExpr::Nil],
                    })),
                    AstStmt::Return(Box::new(AstReturn {
                        values: vec![AstExpr::Var(crate::ast::AstNameRef::SyntheticLocal(
                            AstSyntheticLocalId(TempId(0)),
                        ))],
                    })),
                ],
            },
        };

        let names = assign_names(
            &ast,
            &hir,
            &empty_raw_chunk(),
            NamingOptions {
                mode: NamingMode::DebugLike,
                debug_like_include_function: true,
            },
        )
        .expect("naming should succeed");

        let function = names.function(HirProtoRef(0)).expect("function names");
        assert_eq!(function.params[0].text, "p0_0");
        assert_eq!(function.locals[0].text, "r0_0");
        assert_eq!(
            function
                .synthetic_locals
                .get(&AstSyntheticLocalId(TempId(0)))
                .expect("synthetic local names")
                .text,
            "r0_1"
        );
    }
}
