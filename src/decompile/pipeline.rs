//! 这个文件实现主反编译 pipeline 的统一入口。
//!
//! 当前只真正接上 parser，但入口已经先按完整阶段序列搭好；
//! 这样后续补层时只需要往这个骨架里填实现，不需要重写调用约定。

use std::collections::BTreeSet;

use crate::ast::{
    AstDialectVersion, AstExpr, AstFeature, AstGlobalAttr, AstLocalAttr, AstModule, AstStmt,
    AstTargetDialect, lower_ast, make_readable_with_options_and_timing,
};
use crate::cfg::{analyze_dataflow, analyze_graph_facts, build_cfg_graph};
use crate::generate::{GenerateMode, generate_chunk};
use crate::hir::analyze_hir_with_timing;
use crate::naming::{assign_names_with_evidence, collect_naming_evidence};
use crate::parser::{
    parse_lua51_chunk, parse_lua52_chunk, parse_lua53_chunk, parse_lua54_chunk, parse_lua55_chunk,
    parse_luajit_chunk, parse_luau_chunk,
};
use crate::structure::analyze_structure;
use crate::timing::{TimingCollector, TimingReport};
use crate::transformer::lower_chunk;

use super::debug::{StageDebugOutput, collect_stage_dump};
use super::error::DecompileError;
use super::options::{DecompileDialect, DecompileOptions};
use super::state::{DecompileStage, DecompileState};

/// 一次主 pipeline 调用的返回值。
#[derive(Debug, Clone, PartialEq)]
pub struct DecompileResult {
    pub state: DecompileState,
    pub debug_output: Vec<StageDebugOutput>,
    pub timing_report: Option<TimingReport>,
}

/// 对外暴露唯一的主入口，统一完成默认值补齐和阶段调度。
pub fn decompile(
    bytes: &[u8],
    options: DecompileOptions,
) -> Result<DecompileResult, DecompileError> {
    DecompilerPipeline.run(bytes, options)
}

struct DecompilerPipeline;

impl DecompilerPipeline {
    fn run(
        self,
        bytes: &[u8],
        options: DecompileOptions,
    ) -> Result<DecompileResult, DecompileError> {
        let options = options.normalized();

        let mut state = DecompileState::new(options.dialect, options.target_stage);
        let mut debug_output = Vec::new();
        let timings = TimingCollector::new(options.debug.enable && options.debug.timing);
        let requested_target = target_ast_dialect(options.dialect);

        state.raw_chunk =
            Some(
                timings.record(DecompileStage::Parse.label(), || match options.dialect {
                    DecompileDialect::Lua51 => parse_lua51_chunk(bytes, options.parse),
                    DecompileDialect::Lua52 => parse_lua52_chunk(bytes, options.parse),
                    DecompileDialect::Lua53 => parse_lua53_chunk(bytes, options.parse),
                    DecompileDialect::Lua54 => parse_lua54_chunk(bytes, options.parse),
                    DecompileDialect::Lua55 => parse_lua55_chunk(bytes, options.parse),
                    DecompileDialect::Luajit => parse_luajit_chunk(bytes, options.parse),
                    DecompileDialect::Luau => parse_luau_chunk(bytes, options.parse),
                })?,
            );
        state.mark_completed(DecompileStage::Parse);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Parse, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Parse {
            return Ok(finish_result(state, debug_output, &timings));
        }

        let raw_chunk = state
            .raw_chunk
            .as_ref()
            .expect("parse stage completed must leave raw_chunk in state");
        state.lowered =
            Some(timings.record(DecompileStage::Transform.label(), || lower_chunk(raw_chunk))?);
        state.mark_completed(DecompileStage::Transform);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Transform, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Transform {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.cfg = Some(timings.record(DecompileStage::Cfg.label(), || {
            let lowered = state
                .lowered
                .as_ref()
                .expect("transform stage completed must leave lowered in state");
            build_cfg_graph(lowered)
        }));
        state.mark_completed(DecompileStage::Cfg);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Cfg, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Cfg {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.graph_facts = Some(timings.record(DecompileStage::GraphFacts.label(), || {
            let cfg_graph = state
                .cfg
                .as_ref()
                .expect("cfg stage completed must leave cfg graph in state");
            analyze_graph_facts(cfg_graph)
        }));
        state.mark_completed(DecompileStage::GraphFacts);

        if let Some(output) =
            collect_stage_dump(&state, DecompileStage::GraphFacts, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::GraphFacts {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.dataflow = Some(timings.record(DecompileStage::Dataflow.label(), || {
            let lowered = state
                .lowered
                .as_ref()
                .expect("transform stage completed must leave lowered in state");
            let cfg_graph = state
                .cfg
                .as_ref()
                .expect("cfg stage completed must leave cfg graph in state");
            let graph_facts = state
                .graph_facts
                .as_ref()
                .expect("graph facts stage completed must leave graph facts in state");
            analyze_dataflow(lowered, cfg_graph, graph_facts)
        }));
        state.mark_completed(DecompileStage::Dataflow);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Dataflow, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Dataflow {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.structure_facts =
            Some(timings.record(DecompileStage::StructureFacts.label(), || {
                let lowered = state
                    .lowered
                    .as_ref()
                    .expect("transform stage completed must leave lowered in state");
                let cfg_graph = state
                    .cfg
                    .as_ref()
                    .expect("cfg stage completed must leave cfg graph in state");
                let graph_facts = state
                    .graph_facts
                    .as_ref()
                    .expect("graph facts stage completed must leave graph facts in state");
                let dataflow = state
                    .dataflow
                    .as_ref()
                    .expect("dataflow stage completed must leave dataflow in state");
                analyze_structure(lowered, cfg_graph, graph_facts, dataflow)
            }));
        state.mark_completed(DecompileStage::StructureFacts);

        if let Some(output) =
            collect_stage_dump(&state, DecompileStage::StructureFacts, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::StructureFacts {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.hir = Some(timings.record(DecompileStage::Hir.label(), || {
            let lowered = state
                .lowered
                .as_ref()
                .expect("transform stage completed must leave lowered in state");
            let cfg_graph = state
                .cfg
                .as_ref()
                .expect("cfg stage completed must leave cfg graph in state");
            let graph_facts = state
                .graph_facts
                .as_ref()
                .expect("graph facts stage completed must leave graph facts in state");
            let dataflow = state
                .dataflow
                .as_ref()
                .expect("dataflow stage completed must leave dataflow in state");
            let structure_facts = state
                .structure_facts
                .as_ref()
                .expect("structure stage completed must leave structure facts in state");
            analyze_hir_with_timing(
                lowered,
                cfg_graph,
                graph_facts,
                dataflow,
                structure_facts,
                &timings,
                options.readability,
            )
        }));
        state.mark_completed(DecompileStage::Hir);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Hir, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Hir {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.ast = Some(timings.record(DecompileStage::Ast.label(), || {
            let hir = state
                .hir
                .as_ref()
                .expect("hir stage completed must leave hir module in state");
            lower_ast(hir, ast_lowering_target(requested_target, options.generate.mode))
        })?);
        state.mark_completed(DecompileStage::Ast);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Ast, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Ast {
            return Ok(finish_result(state, debug_output, &timings));
        }

        let output_plan = timings.record(DecompileStage::Readability.label(), || {
            let ast = state
                .ast
                .as_ref()
                .expect("ast stage completed must leave ast module in state");
            resolve_output_plan(
                ast,
                requested_target,
                options.readability,
                options.generate.mode,
                &timings,
            )
        });
        let output_target = output_plan.target;
        let output_generate_mode = output_plan.generate_mode;
        let output_warnings = output_plan.warnings;
        state.readability = Some(output_plan.readability);
        state.mark_completed(DecompileStage::Readability);

        if let Some(output) =
            collect_stage_dump(&state, DecompileStage::Readability, &options.debug)?
        {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Readability {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.naming = Some(timings.record(DecompileStage::Naming.label(), || {
            let ast = state
                .readability
                .as_ref()
                .expect("readability stage completed must leave readability result in state");
            let hir = state
                .hir
                .as_ref()
                .expect("hir stage completed must leave hir module in state");
            let raw_chunk = state
                .raw_chunk
                .as_ref()
                .expect("parse stage completed must leave raw chunk in state");
            let evidence = timings.record("collect-evidence", || {
                collect_naming_evidence(raw_chunk, hir)
            })?;
            assign_names_with_evidence(ast, hir, &evidence, options.naming)
        })?);
        state.mark_completed(DecompileStage::Naming);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Naming, &options.debug)? {
            debug_output.push(output);
        }

        if options.target_stage == DecompileStage::Naming {
            return Ok(finish_result(state, debug_output, &timings));
        }

        state.generated = Some(timings.record(DecompileStage::Generate.label(), || {
            let ast = state
                .readability
                .as_ref()
                .expect("readability stage completed must leave readability result in state");
            let names = state
                .naming
                .as_ref()
                .expect("naming stage completed must leave name map in state");
            let mut generate_options = options.generate;
            generate_options.mode = output_generate_mode;
            let mut generated = generate_chunk(
                ast,
                names,
                output_target,
                generate_options,
            )?;
            generated.warnings = output_warnings.clone();
            Ok::<_, crate::generate::GenerateError>(generated)
        })?);
        state.mark_completed(DecompileStage::Generate);

        if let Some(output) = collect_stage_dump(&state, DecompileStage::Generate, &options.debug)?
        {
            debug_output.push(output);
        }

        Ok(finish_result(state, debug_output, &timings))
    }
}

fn finish_result(
    state: DecompileState,
    debug_output: Vec<StageDebugOutput>,
    timings: &TimingCollector,
) -> DecompileResult {
    DecompileResult {
        state,
        debug_output,
        timing_report: timings.finish(),
    }
}

#[derive(Debug, Clone)]
struct OutputPlan {
    readability: AstModule,
    target: AstTargetDialect,
    generate_mode: GenerateMode,
    warnings: Vec<String>,
}

fn resolve_output_plan(
    ast: &AstModule,
    requested_target: AstTargetDialect,
    readability_options: crate::readability::ReadabilityOptions,
    mode: GenerateMode,
    timings: &TimingCollector,
) -> OutputPlan {
    match mode {
        GenerateMode::Strict => OutputPlan {
            readability: make_readable_with_options_and_timing(
                ast,
                requested_target,
                readability_options,
                timings,
            ),
            target: requested_target,
            generate_mode: GenerateMode::Strict,
            warnings: Vec::new(),
        },
        GenerateMode::Permissive => {
            let readability = make_readable_with_options_and_timing(
                ast,
                requested_target,
                readability_options,
                timings,
            );
            let unsupported = unsupported_ast_features(&readability, requested_target);
            let warnings = if unsupported.is_empty() {
                Vec::new()
            } else {
                vec![format!(
                    "requested target dialect `{}` does not support feature(s) {}; emitting permissive output.",
                    requested_target.version,
                    format_ast_features(&unsupported)
                )]
            };
            OutputPlan {
                readability,
                target: requested_target,
                generate_mode: GenerateMode::Permissive,
                warnings,
            }
        }
        GenerateMode::BestEffort => {
            let mut target =
                choose_best_effort_target(requested_target.version, &collect_ast_features(ast))
                    .unwrap_or(requested_target);

            loop {
                let readability = make_readable_with_options_and_timing(
                    ast,
                    target,
                    readability_options,
                    timings,
                );
                let unsupported_in_target = unsupported_ast_features(&readability, target);
                if unsupported_in_target.is_empty() {
                    let unsupported_in_requested =
                        unsupported_ast_features(&readability, requested_target);
                    let warnings = if target.version != requested_target.version
                        && !unsupported_in_requested.is_empty()
                    {
                        vec![format!(
                            "upgraded output dialect from `{}` to `{}` to support feature(s) {}.",
                            requested_target.version,
                            target.version,
                            format_ast_features(&unsupported_in_requested)
                        )]
                    } else {
                        Vec::new()
                    };
                    return OutputPlan {
                        readability,
                        target,
                        generate_mode: GenerateMode::Strict,
                        warnings,
                    };
                }

                let final_features = collect_ast_features(&readability);
                let Some(upgraded) =
                    choose_best_effort_target(requested_target.version, &final_features)
                else {
                    let mut warnings = Vec::new();
                    let unsupported_in_requested =
                        unsupported_ast_features(&readability, requested_target);
                    if target.version != requested_target.version
                        && !unsupported_in_requested.is_empty()
                    {
                        warnings.push(format!(
                            "upgraded output dialect from `{}` to `{}` to support feature(s) {}.",
                            requested_target.version,
                            target.version,
                            format_ast_features(&unsupported_in_requested)
                        ));
                    }
                    warnings.push(format!(
                        "no single supported target dialect can express feature(s) {}; emitting permissive output.",
                        format_ast_features(&final_features)
                    ));
                    return OutputPlan {
                        readability,
                        target,
                        generate_mode: GenerateMode::Permissive,
                        warnings,
                    };
                };

                if upgraded == target {
                    let unsupported_in_requested =
                        unsupported_ast_features(&readability, requested_target);
                    let mut warnings = Vec::new();
                    if !unsupported_in_requested.is_empty() {
                        warnings.push(format!(
                            "requested target dialect `{}` does not support feature(s) {}; emitting permissive output.",
                            requested_target.version,
                            format_ast_features(&unsupported_in_requested)
                        ));
                    }
                    return OutputPlan {
                        readability,
                        target,
                        generate_mode: GenerateMode::Permissive,
                        warnings,
                    };
                }

                target = upgraded;
            }
        }
    }
}

fn collect_ast_features(module: &AstModule) -> BTreeSet<AstFeature> {
    let mut features = BTreeSet::new();
    collect_block_features(&module.body, &mut features);
    features
}

fn collect_block_features(block: &crate::ast::AstBlock, features: &mut BTreeSet<AstFeature>) {
    for stmt in &block.stmts {
        collect_stmt_features(stmt, features);
    }
}

fn collect_stmt_features(stmt: &AstStmt, features: &mut BTreeSet<AstFeature>) {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            for binding in &local_decl.bindings {
                match binding.attr {
                    AstLocalAttr::Const => {
                        features.insert(AstFeature::LocalConst);
                    }
                    AstLocalAttr::Close => {
                        features.insert(AstFeature::LocalClose);
                    }
                    AstLocalAttr::None => {}
                }
            }
            for value in &local_decl.values {
                collect_expr_features(value, features);
            }
        }
        AstStmt::GlobalDecl(global_decl) => {
            features.insert(AstFeature::GlobalDecl);
            for binding in &global_decl.bindings {
                if binding.attr == AstGlobalAttr::Const {
                    features.insert(AstFeature::GlobalConst);
                }
            }
            for value in &global_decl.values {
                collect_expr_features(value, features);
            }
        }
        AstStmt::Assign(assign) => {
            for target in &assign.targets {
                collect_lvalue_features(target, features);
            }
            for value in &assign.values {
                collect_expr_features(value, features);
            }
        }
        AstStmt::CallStmt(call_stmt) => collect_call_kind_features(&call_stmt.call, features),
        AstStmt::Return(ret) => {
            for value in &ret.values {
                collect_expr_features(value, features);
            }
        }
        AstStmt::If(ast_if) => {
            collect_expr_features(&ast_if.cond, features);
            collect_block_features(&ast_if.then_block, features);
            if let Some(else_block) = &ast_if.else_block {
                collect_block_features(else_block, features);
            }
        }
        AstStmt::While(ast_while) => {
            collect_expr_features(&ast_while.cond, features);
            collect_block_features(&ast_while.body, features);
        }
        AstStmt::Repeat(ast_repeat) => {
            collect_block_features(&ast_repeat.body, features);
            collect_expr_features(&ast_repeat.cond, features);
        }
        AstStmt::NumericFor(numeric_for) => {
            collect_expr_features(&numeric_for.start, features);
            collect_expr_features(&numeric_for.limit, features);
            collect_expr_features(&numeric_for.step, features);
            collect_block_features(&numeric_for.body, features);
        }
        AstStmt::GenericFor(generic_for) => {
            for expr in &generic_for.iterator {
                collect_expr_features(expr, features);
            }
            collect_block_features(&generic_for.body, features);
        }
        AstStmt::Continue => {
            features.insert(AstFeature::ContinueStmt);
        }
        AstStmt::Goto(_) | AstStmt::Label(_) => {
            features.insert(AstFeature::GotoLabel);
        }
        AstStmt::DoBlock(block) => collect_block_features(block, features),
        AstStmt::FunctionDecl(function_decl) => {
            collect_block_features(&function_decl.func.body, features);
        }
        AstStmt::LocalFunctionDecl(local_function_decl) => {
            collect_block_features(&local_function_decl.func.body, features);
        }
        AstStmt::Break => {}
    }
}

fn collect_lvalue_features(
    lvalue: &crate::ast::AstLValue,
    features: &mut BTreeSet<AstFeature>,
) {
    match lvalue {
        crate::ast::AstLValue::Name(_) => {}
        crate::ast::AstLValue::FieldAccess(access) => {
            collect_expr_features(&access.base, features);
        }
        crate::ast::AstLValue::IndexAccess(access) => {
            collect_expr_features(&access.base, features);
            collect_expr_features(&access.index, features);
        }
    }
}

fn collect_expr_features(expr: &AstExpr, features: &mut BTreeSet<AstFeature>) {
    match expr {
        AstExpr::FieldAccess(access) => collect_expr_features(&access.base, features),
        AstExpr::IndexAccess(access) => {
            collect_expr_features(&access.base, features);
            collect_expr_features(&access.index, features);
        }
        AstExpr::Unary(unary) => collect_expr_features(&unary.expr, features),
        AstExpr::Binary(binary) => {
            collect_expr_features(&binary.lhs, features);
            collect_expr_features(&binary.rhs, features);
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            collect_expr_features(&logical.lhs, features);
            collect_expr_features(&logical.rhs, features);
        }
        AstExpr::Call(call) => collect_call_expr_features(call, features),
        AstExpr::MethodCall(call) => collect_method_call_expr_features(call, features),
        AstExpr::SingleValue(inner) => collect_expr_features(inner, features),
        AstExpr::TableConstructor(table) => {
            for field in &table.fields {
                match field {
                    crate::ast::AstTableField::Array(value) => {
                        collect_expr_features(value, features);
                    }
                    crate::ast::AstTableField::Record(record) => {
                        if let crate::ast::AstTableKey::Expr(key) = &record.key {
                            collect_expr_features(key, features);
                        }
                        collect_expr_features(&record.value, features);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(function) => collect_block_features(&function.body, features),
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg => {}
    }
}

fn collect_call_kind_features(
    call: &crate::ast::AstCallKind,
    features: &mut BTreeSet<AstFeature>,
) {
    match call {
        crate::ast::AstCallKind::Call(call) => collect_call_expr_features(call, features),
        crate::ast::AstCallKind::MethodCall(call) => {
            collect_method_call_expr_features(call, features)
        }
    }
}

fn collect_call_expr_features(
    call: &crate::ast::AstCallExpr,
    features: &mut BTreeSet<AstFeature>,
) {
    collect_expr_features(&call.callee, features);
    for arg in &call.args {
        collect_expr_features(arg, features);
    }
}

fn collect_method_call_expr_features(
    call: &crate::ast::AstMethodCallExpr,
    features: &mut BTreeSet<AstFeature>,
) {
    collect_expr_features(&call.receiver, features);
    for arg in &call.args {
        collect_expr_features(arg, features);
    }
}

fn unsupported_ast_features(
    module: &AstModule,
    target: AstTargetDialect,
) -> BTreeSet<AstFeature> {
    collect_ast_features(module)
        .into_iter()
        .filter(|feature| !target.supports_feature(*feature))
        .collect()
}

fn choose_best_effort_target(
    requested: AstDialectVersion,
    features: &BTreeSet<AstFeature>,
) -> Option<AstTargetDialect> {
    candidate_output_versions(requested)
        .into_iter()
        .map(AstTargetDialect::new)
        .find(|target| features.iter().all(|feature| target.supports_feature(*feature)))
}

fn candidate_output_versions(requested: AstDialectVersion) -> Vec<AstDialectVersion> {
    match requested {
        AstDialectVersion::Lua51 => vec![
            AstDialectVersion::Lua51,
            AstDialectVersion::Lua52,
            AstDialectVersion::Lua53,
            AstDialectVersion::Lua54,
            AstDialectVersion::Lua55,
            AstDialectVersion::LuaJit,
            AstDialectVersion::Luau,
        ],
        AstDialectVersion::Lua52 => vec![
            AstDialectVersion::Lua52,
            AstDialectVersion::Lua53,
            AstDialectVersion::Lua54,
            AstDialectVersion::Lua55,
            AstDialectVersion::LuaJit,
            AstDialectVersion::Luau,
        ],
        AstDialectVersion::Lua53 => vec![
            AstDialectVersion::Lua53,
            AstDialectVersion::Lua54,
            AstDialectVersion::Lua55,
            AstDialectVersion::LuaJit,
            AstDialectVersion::Luau,
        ],
        AstDialectVersion::Lua54 => vec![
            AstDialectVersion::Lua54,
            AstDialectVersion::Lua55,
            AstDialectVersion::LuaJit,
            AstDialectVersion::Luau,
        ],
        AstDialectVersion::Lua55 => vec![
            AstDialectVersion::Lua55,
            AstDialectVersion::LuaJit,
            AstDialectVersion::Luau,
        ],
        AstDialectVersion::LuaJit => vec![
            AstDialectVersion::LuaJit,
            AstDialectVersion::Lua52,
            AstDialectVersion::Lua53,
            AstDialectVersion::Lua54,
            AstDialectVersion::Lua55,
            AstDialectVersion::Luau,
        ],
        AstDialectVersion::Luau => vec![
            AstDialectVersion::Luau,
            AstDialectVersion::Lua52,
            AstDialectVersion::Lua53,
            AstDialectVersion::Lua54,
            AstDialectVersion::Lua55,
            AstDialectVersion::LuaJit,
        ],
    }
}

fn format_ast_features(features: &BTreeSet<AstFeature>) -> String {
    features
        .iter()
        .map(|feature| feature.label())
        .collect::<Vec<_>>()
        .join(", ")
}

fn target_ast_dialect(dialect: DecompileDialect) -> AstTargetDialect {
    let version = match dialect {
        DecompileDialect::Lua51 => AstDialectVersion::Lua51,
        DecompileDialect::Lua52 => AstDialectVersion::Lua52,
        DecompileDialect::Lua53 => AstDialectVersion::Lua53,
        DecompileDialect::Lua54 => AstDialectVersion::Lua54,
        DecompileDialect::Lua55 => AstDialectVersion::Lua55,
        DecompileDialect::Luajit => AstDialectVersion::LuaJit,
        DecompileDialect::Luau => AstDialectVersion::Luau,
    };
    AstTargetDialect::new(version)
}

fn ast_lowering_target(target: AstTargetDialect, mode: GenerateMode) -> AstTargetDialect {
    if mode == GenerateMode::Strict {
        target
    } else {
        AstTargetDialect::relaxed_for_lowering(target.version)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{AstBlock, AstGoto, AstLabel, AstLabelId, AstWhile};
    use crate::hir::HirProtoRef;

    fn module_with_stmts(stmts: Vec<AstStmt>) -> AstModule {
        AstModule {
            entry_function: HirProtoRef(0),
            body: AstBlock { stmts },
        }
    }

    #[test]
    fn best_effort_should_upgrade_lua51_goto_to_lua52() {
        let label = AstLabelId(1);
        let module = module_with_stmts(vec![
            AstStmt::Goto(Box::new(AstGoto { target: label })),
            AstStmt::Label(Box::new(AstLabel { id: label })),
        ]);

        let plan = resolve_output_plan(
            &module,
            AstTargetDialect::new(AstDialectVersion::Lua51),
            crate::readability::ReadabilityOptions::default(),
            GenerateMode::BestEffort,
            &TimingCollector::disabled(),
        );

        assert_eq!(plan.target.version, AstDialectVersion::Lua52);
        assert_eq!(plan.generate_mode, GenerateMode::Strict);
        assert!(unsupported_ast_features(&plan.readability, plan.target).is_empty());
        assert_eq!(plan.warnings.len(), 1);
    }

    #[test]
    fn best_effort_should_fall_back_to_permissive_when_no_single_dialect_fits() {
        let label = AstLabelId(1);
        let module = module_with_stmts(vec![
            AstStmt::While(Box::new(AstWhile {
                cond: AstExpr::Boolean(true),
                body: AstBlock {
                    stmts: vec![AstStmt::Continue],
                },
            })),
            AstStmt::Goto(Box::new(AstGoto { target: label })),
            AstStmt::Label(Box::new(AstLabel { id: label })),
        ]);

        let plan = resolve_output_plan(
            &module,
            AstTargetDialect::new(AstDialectVersion::Lua51),
            crate::readability::ReadabilityOptions::default(),
            GenerateMode::BestEffort,
            &TimingCollector::disabled(),
        );

        assert_eq!(plan.generate_mode, GenerateMode::Permissive);
        assert!(!plan.warnings.is_empty());
    }
}
