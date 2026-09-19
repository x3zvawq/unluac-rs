//! 编排 Naming 的证据收集、候选生成和名字分配。
//!
//! evidence 提供 HIR 捕获来源，lexical/validate 确认 AST 可见域与消费边界，
//! hints/strategy 生成候选，allocate 完成分配和冲突消解。本模块只串联这些阶段，
//! 不重建各 owner 的规则。

use crate::ast::AstModule;
use crate::decompile::{DecompileContext, DecompileError, DecompileState};
use crate::hir::HirModule;

use super::NamingError;
use super::allocate::{FunctionAssignContext, assign_names_for_function};
use super::ast_facts::collect_ast_naming_facts;
use super::common::{
    FunctionHints, ModuleNameAllocator, NameMap, NamingEvidence, NamingMode, NamingOptions,
};
use super::evidence::collect_naming_evidence;
use super::hints::collect_function_hints;
use super::lexical::collect_lexical_contexts;
use super::validate::validate_readability_ast;
use super::visibility::VisibleNames;

/// Naming 阶段入口：从 HIR/Readability 槽位收集证据并写回 NameMap。
pub(crate) fn assign_names(
    state: &mut DecompileState,
    context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    let readability = state.require_readability()?;
    let hir = state.require_hir()?;
    state.naming = Some(assign_name_map(readability, hir, context.options.naming)?);
    Ok(())
}

/// 对外的 Naming 显式事实入口。
///
/// 这个 convenience wrapper 内部先收集 evidence 再做分配。
/// 分配核心消费捕获证据与 HIR 已提取的调试提示，不接触 parser 原始结构。
pub fn assign_name_map(
    module: &AstModule,
    hir: &HirModule,
    options: NamingOptions,
) -> Result<NameMap, NamingError> {
    let evidence = collect_naming_evidence(hir)?;
    assign_names_with_evidence(module, hir, &evidence, options)
}

/// Naming 核心入口。
///
/// `evidence` 必须对应当前 HIR 的捕获身份；debug 提示直接消费传入的 HIR。
/// 入口验证同一只读 AST/HIR 的函数引用；事实收集器消费此边界，不重复验证身份。
pub fn assign_names_with_evidence(
    module: &AstModule,
    hir: &HirModule,
    evidence: &NamingEvidence<'_>,
    options: NamingOptions,
) -> Result<NameMap, NamingError> {
    validate_readability_ast(module, hir)?;
    let mut ast_facts = collect_ast_naming_facts(module, hir);
    // 子函数通过 upvalue 读取的参数仍有用；当前函数 AST 的直接读取并不完整。
    for capture in evidence.functions.iter().flatten() {
        for captured in capture.captures {
            if let crate::hir::HirBinding::Param(param) = captured.binding {
                ast_facts.functions[capture.parent.index()]
                    .used_params
                    .insert(param);
            }
        }
    }
    let lexical_contexts = collect_lexical_contexts(module, hir);

    let mut hints = vec![
        FunctionHints {
            heuristic: options.mode == NamingMode::Heuristic,
            ..FunctionHints::default()
        };
        hir.protos.len()
    ];
    collect_function_hints(module, &mut hints);

    let mut visible_names = VisibleNames::default();
    let mut module_names = ModuleNameAllocator::default();
    let mut functions = Vec::with_capacity(hir.protos.len());
    for proto in &hir.protos {
        let lexical = lexical_contexts
            .function(proto.id)
            .expect("lexical contexts should cover every HIR proto");
        functions.push(assign_names_for_function(FunctionAssignContext {
            proto,
            capture_evidence: evidence.functions[proto.id.index()].as_ref(),
            hints: &hints[proto.id.index()],
            ast_facts: &ast_facts.functions[proto.id.index()],
            module_ast_facts: &ast_facts,
            options,
            visible_names: &visible_names,
            definition_position: lexical.definition_position,
            assigned_functions: &functions,
            module_names: &mut module_names,
        })?);
        visible_names.publish(proto.id, lexical, &functions)?;
    }

    Ok(NameMap {
        entry_function: module.entry_function,
        mode: options.mode,
        functions,
    })
}
