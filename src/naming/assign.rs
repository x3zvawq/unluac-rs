//! 这个文件负责串起 Naming 主流程。
//!
//! Naming 现在已经拆成多个关注点模块：
//! - evidence：从 parser/HIR 收集辅助证据
//! - lexical：从 AST 重建定义点可见域
//! - validate：保证 Readability 已经收敛到 Naming 可消费的边界
//! - hints：从 AST 结构收集稳定 hint
//! - strategy：把证据和 hint 组合成候选名字
//! - allocate：做最终分配与冲突消解
//!
//! 这里刻意只保留 orchestrator，避免再次把所有逻辑重新堆回一个巨型文件。

use crate::ast::AstModule;
use crate::hir::HirModule;

use super::NamingError;
use super::allocate::{FunctionAssignContext, assign_names_for_function};
use super::ast_facts::collect_ast_naming_facts;
use super::common::{FunctionHints, ModuleNameAllocator, NameMap, NamingEvidence, NamingOptions};
use super::evidence::collect_naming_evidence;
use super::hints::collect_function_hints;
use super::lexical::collect_lexical_contexts;
use super::validate::validate_readability_ast;

/// 对外的 Naming 入口。
///
/// 这个 convenience wrapper 内部先收集 evidence 再做分配。
/// 分配核心已经下沉到 `assign_names_with_evidence()`：后者只消费预先构建好的
/// Naming 证据，不再直接碰 parser 原始结构。
pub fn assign_names(
    module: &AstModule,
    hir: &HirModule,
    options: NamingOptions,
) -> Result<NameMap, NamingError> {
    let evidence = collect_naming_evidence(hir)?;
    assign_names_with_evidence(module, hir, &evidence, options)
}

/// Naming 核心入口。
///
/// 这里仍然保留 `HIR`，因为 lexical context、AST facts、readability 验证和 hints
/// 这些结构事实当前都是真实依赖 HIR 的；这比把它们偷偷塞回 evidence 里更诚实。
pub fn assign_names_with_evidence(
    module: &AstModule,
    hir: &HirModule,
    evidence: &NamingEvidence,
    options: NamingOptions,
) -> Result<NameMap, NamingError> {
    let ast_facts = collect_ast_naming_facts(module, hir);
    let lexical_contexts = collect_lexical_contexts(module, hir)?;
    validate_readability_ast(module, module.entry_function, hir)?;

    let mut hints = vec![FunctionHints::default(); hir.protos.len()];
    collect_function_hints(module, hir, &mut hints)?;

    let mut module_names = ModuleNameAllocator::default();
    let mut functions = Vec::with_capacity(hir.protos.len());
    for proto in &hir.protos {
        functions.push(assign_names_for_function(FunctionAssignContext {
            proto,
            evidence: &evidence.functions[proto.id.index()],
            hints: &hints[proto.id.index()],
            ast_facts: &ast_facts.functions[proto.id.index()],
            options,
            lexical: lexical_contexts
                .function(proto.id)
                .expect("lexical contexts should cover every HIR proto"),
            assigned_functions: &functions,
            module_names: &mut module_names,
        })?);
    }

    Ok(NameMap {
        entry_function: module.entry_function,
        mode: options.mode,
        functions,
    })
}

#[cfg(test)]
mod tests;
