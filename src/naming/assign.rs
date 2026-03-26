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
use crate::parser::RawChunk;

use super::NamingError;
use super::allocate::assign_names_for_function;
use super::common::{FunctionHints, ModuleNameAllocator, NameMap, NamingOptions};
use super::evidence::build_naming_evidence;
use super::hints::collect_function_hints;
use super::lexical::collect_lexical_contexts;
use super::validate::validate_readability_ast;

/// 对外的 Naming 入口。
pub fn assign_names(
    module: &AstModule,
    hir: &HirModule,
    raw: &RawChunk,
    options: NamingOptions,
) -> Result<NameMap, NamingError> {
    let evidence = build_naming_evidence(raw, hir)?;
    let lexical_contexts = collect_lexical_contexts(module, hir)?;
    validate_readability_ast(module, module.entry_function, hir)?;

    let mut hints = vec![FunctionHints::default(); hir.protos.len()];
    collect_function_hints(module, hir, &mut hints)?;

    let mut module_names = ModuleNameAllocator::default();
    let mut functions = Vec::with_capacity(hir.protos.len());
    for proto in &hir.protos {
        functions.push(assign_names_for_function(
            proto,
            &evidence.functions[proto.id.index()],
            &hints[proto.id.index()],
            options,
            lexical_contexts
                .function(proto.id)
                .expect("lexical contexts should cover every HIR proto"),
            &functions,
            &mut module_names,
        )?);
    }

    Ok(NameMap {
        entry_function: module.entry_function,
        mode: options.mode,
        functions,
    })
}

#[cfg(test)]
mod tests;
