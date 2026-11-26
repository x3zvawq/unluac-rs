//! 编排 Naming 的证据收集、候选生成和名字分配。
//!
//! evidence 提供 AST 捕获来源，lexical/validate 确认 AST 可见域与消费边界，
//! hints/strategy 生成候选，allocate 完成分配和冲突消解。本模块只串联这些阶段，
//! 不重建各 owner 的规则。

use crate::ast::{AstCaptureBinding, AstModule};

use super::NamingError;
use super::allocate::{FunctionAssignContext, assign_names_for_function};
use super::ast_facts::collect_ast_naming_facts;
use super::common::{
    FunctionHints, ModuleNameAllocator, NameMap, NamingEvidence, NamingMode, NamingOptions,
};
use super::evidence::collect_naming_evidence;
use super::hints::collect_function_hints;
use super::lexical::collect_lexical_contexts;
use super::validate::validate_ast;
use super::visibility::VisibleNames;

/// 对外的 Naming 显式事实入口。
pub fn assign_name_map(
    module: &AstModule,
    options: NamingOptions,
) -> Result<NameMap, NamingError> {
    let evidence = collect_naming_evidence(module)?;
    assign_names_with_evidence(module, &evidence, options)
}

/// Naming 核心入口。
pub fn assign_names_with_evidence(
    module: &AstModule,
    evidence: &NamingEvidence<'_>,
    options: NamingOptions,
) -> Result<NameMap, NamingError> {
    validate_ast(module)?;
    let mut ast_facts = collect_ast_naming_facts(module);
    // 子函数通过 upvalue 读取的参数和局部仍有用；当前函数 AST 的直接读取并不完整。
    for capture in evidence.functions.iter().flatten() {
        for captured in capture.captures {
            match captured.binding {
                AstCaptureBinding::Param(param) => {
                    ast_facts.functions[capture.parent.index()]
                        .used_params
                        .insert(param);
                }
                AstCaptureBinding::Local(local) => {
                    ast_facts.functions[capture.parent.index()]
                        .mentioned_bindings
                        .insert(crate::ast::AstBindingRef::Local(local));
                }
                AstCaptureBinding::SyntheticLocal(local) => {
                    ast_facts.functions[capture.parent.index()]
                        .mentioned_bindings
                        .insert(crate::ast::AstBindingRef::SyntheticLocal(local));
                }
                AstCaptureBinding::Upvalue(_) => {}
            }
        }
    }
    let lexical_contexts = collect_lexical_contexts(module);

    let mut hints = vec![
        FunctionHints {
            heuristic: options.mode == NamingMode::Heuristic,
            ..FunctionHints::default()
        };
        module.protos.len()
    ];
    collect_function_hints(module, &mut hints);

    // 为最终 AST 中实际可达的函数分配稠密 debug-like 编号，跳过 Luau `-O2` 内联遗留的死 proto 槽，
    // 防止重编译消除死 proto 后引发无意义的 `p4_0 -> p3_0` 编号漂移。
    let mut live_proto_indices = vec![0usize; module.protos.len()];
    let mut next_live_proto = 0usize;
    for (idx, func_facts) in ast_facts.functions.iter().enumerate() {
        if func_facts.is_reachable() {
            live_proto_indices[idx] = next_live_proto;
            next_live_proto += 1;
        } else {
            live_proto_indices[idx] = idx;
        }
    }

    let mut visible_names = VisibleNames::default();
    let mut module_names = ModuleNameAllocator::default();
    let mut functions = Vec::with_capacity(module.protos.len());
    for proto in &module.protos {
        let lexical = lexical_contexts
            .function(proto.id)
            .expect("lexical contexts should cover every AST proto");
        functions.push(assign_names_for_function(FunctionAssignContext {
            proto,
            debug_like_function_index: live_proto_indices[proto.id.index()],
            capture_evidence: evidence.functions[proto.id.index()].as_ref(),
            hints: &hints[proto.id.index()],
            ast_facts: &ast_facts.functions[proto.id.index()],
            module_ast_facts: &ast_facts,
            target_dialect: module.target_dialect,
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
