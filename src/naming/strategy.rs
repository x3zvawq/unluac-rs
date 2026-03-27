//! 这个文件负责把 evidence/hints 组合成具体候选名字。
//!
//! 这里还不做最终冲突消解，只回答“这个槽位现在最像什么名字”。
//! 真正的唯一化和祖先作用域避让由 allocation 阶段完成。

use std::collections::BTreeSet;

use crate::ast::AstSyntheticLocalId;
use crate::hir::{HirProto, HirProtoRef, LocalId, ParamId, UpvalueId};

use super::NamingError;
use super::ast_facts::FunctionAstNamingFacts;
use super::common::{
    CandidateHint, CapturedBinding, FunctionHints, FunctionNameMap, FunctionNamingEvidence,
    NameSource, NamingMode, NamingOptions,
};
use super::lexical::{FunctionLexicalContext, VisibleBinding};
use super::support::{alphabetical_name, as_valid_name};

/// 计算函数定义点外层当前可见绑定对应的最终名字。
pub(super) fn resolve_outer_visible_names(
    function: HirProtoRef,
    lexical: &FunctionLexicalContext,
    assigned_functions: &[FunctionNameMap],
) -> Result<BTreeSet<String>, NamingError> {
    let mut names = BTreeSet::new();
    for &binding in &lexical.outer_visible_bindings {
        names.insert(resolve_visible_binding_name(
            function,
            binding,
            assigned_functions,
        )?);
    }
    Ok(names)
}

/// 选择参数候选名。
pub(super) fn choose_param_candidate(
    proto: &HirProto,
    param: ParamId,
    index: usize,
    evidence: &FunctionNamingEvidence,
    hints: &FunctionHints,
    options: NamingOptions,
) -> CandidateHint {
    if let Some(hint) = hints.param_hints.get(&param)
        && hint.source == NameSource::SelfParam
    {
        return hint.clone();
    }
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

/// 选择 local 候选名。
pub(super) fn choose_local_candidate(
    proto: &HirProto,
    local: LocalId,
    index: usize,
    evidence: &FunctionNamingEvidence,
    hints: &FunctionHints,
    ast_facts: &FunctionAstNamingFacts,
    options: NamingOptions,
) -> CandidateHint {
    if options.mode == NamingMode::DebugLike {
        let visible_count = ast_facts.debug_like_binding_order.len();
        return mode_fallback_candidate(
            options,
            proto.id,
            "r",
            debug_like_binding_index(ast_facts, crate::ast::AstBindingRef::Local(local))
                .unwrap_or(visible_count + index),
            "value".to_owned(),
        );
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

/// 选择 upvalue 候选名。
pub(super) fn choose_upvalue_candidate(
    proto: &HirProto,
    index: usize,
    evidence: &FunctionNamingEvidence,
    options: NamingOptions,
    assigned_functions: &[FunctionNameMap],
) -> Result<CandidateHint, NamingError> {
    if let Some(capture) = evidence
        .upvalue_capture_sources
        .get(index)
        .and_then(|capture| *capture)
    {
        // upvalue 不是一个“重新发明名字”的槽位：只要我们知道它捕获自哪个父绑定，
        // 就应该沿用那个绑定在父作用域里已经稳定下来的名字。
        return resolve_captured_name(proto.id, capture, assigned_functions);
    }
    if options.mode == NamingMode::DebugLike {
        return Ok(mode_fallback_candidate(
            options,
            proto.id,
            "u",
            index,
            "up".to_owned(),
        ));
    }
    if let Some(name) = evidence
        .upvalue_debug_names
        .get(index)
        .and_then(as_valid_name)
    {
        return Ok(CandidateHint {
            text: name,
            source: NameSource::Debug,
        });
    }
    Ok(mode_fallback_candidate(
        options,
        proto.id,
        "u",
        index,
        "up".to_owned(),
    ))
}

/// 选择 synthetic local 候选名。
pub(super) fn choose_synthetic_local_candidate(
    proto: &HirProto,
    local: AstSyntheticLocalId,
    synthetic_order: usize,
    evidence: &FunctionNamingEvidence,
    hints: &FunctionHints,
    ast_facts: &FunctionAstNamingFacts,
    options: NamingOptions,
) -> CandidateHint {
    if options.mode == NamingMode::DebugLike {
        let visible_count = ast_facts.debug_like_binding_order.len();
        return mode_fallback_candidate(
            options,
            proto.id,
            "r",
            debug_like_binding_index(ast_facts, crate::ast::AstBindingRef::SyntheticLocal(local))
                .unwrap_or(visible_count + proto.locals.len() + synthetic_order),
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
    if ast_facts.unused_synthetic_locals.contains(&local) {
        return CandidateHint {
            text: "_".to_owned(),
            source: NameSource::Discard,
        };
    }
    if let Some(hint) = hints.synthetic_local_hints.get(&local) {
        return hint.clone();
    }
    mode_fallback_candidate(options, proto.id, "sl", index, "value".to_owned())
}

fn debug_like_binding_index(
    ast_facts: &FunctionAstNamingFacts,
    binding: crate::ast::AstBindingRef,
) -> Option<usize> {
    ast_facts.debug_like_binding_order.get(&binding).copied()
}

fn resolve_visible_binding_name(
    function: HirProtoRef,
    binding: VisibleBinding,
    assigned_functions: &[FunctionNameMap],
) -> Result<String, NamingError> {
    match binding {
        VisibleBinding::Param {
            function: parent,
            param,
        } => resolve_captured_param_name(function, parent, param, assigned_functions),
        VisibleBinding::Local {
            function: parent,
            local,
        } => resolve_captured_local_name(function, parent, local, assigned_functions),
        VisibleBinding::SyntheticLocal {
            function: parent,
            local,
        } => {
            let parent_names = assigned_functions.get(parent.index()).ok_or(
                NamingError::MissingCaptureParent {
                    function: function.index(),
                    parent: parent.index(),
                },
            )?;
            parent_names
                .synthetic_locals
                .get(&local)
                .map(|name| name.text.clone())
                .ok_or(NamingError::MissingCapturedBinding {
                    function: function.index(),
                    parent: parent.index(),
                    kind: "synthetic-local",
                    index: local.index(),
                })
        }
        VisibleBinding::Upvalue {
            function: parent,
            upvalue,
        } => resolve_captured_upvalue_name(function, parent, upvalue, assigned_functions),
    }
}

fn resolve_captured_name(
    function: HirProtoRef,
    capture: CapturedBinding,
    assigned_functions: &[FunctionNameMap],
) -> Result<CandidateHint, NamingError> {
    let text = match capture {
        CapturedBinding::Param { parent, param } => {
            resolve_captured_param_name(function, parent, param, assigned_functions)?
        }
        CapturedBinding::Local { parent, local } => {
            resolve_captured_local_name(function, parent, local, assigned_functions)?
        }
        CapturedBinding::Upvalue { parent, upvalue } => {
            resolve_captured_upvalue_name(function, parent, upvalue, assigned_functions)?
        }
    };
    Ok(CandidateHint {
        text,
        source: NameSource::CaptureProvenance,
    })
}

fn resolve_captured_param_name(
    function: HirProtoRef,
    parent: HirProtoRef,
    param: ParamId,
    assigned_functions: &[FunctionNameMap],
) -> Result<String, NamingError> {
    let parent_names =
        assigned_functions
            .get(parent.index())
            .ok_or(NamingError::MissingCaptureParent {
                function: function.index(),
                parent: parent.index(),
            })?;
    parent_names
        .params
        .get(param.index())
        .map(|name| name.text.clone())
        .ok_or(NamingError::MissingCapturedBinding {
            function: function.index(),
            parent: parent.index(),
            kind: "param",
            index: param.index(),
        })
}

fn resolve_captured_local_name(
    function: HirProtoRef,
    parent: HirProtoRef,
    local: LocalId,
    assigned_functions: &[FunctionNameMap],
) -> Result<String, NamingError> {
    let parent_names =
        assigned_functions
            .get(parent.index())
            .ok_or(NamingError::MissingCaptureParent {
                function: function.index(),
                parent: parent.index(),
            })?;
    parent_names
        .locals
        .get(local.index())
        .map(|name| name.text.clone())
        .ok_or(NamingError::MissingCapturedBinding {
            function: function.index(),
            parent: parent.index(),
            kind: "local",
            index: local.index(),
        })
}

fn resolve_captured_upvalue_name(
    function: HirProtoRef,
    parent: HirProtoRef,
    upvalue: UpvalueId,
    assigned_functions: &[FunctionNameMap],
) -> Result<String, NamingError> {
    let parent_names =
        assigned_functions
            .get(parent.index())
            .ok_or(NamingError::MissingCaptureParent {
                function: function.index(),
                parent: parent.index(),
            })?;
    parent_names
        .upvalues
        .get(upvalue.index())
        .map(|name| name.text.clone())
        .ok_or(NamingError::MissingCapturedBinding {
            function: function.index(),
            parent: parent.index(),
            kind: "upvalue",
            index: upvalue.index(),
        })
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
