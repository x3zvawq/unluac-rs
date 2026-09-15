//! 这个文件负责把 evidence/hints 组合成具体候选名字。
//!
//! 这里还不做最终冲突消解，只回答“这个槽位现在最像什么名字”。
//! 真正的唯一化和祖先作用域避让由 allocation 阶段完成。

use crate::ast::AstSyntheticLocalId;
use crate::hir::{HirBinding, HirProto, HirProtoRef, LocalId, ParamId};

use super::NamingError;
use super::ast_facts::FunctionAstNamingFacts;
use super::common::{
    CandidateHint, ClosureCaptureEvidence, FunctionHints, FunctionNameMap, NameSource, NamingMode,
    NamingOptions,
};
use super::lexical::VisibleBinding;
use super::support::{alphabetical_name, as_valid_name};

/// 选择参数候选名。
pub(super) fn choose_param_candidate(
    proto: &HirProto,
    param: ParamId,
    index: usize,
    hints: &FunctionHints,
    options: NamingOptions,
) -> CandidateHint {
    if let Some(hint) = hints.param_hints.get(&param)
        && hint.source == NameSource::SelfParam
    {
        return hint.clone();
    }
    if let Some(name) = proto.param_debug_hints.get(index).and_then(as_valid_name) {
        return CandidateHint {
            text: name,
            source: NameSource::Debug,
        };
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
    hints: &FunctionHints,
    ast_facts: &FunctionAstNamingFacts,
    options: NamingOptions,
) -> CandidateHint {
    let index = local.index();
    if proto.lexical_environment_local == Some(local) {
        return CandidateHint {
            text: "_ENV".to_owned(),
            source: NameSource::LexicalEnvironment,
        };
    }
    if proto.signature.legacy_arg_slot && proto.vararg_param_local == Some(local) {
        return CandidateHint {
            text: "arg".to_owned(),
            source: NameSource::LegacyArg,
        };
    }
    // 仅为 HIR 指定的变参 local 补空提示，不覆盖已有名字或越界槽。
    let debug_hint = proto.local_debug_hints.get(index).and_then(|hint| {
        if hint.is_none() && proto.vararg_param_local == Some(local) {
            proto.param_debug_hints.get(proto.params.len())
        } else {
            Some(hint)
        }
    });
    if let Some(name) = debug_hint.and_then(as_valid_name) {
        return CandidateHint {
            text: name,
            source: NameSource::Debug,
        };
    }
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
    if let Some(hint) = hints.local_hints.get(&local) {
        return hint.clone();
    }
    mode_fallback_candidate(options, proto.id, "l", index, "value".to_owned())
}

/// 选择 upvalue 候选名。
pub(super) fn choose_upvalue_candidate(
    proto: &HirProto,
    index: usize,
    capture_evidence: Option<&ClosureCaptureEvidence<'_>>,
    options: NamingOptions,
    assigned_functions: &[FunctionNameMap],
) -> Result<CandidateHint, NamingError> {
    if let Some(evidence) = capture_evidence
        && let Some(capture) = evidence.captures.get(index)
    {
        // upvalue 不是一个“重新发明名字”的槽位：只要我们知道它捕获自哪个父绑定，
        // 就应该沿用那个绑定在父作用域里已经稳定下来的名字。
        return resolve_captured_name(
            proto.id,
            evidence.parent,
            capture.binding,
            assigned_functions,
        );
    }
    if let Some(name) = proto.upvalue_debug_hints.get(index).and_then(as_valid_name) {
        return Ok(CandidateHint {
            text: name,
            source: NameSource::Debug,
        });
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
    hints: &FunctionHints,
    ast_facts: &FunctionAstNamingFacts,
    options: NamingOptions,
) -> CandidateHint {
    let index = local.index();
    if let AstSyntheticLocalId::HirTemp(temp) = local
        && let Some(name) = proto
            .temp_debug_locals
            .get(temp.index())
            .and_then(as_valid_name)
    {
        return CandidateHint {
            text: name,
            source: NameSource::Debug,
        };
    }
    if options.mode == NamingMode::DebugLike {
        let visible_count = ast_facts.debug_like_binding_order.len();
        return mode_fallback_candidate(
            options,
            proto.id,
            "r",
            debug_like_binding_index(ast_facts, crate::ast::AstBindingRef::SyntheticLocal(local))
                .unwrap_or(visible_count + proto.local_count + synthetic_order),
            "value".to_owned(),
        );
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

pub(super) fn resolve_visible_binding_name(
    function: HirProtoRef,
    binding: VisibleBinding,
    assigned_functions: &[FunctionNameMap],
) -> Result<&str, NamingError> {
    let (parent, kind, index) = match binding {
        VisibleBinding::Param { function, param } => (function, "param", param.index()),
        VisibleBinding::Local { function, local } => (function, "local", local.index()),
        VisibleBinding::SyntheticLocal { function, local } => {
            (function, "synthetic-local", local.index())
        }
        VisibleBinding::Upvalue { function, upvalue } => (function, "upvalue", upvalue.index()),
    };
    let parent_names =
        assigned_functions
            .get(parent.index())
            .ok_or(NamingError::MissingCaptureParent {
                function: function.index(),
                parent: parent.index(),
            })?;
    let name = match binding {
        VisibleBinding::Param { param, .. } => parent_names.params.get(param.index()),
        VisibleBinding::Local { local, .. } => parent_names.locals.get(local.index()),
        VisibleBinding::SyntheticLocal { local, .. } => parent_names.synthetic_locals.get(&local),
        VisibleBinding::Upvalue { upvalue, .. } => parent_names.upvalues.get(upvalue.index()),
    };
    name.map(|name| name.text.as_str())
        .ok_or(NamingError::MissingCapturedBinding {
            function: function.index(),
            parent: parent.index(),
            kind,
            index,
        })
}

fn resolve_captured_name(
    function: HirProtoRef,
    parent: HirProtoRef,
    binding: HirBinding,
    assigned_functions: &[FunctionNameMap],
) -> Result<CandidateHint, NamingError> {
    let binding = match binding {
        HirBinding::Param(param) => VisibleBinding::Param {
            function: parent,
            param,
        },
        HirBinding::Local(local) => VisibleBinding::Local {
            function: parent,
            local,
        },
        HirBinding::Temp(temp) => VisibleBinding::SyntheticLocal {
            function: parent,
            local: AstSyntheticLocalId::HirTemp(temp),
        },
        HirBinding::Upvalue(upvalue) => VisibleBinding::Upvalue {
            function: parent,
            upvalue,
        },
    };
    Ok(CandidateHint {
        text: resolve_visible_binding_name(function, binding, assigned_functions)?.to_owned(),
        source: NameSource::CaptureProvenance,
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
