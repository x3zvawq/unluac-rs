//! 这个子模块负责从 HIR 已提取好的 debug 提示翻译成 naming evidence。
//!
//! 它依赖 HIR 层在构建 `HirProto` 时已经预提取好的 `param_debug_hints`、
//! `upvalue_debug_hints`、`local_debug_hints`、`temp_debug_locals`，
//! 只构建 `FunctionNamingEvidence`，不会在这里决定最后采用哪个名字。
//! 例如：某个参数在 HIR 层已经提取出的 debug 名字，会在这里被折成参数命名证据。

use crate::hir::HirProto;

use super::super::common::{ClosureCaptureEvidence, FunctionNamingEvidence};

pub(super) fn build_function_evidence(
    hir: &HirProto,
    capture_evidence: Option<&ClosureCaptureEvidence>,
) -> FunctionNamingEvidence {
    let param_debug_names = hir.param_debug_hints.clone();

    let mut local_debug_names = hir.local_debug_hints.clone();
    // 变参参数寄存器的 binding 身份由 HIR 冻结；debug evidence 只能按该身份补提示，
    // 不能把 locals 的物理顺序当成参数身份。
    if let Some(local) = hir.vararg_param_local
        && let Some(slot) = local_debug_names.get_mut(local.index())
        && slot.is_none()
    {
        *slot = hir
            .param_debug_hints
            .get(hir.params.len())
            .cloned()
            .flatten();
    }

    let upvalue_debug_names = hir.upvalue_debug_hints.clone();
    let upvalue_capture_sources = capture_evidence
        .map(|evidence| evidence.captures.iter().copied().map(Some).collect())
        .unwrap_or_else(|| vec![None; hir.upvalues.len()]);

    FunctionNamingEvidence {
        param_debug_names,
        local_debug_names,
        upvalue_debug_names,
        upvalue_capture_sources,
        temp_debug_names: hir.temp_debug_locals.clone(),
    }
}
