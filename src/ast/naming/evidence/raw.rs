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
    // vararg 参数占用的 local slot 可能在 HIR 构建时未覆盖到；
    // 这里用 param_debug_hints 对应位置做补全。
    if hir.signature.has_vararg_param_reg
        && let Some(slot) = local_debug_names.first_mut()
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
        .map(|evidence| evidence.captures.clone())
        .unwrap_or_else(|| vec![None; hir.upvalues.len()]);

    FunctionNamingEvidence {
        param_debug_names,
        local_debug_names,
        upvalue_debug_names,
        upvalue_capture_sources,
        temp_debug_names: hir.temp_debug_locals.clone(),
    }
}
