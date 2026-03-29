//! 这个子模块负责把 raw debug 信息翻译成 naming evidence。
//!
//! 它依赖 parser/raw 已给好的局部变量、upvalue、capture 事实，只构建 `FunctionNamingEvidence`，
//! 不会在这里决定最后采用哪个名字。
//! 例如：某个寄存器在 pc=0 的 debug 名字，会在这里被折成参数命名证据。

use crate::hir::HirProto;
use crate::parser::RawProto;

use super::super::common::{ClosureCaptureEvidence, FunctionNamingEvidence};
use super::super::support::{debug_local_name_for_reg_at_pc, decode_raw_string};

pub(super) fn build_function_evidence(
    raw: &RawProto,
    hir: &HirProto,
    capture_evidence: Option<&ClosureCaptureEvidence>,
) -> FunctionNamingEvidence {
    let param_debug_names = (0..hir.params.len())
        .map(|reg| debug_local_name_for_reg_at_pc(raw, reg, 0))
        .collect::<Vec<_>>();

    let mut local_debug_names = hir.local_debug_hints.clone();
    if raw.common.signature.has_vararg_param_reg
        && let Some(slot) = local_debug_names.first_mut()
        && slot.is_none()
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

pub(super) fn collect_raw_functions<'a>(proto: &'a RawProto, functions: &mut Vec<&'a RawProto>) {
    functions.push(proto);
    for child in &proto.common.children {
        collect_raw_functions(child, functions);
    }
}
