//! 这个文件负责组装 Naming 证据 builder。
//!
//! 这里保持成薄入口：
//! - `raw.rs` 只负责从 HIR 已预提取好的 debug 提示构建证据
//! - `capture.rs` 只负责 HIR closure capture provenance
//!
//! 所有 debug 信息都在 HIR 构建阶段通过 `param_debug_hints`、`upvalue_debug_hints`
//! 等字段预提取完毕。证据构建不再直接接触 parser raw 结构。

mod capture;
mod raw;

use crate::hir::HirModule;

use super::NamingError;
use super::common::NamingEvidence;
use capture::build_capture_evidence;
use raw::build_function_evidence;

/// 从 HIR 收集 Naming 证据。
///
/// 这里故意只产出"辅助命名的证据"，不顺带把 Naming 其它依赖一起揉进去。
/// 这样 `assign` 核心不必再直接碰 parser 原始结构，后续如果要替换证据来源，
/// 也可以先从这一层入手，而不会把分配逻辑重新拉回 parser 细节里。
pub fn collect_naming_evidence(hir: &HirModule) -> Result<NamingEvidence, NamingError> {
    let capture_evidence = build_capture_evidence(hir)?;
    let functions = hir
        .protos
        .iter()
        .enumerate()
        .map(|(index, hir_proto)| {
            build_function_evidence(hir_proto, capture_evidence[index].as_ref())
        })
        .collect();

    Ok(NamingEvidence { functions })
}
