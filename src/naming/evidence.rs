//! 这个文件负责组装 Naming 证据 builder。
//!
//! 这里保持成薄入口：
//! - `raw.rs` 只负责 parser/raw debug 相关证据
//! - `capture.rs` 只负责 HIR closure capture provenance
//!
//! 这样后续继续替换任意一侧的证据来源时，不需要再在同一个文件里同时穿梭
//! parser raw 和 HIR walker。

mod capture;
mod raw;

use crate::hir::HirModule;
use crate::parser::RawChunk;

use super::NamingError;
use super::common::NamingEvidence;
use capture::build_capture_evidence;
use raw::{build_function_evidence, collect_raw_functions};

/// 从 parser raw chunk 和 HIR 收集 Naming 证据。
///
/// 这里故意只产出“辅助命名的证据”，不顺带把 Naming 其它依赖一起揉进去。
/// 这样 `assign` 核心不必再直接碰 parser 原始结构，后续如果要替换证据来源，
/// 也可以先从这一层入手，而不会把分配逻辑重新拉回 parser 细节里。
pub fn collect_naming_evidence(
    raw: &RawChunk,
    hir: &HirModule,
) -> Result<NamingEvidence, NamingError> {
    let mut raw_functions = Vec::new();
    collect_raw_functions(&raw.main, &mut raw_functions);
    if raw_functions.len() != hir.protos.len() {
        return Err(NamingError::EvidenceProtoCountMismatch {
            raw_count: raw_functions.len(),
            hir_count: hir.protos.len(),
        });
    }

    let capture_evidence = build_capture_evidence(hir)?;
    let functions = raw_functions
        .into_iter()
        .zip(hir.protos.iter())
        .enumerate()
        .map(|(index, (raw_proto, hir_proto))| {
            build_function_evidence(raw_proto, hir_proto, capture_evidence[index].as_ref())
        })
        .collect();

    Ok(NamingEvidence { functions })
}
