//! 从 HIR 闭包收集并校验命名所需的捕获来源。
//!
//! 每个 proto 只保存一次 capture provenance；例如 child upvalue 继承父 Local 的名字。
//! 调试提示已经属于 HirProto，候选名选择直接查询它，不复制另一套 debug 数组。

mod capture;

use crate::hir::HirModule;

use super::NamingError;
use super::common::NamingEvidence;
use capture::build_capture_evidence;

/// 从当前 HIR 收集捕获来源；与该 HIR 一起交给命名分配。
pub fn collect_naming_evidence(hir: &HirModule) -> Result<NamingEvidence, NamingError> {
    Ok(NamingEvidence {
        functions: build_capture_evidence(hir)?,
    })
}
