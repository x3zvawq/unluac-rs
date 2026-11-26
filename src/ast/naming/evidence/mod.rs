//! 从 AST 元数据收集并校验命名所需的捕获来源。
//!
//! 每个 proto 只保存一次 capture provenance；例如 child upvalue 继承父 Local 的名字。
//! 调试提示直接保存在 `AstProtoMeta` 中，候选名选择直接查询它，不复制另一套 debug 数组。

mod capture;

use crate::ast::AstModule;

use super::NamingError;
use super::common::NamingEvidence;
use capture::build_capture_evidence;

/// 从当前 AST 借用捕获来源；与该只读 AST 一起交给命名分配。
pub fn collect_naming_evidence(module: &AstModule) -> Result<NamingEvidence<'_>, NamingError> {
    Ok(NamingEvidence {
        functions: build_capture_evidence(module)?,
    })
}
