//! 主反编译流水线各层之间的稳定契约类型重导出。

pub use crate::analysis::{AnalysisChunk, CfgGraph};
pub use crate::ast::{AstModule as AstChunk, NameMap as NamingResult};
pub use crate::generate::GeneratedChunk;
pub use crate::transformer::LoweredChunk;
