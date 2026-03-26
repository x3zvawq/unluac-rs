//! 这个文件重导出主 pipeline 各层之间的稳定契约类型。
//!
//! `decompile` 是对外总入口，但真实实现已经分散到 parser、transformer、
//! cfg 等模块里；这里统一转发，可以让调用方只从一处拿到完整阶段类型。

/// Transformer 层产出的统一 low-IR 根对象。
pub use crate::transformer::LoweredChunk;

/// CFG 层产出的控制流图。
pub use crate::cfg::CfgGraph;

/// 图分析层产出的支配、回边和循环等事实集合。
pub use crate::cfg::GraphFacts;

/// 数据流层产出的 def-use、活跃性和副作用摘要。
pub use crate::cfg::DataflowFacts;

/// 结构恢复前置层产出的结构候选与保留约束。
pub use crate::structure::StructureFacts;

/// HIR 层产出的结构化语义树。
pub use crate::hir::HirModule as HirChunk;

/// AST 层产出的 target-dialect-aware 语法树。
pub use crate::ast::AstModule as AstChunk;

/// 可读性层未来会产出的稳定 AST 调整结果。
pub use crate::ast::AstModule as ReadabilityResult;

/// 命名层未来会产出的绑定名决策结果。
pub use crate::naming::NameMap as NamingResult;

/// 生成层产出的最终源码对象。
pub use crate::generate::GeneratedChunk;
