//! 这个文件定义主 pipeline 各层之间的契约占位类型。
//!
//! 当前只有 parser 真正实现完成，但现在就把后续层的输出位置先定出来，
//! 可以避免后面补 transformer、cfg 时为了接线再次大幅改 state 结构。

/// Transformer 层产出的统一 low-IR 根对象。
pub use crate::transformer::LoweredChunk;

/// CFG 层未来会产出的控制流图根对象。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CfgGraph;

/// 图分析层未来会产出的支配、回边和循环等事实集合。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GraphFacts;

/// 数据流层未来会产出的 def-use、活跃性和副作用摘要。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DataflowFacts;

/// 结构恢复前置层未来会产出的结构候选与保留约束。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StructureFacts;

/// HIR 层未来会产出的结构化语义树。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct HirChunk;

/// AST 层未来会产出的语法树。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AstChunk;

/// 可读性层未来会产出的稳定 AST 调整结果。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ReadabilityResult;

/// 命名层未来会产出的绑定名决策结果。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct NamingResult;

/// 生成层未来会产出的最终源码对象。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GeneratedChunk;
