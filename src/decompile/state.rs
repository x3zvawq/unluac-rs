//! 这个文件定义主 pipeline 的阶段枚举和状态容器。
//!
//! 这里选择“固定阶段枚举 + 强类型槽位”，是因为当前项目的阶段顺序天然固定，
//! 用静态结构能把每层的输入输出边界尽早钉死，后续排错和调试也更直接。

use std::{fmt, str::FromStr};

use crate::parser::RawChunk;

use super::contracts::{
    AstChunk, CfgGraph, DataflowFacts, GeneratedChunk, GraphFacts, HirChunk, LoweredChunk,
    NamingResult, ReadabilityResult, StructureFacts,
};
use super::options::DecompileDialect;

/// 主反编译 pipeline 的固定阶段顺序。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum DecompileStage {
    Parse,
    Transform,
    Cfg,
    GraphFacts,
    Dataflow,
    StructureFacts,
    Hir,
    Ast,
    Readability,
    Naming,
    Generate,
}

impl DecompileStage {
    /// 这里保留稳定标签，是为了让 CLI、错误消息和调试过滤器共用同一套名字。
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Parse => "parse",
            Self::Transform => "transform",
            Self::Cfg => "cfg",
            Self::GraphFacts => "graph-facts",
            Self::Dataflow => "dataflow",
            Self::StructureFacts => "structure-facts",
            Self::Hir => "hir",
            Self::Ast => "ast",
            Self::Readability => "readability",
            Self::Naming => "naming",
            Self::Generate => "generate",
        }
    }

    /// 主 pipeline 目前固定线性推进，所以“下一个阶段”也在这里集中维护。
    pub const fn next(self) -> Option<Self> {
        match self {
            Self::Parse => Some(Self::Transform),
            Self::Transform => Some(Self::Cfg),
            Self::Cfg => Some(Self::GraphFacts),
            Self::GraphFacts => Some(Self::Dataflow),
            Self::Dataflow => Some(Self::StructureFacts),
            Self::StructureFacts => Some(Self::Hir),
            Self::Hir => Some(Self::Ast),
            Self::Ast => Some(Self::Readability),
            Self::Readability => Some(Self::Naming),
            Self::Naming => Some(Self::Generate),
            Self::Generate => None,
        }
    }

}

impl fmt::Display for DecompileStage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for DecompileStage {
    type Err = ();

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "parse" => Ok(Self::Parse),
            "transform" => Ok(Self::Transform),
            "cfg" => Ok(Self::Cfg),
            "graph-facts" | "graph_facts" | "graphfacts" => Ok(Self::GraphFacts),
            "dataflow" => Ok(Self::Dataflow),
            "structure-facts" | "structure_facts" | "structurefacts" => {
                Ok(Self::StructureFacts)
            }
            "hir" => Ok(Self::Hir),
            "ast" => Ok(Self::Ast),
            "readability" => Ok(Self::Readability),
            "naming" => Ok(Self::Naming),
            "generate" => Ok(Self::Generate),
            _ => Err(()),
        }
    }
}

/// 一次 pipeline 执行期间，各层产物的统一状态容器。
#[derive(Debug, Clone, PartialEq)]
pub struct DecompileState {
    pub dialect: DecompileDialect,
    pub target_stage: DecompileStage,
    pub completed_stage: Option<DecompileStage>,
    pub raw_chunk: Option<RawChunk>,
    pub lowered: Option<LoweredChunk>,
    pub cfg: Option<CfgGraph>,
    pub graph_facts: Option<GraphFacts>,
    pub dataflow: Option<DataflowFacts>,
    pub structure_facts: Option<StructureFacts>,
    pub hir: Option<HirChunk>,
    pub ast: Option<AstChunk>,
    pub readability: Option<ReadabilityResult>,
    pub naming: Option<NamingResult>,
    pub generated: Option<GeneratedChunk>,
}

impl DecompileState {
    pub(crate) fn new(dialect: DecompileDialect, target_stage: DecompileStage) -> Self {
        Self {
            dialect,
            target_stage,
            completed_stage: None,
            raw_chunk: None,
            lowered: None,
            cfg: None,
            graph_facts: None,
            dataflow: None,
            structure_facts: None,
            hir: None,
            ast: None,
            readability: None,
            naming: None,
            generated: None,
        }
    }

    pub(crate) fn mark_completed(&mut self, stage: DecompileStage) {
        self.completed_stage = Some(stage);
    }
}
