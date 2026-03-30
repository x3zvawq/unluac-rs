//! 这个文件集中声明 Naming 层共享的数据结构。
//!
//! Naming 自身分成 evidence、lexical、hint、allocation 等多个关注点，
//! 但它们会共同读写一套稳定的类型定义。把这些共享类型放在这里，可以避免
//! 每个子模块都从 `assign.rs` 反向依赖，后续继续拆分时边界也更稳定。

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::AstSyntheticLocalId;
use crate::hir::{HirProtoRef, LocalId, ParamId, UpvalueId};

/// Naming 模式。
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum NamingMode {
    DebugLike,
    #[default]
    Simple,
    Heuristic,
}

impl NamingMode {
    pub const fn label(self) -> &'static str {
        match self {
            Self::DebugLike => "debug-like",
            Self::Simple => "simple",
            Self::Heuristic => "heuristic",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "debug-like" => Some(Self::DebugLike),
            "simple" => Some(Self::Simple),
            "heuristic" => Some(Self::Heuristic),
            _ => None,
        }
    }
}

/// Naming 选项。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NamingOptions {
    pub mode: NamingMode,
    pub debug_like_include_function: bool,
}

impl Default for NamingOptions {
    fn default() -> Self {
        Self {
            mode: NamingMode::Simple,
            debug_like_include_function: true,
        }
    }
}

/// 命名来源。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NameSource {
    Debug,
    CaptureProvenance,
    SelfParam,
    LoopRole,
    FieldName,
    TableShape,
    BoolShape,
    FunctionShape,
    ResultShape,
    Discard,
    DebugLike,
    Simple,
    ConflictFallback,
}

impl NameSource {
    pub const fn label(self) -> &'static str {
        match self {
            Self::Debug => "debug",
            Self::CaptureProvenance => "capture-provenance",
            Self::SelfParam => "self-param",
            Self::LoopRole => "loop-role",
            Self::FieldName => "field-name",
            Self::TableShape => "table-shape",
            Self::BoolShape => "bool-shape",
            Self::FunctionShape => "function-shape",
            Self::ResultShape => "result-shape",
            Self::Discard => "discard",
            Self::DebugLike => "debug-like",
            Self::Simple => "simple",
            Self::ConflictFallback => "conflict-fallback",
        }
    }
}

/// 单个名字槽位的最终结果。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NameInfo {
    pub text: String,
    pub source: NameSource,
    pub renamed: bool,
}

/// 单个函数上下文的名字表。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FunctionNameMap {
    pub params: Vec<NameInfo>,
    pub locals: Vec<NameInfo>,
    pub synthetic_locals: BTreeMap<AstSyntheticLocalId, NameInfo>,
    pub upvalues: Vec<NameInfo>,
}

/// Naming 阶段产出的整模块名字表。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct NameMap {
    pub entry_function: HirProtoRef,
    pub mode: NamingMode,
    pub functions: Vec<FunctionNameMap>,
}

impl NameMap {
    pub fn function(&self, function: HirProtoRef) -> Option<&FunctionNameMap> {
        self.functions.get(function.index())
    }
}

/// 所有函数的辅助证据。
#[derive(Debug, Clone, Default)]
pub struct NamingEvidence {
    pub(super) functions: Vec<FunctionNamingEvidence>,
}

/// 单个函数的命名证据。
#[derive(Debug, Clone, Default)]
pub(super) struct FunctionNamingEvidence {
    pub(super) param_debug_names: Vec<Option<String>>,
    pub(super) local_debug_names: Vec<Option<String>>,
    pub(super) upvalue_debug_names: Vec<Option<String>>,
    pub(super) upvalue_capture_sources: Vec<Option<CapturedBinding>>,
    pub(super) temp_debug_names: Vec<Option<String>>,
}

/// upvalue 捕获自父函数哪个绑定。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CapturedBinding {
    Param {
        parent: HirProtoRef,
        param: ParamId,
    },
    Local {
        parent: HirProtoRef,
        local: LocalId,
    },
    Upvalue {
        parent: HirProtoRef,
        upvalue: UpvalueId,
    },
}

/// 单次 closure 观察得到的 capture 证据。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ClosureCaptureEvidence {
    pub(super) parent: HirProtoRef,
    pub(super) captures: Vec<Option<CapturedBinding>>,
}

/// 从 AST 结构收集到的 naming hint。
#[derive(Debug, Clone, Default)]
pub(super) struct FunctionHints {
    pub(super) param_hints: BTreeMap<ParamId, CandidateHint>,
    pub(super) local_hints: BTreeMap<LocalId, CandidateHint>,
    pub(super) synthetic_locals: BTreeSet<AstSyntheticLocalId>,
    pub(super) synthetic_local_hints: BTreeMap<AstSyntheticLocalId, CandidateHint>,
}

/// 一个候选名字及其来源。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct CandidateHint {
    pub(super) text: String,
    pub(super) source: NameSource,
}

/// loop 相关的轻量上下文。
#[derive(Debug, Clone, Copy, Default)]
pub(super) struct LoopContext {
    pub(super) numeric_depth: usize,
}

/// 模块级分配器。
///
/// 目前只承载跨函数共享的 `FunctionShape` 去重状态，不把所有局部名字都提升成
/// 模块级全局唯一，避免破坏函数内局部命名的独立性。
#[derive(Debug, Default)]
pub(super) struct ModuleNameAllocator {
    pub(super) function_shape_names: BTreeSet<String>,
    pub(super) next_function_shape_suffix: BTreeMap<String, usize>,
}
