//! Naming 各子阶段共用的数据结构。
//!
//! 承载捕获证据、词法可见性、命名提示与最终分配的接口类型。

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::AstSyntheticLocalId;
use crate::hir::{HirProtoRef, LocalId, ParamId};
use strum_macros::{Display, EnumString, IntoStaticStr};

/// Naming 模式。
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Display, EnumString, IntoStaticStr)]
#[strum(serialize_all = "kebab-case")]
pub enum NamingMode {
    /// 优先保留 debug 名，缺失时使用稳定的函数/绑定编号。
    DebugLike,
    /// 使用通用递增名以及循环、函数等基本语法角色，不推断业务用途。
    #[default]
    Simple,
    /// 在通用策略上利用表达式形状、字段用途和调用线索推断名字。
    Heuristic,
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Display, IntoStaticStr)]
#[strum(serialize_all = "kebab-case")]
pub enum NameSource {
    LegacyArg,
    LexicalEnvironment,
    Debug,
    CaptureProvenance,
    SelfParam,
    LoopRole,
    FieldName,
    TableShape,
    BoolShape,
    FunctionShape,
    ResultShape,
    NumberShape,
    StringShape,
    Usage,
    ModulePath,
    CallResult,
    LibrarySignature,
    Discard,
    DebugLike,
    Simple,
    ConflictFallback,
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

/// 借用当前 HIR 模块的捕获来源；存活期间源 HIR 不可修改，调试提示仍查询同一模块。
#[derive(Debug, Clone, Default)]
pub struct NamingEvidence<'hir> {
    pub(super) functions: Vec<Option<ClosureCaptureEvidence<'hir>>>,
}

/// 单次 closure 的父级来源；借用完整 capture，但命名一致性只比较有序 binding，不比较 mode。
#[derive(Debug, Clone)]
pub(super) struct ClosureCaptureEvidence<'hir> {
    pub(super) parent: HirProtoRef,
    pub(super) captures: &'hir [crate::hir::HirCapture],
}

/// 从 AST 结构收集到的 naming hint。
#[derive(Debug, Clone, Default)]
pub(super) struct FunctionHints {
    pub(super) heuristic: bool,
    pub(super) param_hints: BTreeMap<ParamId, HintChoice>,
    pub(super) local_hints: BTreeMap<LocalId, HintChoice>,
    pub(super) synthetic_locals: BTreeSet<AstSyntheticLocalId>,
    pub(super) synthetic_local_hints: BTreeMap<AstSyntheticLocalId, HintChoice>,
}

/// 同级证据冲突时不采用遍历顺序碰巧选中的名字；更强证据仍可覆盖冲突。
#[derive(Debug, Clone)]
pub(super) enum HintChoice {
    Unique(CandidateHint),
    Ambiguous(NameSource),
}

impl HintChoice {
    pub(super) fn candidate(&self) -> Option<&CandidateHint> {
        match self {
            Self::Unique(candidate) => Some(candidate),
            Self::Ambiguous(_) => None,
        }
    }
    pub(super) fn source(&self) -> NameSource {
        match self {
            Self::Unique(candidate) => candidate.source,
            Self::Ambiguous(source) => *source,
        }
    }
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
