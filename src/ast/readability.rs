//! AST readability：把前层已经合法的 AST 收敛成更接近源码的稳定形状。
//!
//! 这里不是给前层“补事实”或“兜底修结构”的阶段：
//! - 不负责替 AST build / HIR / Structure 补缺失语义
//! - 不负责把前层过度内联、过度结构化的问题继续静默修掉
//! - 只在前层事实已经足够稳定时，做源码可读性层面的保守整形

mod binding_flow;
mod binding_tree;
mod branch_pretty;
mod cleanup;
mod expr_analysis;
mod field_access_sugar;
mod function_sugar;
mod global_decl_pretty;
mod inline_exprs;
mod installer_iife;
mod local_coalesce;
mod loop_header_merge;
mod luajit_goto_safety;
mod materialize_temps;
mod short_circuit_pretty;
mod statement_merge;
mod traverse;
mod visit;
mod walk;

use super::common::{AstModule, AstTargetDialect};
use crate::readability::ReadabilityOptions;
use crate::scheduler::{run_invalidation_loop, InvalidationTag, PassDescriptor, PassPhase};
use crate::timing::TimingCollector;

#[derive(Clone, Copy)]
pub(super) struct ReadabilityContext {
    pub target: AstTargetDialect,
    pub options: ReadabilityOptions,
}

/// AST 可读性变化的粗粒度标签。
///
/// 每个 pass 声明自己依赖和产出哪些标签，调度器根据 dirty set 决定哪些 pass 需要重跑。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum AstInvalidation {
    /// 语句相邻关系变化（影响 statement-merge, local-coalesce, loop-header-merge）。
    StatementAdjacency,
    /// 控制流形状变化（影响 branch-pretty 及其下游）。
    ControlFlowShape,
    /// 表达式形状变化（影响 field-access-sugar, short-circuit-pretty, inline-exprs）。
    ExprShape,
    /// 绑定关系变化（影响 local-coalesce, function-sugar）。
    BindingStructure,
    /// temp 存在性变化（影响 temp-materialize, inline-exprs）。
    TempPresence,
}

impl InvalidationTag for AstInvalidation {
    fn all() -> &'static [Self] {
        &[
            Self::StatementAdjacency,
            Self::ControlFlowShape,
            Self::ExprShape,
            Self::BindingStructure,
            Self::TempPresence,
        ]
    }
}

/// pass 的可执行入口，与 `PASS_DESCRIPTORS` 按下标一一对应。
struct ReadabilityPassEntry {
    apply: fn(&mut AstModule, ReadabilityContext) -> bool,
}

use AstInvalidation::*;

// Pass 描述符：声明每个 pass 依赖和产出哪些 invalidation tag。
//
// 排列顺序决定同一轮内的执行先后——把"生产者"放在"消费者"前面可以减少
// 不必要的多轮迭代。调度器会根据 dirty set 自动跳过不相关的 pass。
//
// Normal phase 处理主要形状收敛：
//   cleanup → local-coalesce → statement-merge → loop-header-merge
//   → branch-pretty → field-access-sugar → inline-exprs → short-circuit-pretty
//
// Deferred phase 在 Normal 全部收敛后执行终态物化和语法糖：
//   temp-materialize → installer-iife → function-sugar → global-decl-pretty → luajit-goto-safety
//
// 如果 Deferred pass 产出新 invalidation，Normal phase 会重新收敛。
const PASS_DESCRIPTORS: &[PassDescriptor<AstInvalidation>] = &[
    // ── Normal phase ──
    PassDescriptor {
        name: "cleanup",
        phase: PassPhase::Normal,
        depends_on: &[StatementAdjacency, ControlFlowShape, ExprShape, BindingStructure, TempPresence],
        invalidates: &[StatementAdjacency],
    },
    PassDescriptor {
        name: "local-coalesce",
        phase: PassPhase::Normal,
        depends_on: &[StatementAdjacency, ControlFlowShape, BindingStructure],
        invalidates: &[StatementAdjacency, BindingStructure],
    },
    PassDescriptor {
        name: "statement-merge",
        phase: PassPhase::Normal,
        depends_on: &[StatementAdjacency, ControlFlowShape],
        invalidates: &[StatementAdjacency, ExprShape],
    },
    PassDescriptor {
        name: "loop-header-merge",
        phase: PassPhase::Normal,
        depends_on: &[StatementAdjacency],
        invalidates: &[StatementAdjacency, BindingStructure],
    },
    PassDescriptor {
        name: "branch-pretty",
        phase: PassPhase::Normal,
        depends_on: &[ControlFlowShape],
        invalidates: &[ControlFlowShape, StatementAdjacency],
    },
    PassDescriptor {
        name: "field-access-sugar",
        phase: PassPhase::Normal,
        depends_on: &[ExprShape],
        invalidates: &[ExprShape],
    },
    PassDescriptor {
        name: "inline-exprs",
        phase: PassPhase::Normal,
        depends_on: &[StatementAdjacency, ExprShape, TempPresence],
        invalidates: &[StatementAdjacency, ExprShape],
    },
    PassDescriptor {
        name: "short-circuit-pretty",
        phase: PassPhase::Normal,
        depends_on: &[ExprShape],
        invalidates: &[ExprShape],
    },
    // ── Deferred phase ──
    PassDescriptor {
        name: "materialize-temps",
        phase: PassPhase::Deferred,
        depends_on: &[TempPresence],
        invalidates: &[TempPresence, BindingStructure, StatementAdjacency],
    },
    PassDescriptor {
        name: "installer-iife",
        phase: PassPhase::Deferred,
        depends_on: &[TempPresence, BindingStructure],
        invalidates: &[StatementAdjacency, ExprShape, BindingStructure],
    },
    PassDescriptor {
        name: "function-sugar",
        phase: PassPhase::Deferred,
        depends_on: &[TempPresence, BindingStructure, ExprShape],
        invalidates: &[StatementAdjacency, ExprShape],
    },
    PassDescriptor {
        name: "global-decl-pretty",
        phase: PassPhase::Deferred,
        depends_on: &[StatementAdjacency],
        invalidates: &[StatementAdjacency],
    },
    PassDescriptor {
        name: "luajit-goto-safety",
        phase: PassPhase::Deferred,
        depends_on: &[ControlFlowShape],
        invalidates: &[],
    },
];

/// pass 执行入口，下标与 `PASS_DESCRIPTORS` 一一对应。
const PASS_ENTRIES: &[ReadabilityPassEntry] = &[
    ReadabilityPassEntry { apply: cleanup::apply },
    ReadabilityPassEntry { apply: local_coalesce::apply },
    ReadabilityPassEntry { apply: statement_merge::apply },
    ReadabilityPassEntry { apply: loop_header_merge::apply },
    ReadabilityPassEntry { apply: branch_pretty::apply },
    ReadabilityPassEntry { apply: field_access_sugar::apply },
    ReadabilityPassEntry { apply: inline_exprs::apply },
    ReadabilityPassEntry { apply: short_circuit_pretty::apply },
    ReadabilityPassEntry { apply: materialize_temps::apply },
    ReadabilityPassEntry { apply: installer_iife::apply },
    ReadabilityPassEntry { apply: function_sugar::apply },
    ReadabilityPassEntry { apply: global_decl_pretty::apply },
    ReadabilityPassEntry { apply: luajit_goto_safety::apply },
];

const MAX_ROUNDS: usize = 64;

/// 对外的 readability 入口。
pub(crate) fn make_readable(
    module: &AstModule,
    target: AstTargetDialect,
    options: ReadabilityOptions,
    timings: &TimingCollector,
) -> AstModule {
    let mut module = module.clone();
    let context = ReadabilityContext { target, options };

    run_invalidation_loop(
        PASS_DESCRIPTORS,
        |index, name| timings.record(name, || (PASS_ENTRIES[index].apply)(&mut module, context)),
        MAX_ROUNDS,
    );

    module
}
