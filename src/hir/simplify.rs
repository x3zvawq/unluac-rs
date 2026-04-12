//! 这个文件承载 HIR 的后处理收敛入口。
//!
//! 和 [analyze.rs](/Users/x3zvawq/workspace/unluac-rs/src/hir/analyze.rs) 一样，外层文件只
//! 负责声明 simplify 子模块并暴露主入口；真正的 pass 实现都放在目录内部。这样
//! `src/hir` 下两条主线在结构上保持一致，后续维护时更不容易产生“哪边是入口、哪边
//! 是细节实现”的混淆。

mod boolean_shells;
mod carried_locals;
mod close_scopes;
mod closure_self_capture;
mod dead_labels;
mod dead_temps;
pub(super) mod decision;
mod expr_facts;
mod locals;
mod logical_simplify;
mod residuals;
mod table_constructors;
mod temp_inline;
mod traverse;
mod visit;
mod walk;

use crate::generate::GenerateMode;
use crate::hir::common::HirModule;
use crate::hir::promotion::ProtoPromotionFacts;
use crate::readability::ReadabilityOptions;
use crate::scheduler::{run_invalidation_loop, InvalidationTag, PassDescriptor, PassPhase};
use crate::timing::TimingCollector;

const MAX_SIMPLIFY_ITERATIONS: usize = 128;

/// HIR 化简阶段的粗粒度变化标签。
///
/// 每个 pass 声明自己依赖和产出哪些标签，调度器根据 dirty set 决定哪些 pass 需要重跑。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum HirInvalidation {
    /// Decision DAG 结构变化。
    DecisionShape,
    /// 布尔物化 shell 变化。
    BooleanPattern,
    /// 逻辑表达式形状变化。
    LogicalExpr,
    /// 表构造器可合并区域变化。
    TablePattern,
    /// temp 链变化（影响 temp-inline, locals）。
    TempChain,
    /// local 绑定变化（影响 branch-value-exprs, table-constructors）。
    LocalBinding,
    /// block 嵌套结构变化（影响 close-scopes 及其下游 locals）。
    BlockStructure,
    /// label/goto 存在性变化。
    LabelGoto,
    /// 闭包捕获变化。
    ClosureCapture,
}

impl InvalidationTag for HirInvalidation {
    fn all() -> &'static [Self] {
        &[
            Self::DecisionShape,
            Self::BooleanPattern,
            Self::LogicalExpr,
            Self::TablePattern,
            Self::TempChain,
            Self::LocalBinding,
            Self::BlockStructure,
            Self::LabelGoto,
            Self::ClosureCapture,
        ]
    }
}

use HirInvalidation::*;

// Pass 描述符：声明每个 pass 依赖和产出哪些 invalidation tag。
//
// Normal phase（对应原 core + exposure）在每轮 dirty-set 驱动下重复执行直到收敛。
// Deferred phase（对应原 cleanup）在 Normal 全部收敛后执行一遍；如果产出新
// invalidation 则触发 Normal 重新收敛。
const PASS_DESCRIPTORS: &[PassDescriptor<HirInvalidation>] = &[
    // ── Normal phase ──
    PassDescriptor {
        name: "decision",
        phase: PassPhase::Normal,
        depends_on: &[DecisionShape],
        invalidates: &[DecisionShape, LogicalExpr, BooleanPattern],
    },
    PassDescriptor {
        name: "boolean-shells",
        phase: PassPhase::Normal,
        depends_on: &[BooleanPattern, DecisionShape],
        invalidates: &[BooleanPattern, TempChain],
    },
    PassDescriptor {
        name: "logical-simplify",
        phase: PassPhase::Normal,
        depends_on: &[LogicalExpr, DecisionShape],
        invalidates: &[LogicalExpr, DecisionShape],
    },
    PassDescriptor {
        name: "table-constructors",
        phase: PassPhase::Normal,
        depends_on: &[TablePattern, LocalBinding],
        invalidates: &[TablePattern],
    },
    PassDescriptor {
        name: "closure-self-capture",
        phase: PassPhase::Normal,
        depends_on: &[ClosureCapture],
        invalidates: &[ClosureCapture],
    },
    PassDescriptor {
        name: "temp-inline",
        phase: PassPhase::Normal,
        depends_on: &[TempChain, DecisionShape, BooleanPattern, LogicalExpr],
        invalidates: &[TempChain, LocalBinding],
    },
    PassDescriptor {
        name: "locals",
        phase: PassPhase::Normal,
        depends_on: &[TempChain, LocalBinding, BlockStructure],
        invalidates: &[LocalBinding, TempChain],
    },
    // ── Deferred phase ──
    PassDescriptor {
        name: "eliminate-decisions",
        phase: PassPhase::Deferred,
        depends_on: &[DecisionShape],
        invalidates: &[DecisionShape],
    },
    PassDescriptor {
        name: "close-scopes",
        phase: PassPhase::Deferred,
        depends_on: &[BlockStructure],
        invalidates: &[BlockStructure, LocalBinding, TempChain],
    },
    PassDescriptor {
        name: "carried-locals",
        phase: PassPhase::Deferred,
        depends_on: &[LocalBinding],
        invalidates: &[LocalBinding],
    },
    PassDescriptor {
        name: "dead-unresolved-temps",
        phase: PassPhase::Deferred,
        depends_on: &[TempChain],
        invalidates: &[TempChain],
    },
    PassDescriptor {
        name: "dead-labels",
        phase: PassPhase::Deferred,
        depends_on: &[LabelGoto],
        invalidates: &[LabelGoto],
    },
];

/// 对已经构造完成的 HIR 做 fixed-point 收敛。
pub(super) fn simplify_hir(
    module: &mut HirModule,
    readability: ReadabilityOptions,
    timings: &TimingCollector,
    promotion_facts: &[ProtoPromotionFacts],
    generate_mode: GenerateMode,
) {
    let empty_facts = ProtoPromotionFacts::default();

    run_invalidation_loop(
        PASS_DESCRIPTORS,
        |index, name| {
            timings.record(name, || {
                apply_proto_pass(module, |proto| {
                    let facts = promotion_facts
                        .get(proto.id.index())
                        .unwrap_or(&empty_facts);
                    match index {
                        0 => decision::simplify_decision_exprs_in_proto(proto),
                        1 => boolean_shells::remove_boolean_materialization_shells_in_proto(proto),
                        2 => logical_simplify::simplify_logical_exprs_in_proto(proto),
                        3 => table_constructors::stabilize_table_constructors_in_proto(proto),
                        4 => closure_self_capture::resolve_recursive_closure_self_captures_in_proto(proto),
                        5 => temp_inline::inline_temps_in_proto_with_facts(proto, readability, facts),
                        6 => locals::promote_temps_to_locals_in_proto_with_facts(proto, facts),
                        7 => decision::eliminate_remaining_decisions_in_proto(proto),
                        8 => close_scopes::materialize_tbc_close_scopes_in_proto(proto),
                        9 => carried_locals::collapse_carried_local_handoffs_in_proto(proto),
                        10 => dead_temps::remove_dead_temp_materializations_in_proto(proto),
                        11 => dead_labels::remove_unused_labels_in_proto(proto),
                        _ => unreachable!("invalid HIR pass index: {index}"),
                    }
                })
            })
        },
        MAX_SIMPLIFY_ITERATIONS,
    );

    let residuals = residuals::collect_hir_exit_residuals(module);
    if residuals.has_soft_residuals() && generate_mode != GenerateMode::Permissive {
        residuals::emit_hir_warning(format!(
            "HIR exit still contains residual nodes: decision={}, unresolved={}, \
             fallback_unstructured={}, other_unstructured={}.",
            residuals.decisions,
            residuals.unresolved,
            residuals.fallback_unstructured,
            residuals.other_unstructured
        ));
    }
}

fn apply_proto_pass(
    module: &mut HirModule,
    mut pass: impl FnMut(&mut crate::hir::common::HirProto) -> bool,
) -> bool {
    let mut changed = false;
    for proto in &mut module.protos {
        changed |= pass(proto);
    }
    changed
}

pub(crate) use decision::synthesize_readable_pure_logical_expr;
