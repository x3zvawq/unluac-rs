//! 这个文件承载 HIR 的后处理收敛入口。
//!
//! 和 [analyze.rs](/Users/x3zvawq/workspace/unluac-rs/src/hir/analyze.rs) 一样，外层文件只
//! 负责声明 simplify 子模块并暴露主入口；真正的 pass 实现都放在目录内部。这样
//! `src/hir` 下两条主线在结构上保持一致，后续维护时更不容易产生“哪边是入口、哪边
//! 是细节实现”的混淆。

mod boolean_shells;
mod branch_value_folding;
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
mod temp_touch;
mod traverse;
mod visit;
mod walk;

use crate::debug::DebugFilters;
use crate::generate::GenerateMode;
use crate::hir::common::HirModule;
use crate::hir::promotion::ProtoPromotionFacts;
use crate::readability::ReadabilityOptions;
use crate::scheduler::{run_invalidation_loop, InvalidationTag, PassDescriptor, PassPhase};
use crate::timing::TimingCollector;

/// pass dump 需要的参数包。
///
/// 聚焦与深度语义由 `filters` 提供，这里不再单独记录 `proto_filter`。
/// 所有层级的 dump 对齐到同一套 `compute_focus_plan`：pass 快照对可见
/// proto 走完整 before/after，对“elided” proto 只发送一行 `<elided>` 摘要标记，
/// 对完全不可见的 proto 直接跳过。
#[derive(Clone, Default)]
pub(crate) struct PassDumpConfig {
    /// 需要 dump 的 pass 名称集合（空则不启用 dump）。
    pub pass_names: Vec<String>,
    /// 用户传入的调试过滤器，同时承载 focus proto 和 proto_depth。
    pub filters: DebugFilters,
}

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
    dialect: crate::ast::AstDialectVersion,
    dump_config: &PassDumpConfig,
) {
    let empty_facts = ProtoPromotionFacts::default();
    let dump_active = !dump_config.pass_names.is_empty();

    run_invalidation_loop(
        PASS_DESCRIPTORS,
        |index, name| {
            // 如果当前 pass 在 dump 列表中，先快照 before
            let before_snapshots = if dump_active && dump_config.pass_names.iter().any(|p| p == name) {
                Some(capture_hir_snapshots(module, &dump_config.filters))
            } else {
                None
            };

            let changed = timings.record(name, || {
                apply_proto_pass(module, |proto| {
                    let facts = promotion_facts
                        .get(proto.id.index())
                        .unwrap_or(&empty_facts);
                    match index {
                        0 => decision::simplify_decision_exprs_in_proto(proto),
                        1 => boolean_shells::remove_boolean_materialization_shells_in_proto(proto),
                        2 => logical_simplify::simplify_logical_exprs_in_proto(proto),
                        3 => table_constructors::stabilize_table_constructors_in_proto(proto, dialect),
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
            });

            // pass 产生变化时输出 before/after diff
            if let Some(before) = before_snapshots.filter(|_| changed) {
                emit_hir_pass_diff(name, &before, module, &dump_config.filters);
            }

            changed
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

/// 拍摄所有可见 proto 的文本快照，用于 pass dump before/after 对比。
///
/// 返回值的第三个字段是“是否被 focus plan 归为 visible”；false 表示这个 proto
/// 处于 elided 档位，下游 diff 只会在发生变化时打一行 `<elided>` 摘要。
/// 完全不可见的 proto 不会进入返回数组。
fn capture_hir_snapshots(
    module: &HirModule,
    filters: &DebugFilters,
) -> Vec<(usize, String, bool)> {
    let entries = super::debug::collect_hir_entries(module);
    let plan = super::debug::plan_focus(&entries, filters);
    if plan.focus.is_none() {
        return Vec::new();
    }
    entries
        .iter()
        .filter_map(|entry| {
            if plan.is_visible(entry.id) {
                Some((
                    entry.proto.id.index(),
                    super::debug::dump_proto_snapshot(entry.proto),
                    true,
                ))
            } else if plan.is_elided(entry.id) {
                Some((
                    entry.proto.id.index(),
                    super::debug::dump_proto_snapshot(entry.proto),
                    false,
                ))
            } else {
                None
            }
        })
        .collect()
}

/// 对比 before 快照与当前 module 状态，输出有变化的 proto 到 stderr。
///
/// 可见 proto 打印完整 before/after；elided proto 只打一行 `<elided>` 摘要标记
/// `=== [hir] pass=X proto#N CHANGED (elided) <summary> === end ===`，避免击穿用户
/// 没有要求关注的下层 proto 细节。
fn emit_hir_pass_diff(
    pass_name: &str,
    before: &[(usize, String, bool)],
    module: &HirModule,
    filters: &DebugFilters,
) {
    let after = capture_hir_snapshots(module, filters);
    for ((idx, before_text, before_visible), (_, after_text, _)) in
        before.iter().zip(after.iter())
    {
        if before_text == after_text {
            continue;
        }
        if *before_visible {
            eprintln!("=== [hir] pass={pass_name} proto#{idx} CHANGED ===");
            eprintln!("--- before ---");
            eprint!("{before_text}");
            eprintln!("--- after ---");
            eprint!("{after_text}");
            eprintln!("=== end ===");
        } else {
            // elided proto 只留一行标记；不再重复推算 summary row，
            // 用户想看完整 diff 可以把 focus 换到该 proto 再跑一遍。
            eprintln!("=== [hir] pass={pass_name} proto#{idx} CHANGED (elided) ===");
        }
    }
}

pub(crate) use decision::synthesize_readable_pure_logical_expr;
