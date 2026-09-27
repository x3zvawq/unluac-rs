//! HIR 后处理收敛入口：按变化标签调度 pass，并提供同一次执行的模块事实快照。
//!
//! 闭包效果由当前 HIR 的显式 child/capture 身份统一汇总，构造器与 repeat root
//! 消费同一份摘要，任一 pass 改写 HIR 后失效。例如只读 capture 的调用
//! 不应被消费者重新解释为写入，未改写的连续 pass 也不必重复分析 child。
//! 此处负责摘要刷新和 pass 调度，不重新证明 VM 寄存器或源码改写合同。

mod boolean_shells;
mod branch_control_folding;
mod branch_value_folding;
mod call_frames;
mod carried_locals;
mod close_scopes;
mod dead_labels;
mod dead_temps;
mod debug_scopes;
pub(super) mod decision;
mod expr_facts;
mod generic_for_iterators;
mod label_refs;
mod lexical_cfg;
mod local_shapes;
mod locals;
mod logical_simplify;
mod mention;
mod method_protocol;
mod method_rewrite_transactions;
mod object_flow;
mod plain_method_syntax;
mod repeat_root_lifetimes;
mod residuals;
mod root_lifetimes;
mod source_frames;
mod stmt_plan;
mod table_constructors;
mod temp_inline;
mod temp_touch;
pub(crate) mod walk;

use crate::debug::DebugFilters;
use crate::decompile::{DecompileDialect, ReadabilityOptions};
use crate::generate::GenerateMode;
use crate::hir::common::HirModule;
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::ProtoPromotionFacts;
use crate::scheduler::{
    InvalidationConvergence, InvalidationTag, PassDescriptor, PassPhase, run_invalidation_loop,
};
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
        HIR_SHAPE_INPUTS
    }
}

use HirInvalidation::*;

// 表达式、物理根与 capture 投影共同消费完整 HIR 形状；每种标签只在此登记一次。
const HIR_SHAPE_INPUTS: &[HirInvalidation] = &[
    DecisionShape,
    BooleanPattern,
    LogicalExpr,
    TablePattern,
    TempChain,
    LocalBinding,
    BlockStructure,
    LabelGoto,
    ClosureCapture,
];

// Pass 描述符：声明每个 pass 依赖和产出哪些 invalidation tag。
//
// Normal 按失效标签恢复表达式和身份；构造器消除旧 allocation 后，先刷新根保护与内联，
// 再让 locals 固化身份，避免把已经结束的物理根事务保留成独立声明。
// Normal 全部收敛后执行 Deferred，新增形状再回到 Normal 消费。
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
        // Local promotion and handoff rewrites change source identity, physical-home provenance,
        // capture visibility, and the adjacent declaration shape consumed by this pass.
        depends_on: &[
            BooleanPattern,
            DecisionShape,
            LabelGoto,
            TempChain,
            LocalBinding,
            ClosureCapture,
        ],
        invalidates: &[
            BooleanPattern,
            LogicalExpr,
            TempChain,
            LocalBinding,
            BlockStructure,
            ClosureCapture,
        ],
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
        depends_on: HIR_SHAPE_INPUTS,
        // Constructor commit 会删除 producer、替换 SETLIST 并改变 binding 的使用点；
        // 这些事实必须让内联与 identity owner 重算，不能只通知表形状消费者。
        invalidates: &[TablePattern, TempChain, LocalBinding],
    },
    PassDescriptor {
        name: "temp-inline",
        phase: PassPhase::Normal,
        depends_on: HIR_SHAPE_INPUTS,
        // Temp substitution can expose literal/logical shapes that were not present in the
        // pre-inline HIR expression.  Let logical-simplify consume those facts in the next
        // invalidation round instead of leaving a mechanical numeric shell behind.
        invalidates: &[TempChain, LocalBinding, LogicalExpr],
    },
    PassDescriptor {
        name: "generic-for-iterators",
        phase: PassPhase::Normal,
        depends_on: &[TempChain, BlockStructure],
        invalidates: &[TempChain, LocalBinding],
    },
    PassDescriptor {
        name: "branch-values",
        phase: PassPhase::Normal,
        depends_on: HIR_SHAPE_INPUTS,
        invalidates: &[
            LabelGoto,
            BlockStructure,
            DecisionShape,
            TempChain,
            LocalBinding,
            LogicalExpr,
        ],
    },
    PassDescriptor {
        name: "locals",
        phase: PassPhase::Normal,
        depends_on: HIR_SHAPE_INPUTS,
        invalidates: &[LocalBinding, TempChain],
    },
    PassDescriptor {
        name: "branch-control",
        phase: PassPhase::Normal,
        depends_on: &[
            LabelGoto,
            BlockStructure,
            BooleanPattern,
            TempChain,
            LocalBinding,
            LogicalExpr,
            DecisionShape,
            ClosureCapture,
        ],
        invalidates: &[
            LabelGoto,
            BlockStructure,
            BooleanPattern,
            TempChain,
            LocalBinding,
            LogicalExpr,
            ClosureCapture,
        ],
    },
    // ── Deferred phase ──
    PassDescriptor {
        name: "eliminate-decisions",
        phase: PassPhase::Deferred,
        depends_on: &[DecisionShape],
        // Decision 线性化不只是删掉一个表达式节点：它会插入 if/block、home-free local、
        // temp/local assignment，并暴露新的逻辑、布尔壳和 table 相邻形状。把这些真实产出
        // 全部标脏，Normal consumers 才能在 owner 消费后重新审计原候选。
        invalidates: &[
            DecisionShape,
            BooleanPattern,
            LogicalExpr,
            TablePattern,
            TempChain,
            LocalBinding,
            BlockStructure,
        ],
    },
    PassDescriptor {
        name: "debug-scopes",
        phase: PassPhase::Deferred,
        depends_on: &[LocalBinding, BlockStructure],
        invalidates: &[BlockStructure],
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
        depends_on: &[LocalBinding, BlockStructure, ClosureCapture, LabelGoto],
        invalidates: &[LocalBinding, TempChain],
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
        invalidates: &[LabelGoto, BlockStructure, TempChain],
    },
    PassDescriptor {
        name: "repeat-root-lifetimes",
        phase: PassPhase::Deferred,
        depends_on: HIR_SHAPE_INPUTS,
        // 新发现的无显式读取 root 仍需要 locals 在原 repeat body 安排词法 owner。
        invalidates: &[TempChain, LocalBinding],
    },
    PassDescriptor {
        name: "native-call-frames",
        phase: PassPhase::Deferred,
        depends_on: HIR_SHAPE_INPUTS,
        // 完整调用消费后，同一身份的下一次写可能恢复为声明；构造器应在新词法
        // owner 上继续证明 initializer，不能等 AST 再次重建 HIR 已经拥有的事实。
        invalidates: &[LocalBinding, TablePattern, TempChain, BlockStructure],
    },
    PassDescriptor {
        name: "expanded-source-frames",
        phase: PassPhase::Final,
        depends_on: HIR_SHAPE_INPUTS,
        // 展开帧仍消费原 SETLIST 和内部值版本，必须先于不可逆的固定批次降低。
        invalidates: &[TablePattern, TempChain, LocalBinding, BlockStructure],
    },
    PassDescriptor {
        name: "source-frame-materializations",
        phase: PassPhase::Final,
        depends_on: HIR_SHAPE_INPUTS,
        // 词法事务可能同时消费 CALL 准备，暴露循环入口 guard；须交还 Normal
        // consumers 收敛，不能在调度结束后才产生新的表达式和控制形状。
        invalidates: &[TempChain, LocalBinding, BlockStructure, TablePattern],
    },
    PassDescriptor {
        name: "lower-fixed-table-batches",
        phase: PassPhase::Final,
        depends_on: HIR_SHAPE_INPUTS,
        // SETLIST 展开会丢失原 Batch 身份；完整原帧及其 Normal consumers 稳定后再降低。
        invalidates: &[TablePattern, TempChain, LocalBinding],
    },
    PassDescriptor {
        name: "parameter-return-frames",
        phase: PassPhase::Normal,
        depends_on: HIR_SHAPE_INPUTS,
        // 参数返回树不依赖模块调用摘要；完整树先收成表达式，再交 Normal 消费。
        invalidates: &[LocalBinding, BlockStructure, LogicalExpr, DecisionShape],
    },
    PassDescriptor {
        name: "tbc-initializer-frames",
        phase: PassPhase::Normal,
        depends_on: HIR_SHAPE_INPUTS,
        invalidates: &[LocalBinding, TempChain, TablePattern],
    },
    PassDescriptor {
        name: "final-dead-unresolved-temps",
        phase: PassPhase::Final,
        depends_on: HIR_SHAPE_INPUTS,
        // 原 nil 声明前缀已交词法事务，未消费项与 Boolean 预写仍按原证明清理。
        invalidates: &[TempChain, LocalBinding, BlockStructure, TablePattern],
    },
];

/// 对已经构造完成的 HIR 做 fixed-point 收敛。
pub(super) fn simplify_hir(
    module: &mut HirModule,
    readability: ReadabilityOptions,
    timings: &TimingCollector,
    promotion_facts: &mut Vec<ProtoPromotionFacts>,
    generate_mode: GenerateMode,
    dialect: DecompileDialect,
    dump_config: &PassDumpConfig,
) -> Result<(), crate::decompile::DecompileError> {
    // 入口状态的源码槽须先于 COPY 内联固定；否则原低槽写会变成分支末尾的
    // phi 交接，高槽构造器再也无法证明自己的完整 freereg 前缀。
    for proto in &mut module.protos {
        if let Some(facts) = promotion_facts.get_mut(proto.id.index()) {
            locals::restore_entry_frame(proto, facts);
        }
    }
    let mut empty_facts = ProtoPromotionFacts::default();
    let safety = HirExprSafety::for_dialect(dialect);
    let mut effect_snapshot = None;

    let convergence = run_invalidation_loop(
        PASS_DESCRIPTORS,
        &[("locals", "table-constructors"), ("locals", "temp-inline")],
        |index, name| {
            // 如果当前 pass 在 dump 列表中，先快照 before。关闭 debug feature 的构建
            // 不编译 HIR renderer，因此这里会退化成 None。
            let before_snapshots = capture_hir_snapshots_if_requested(module, dump_config, name);

            let changed = timings.record(name, || {
                // 空候选 pass 不需要 closure-effects；先判定适用性，避免其它 pass
                // 改写后为没有建表工作的模块反复重建整模块效果快照。
                if matches!(index, 3 | 19)
                    && !module.protos.iter().any(|proto| {
                        table_constructors::block_has_table_constructor_candidate(&proto.body)
                    })
                {
                    return false;
                }
                if index == 17 {
                    return call_frames::restore_expanded_frames(module, promotion_facts, dialect);
                }
                let effects = (matches!(index, 3 | 15 | 16 | 19)
                    || index == 4 && dialect == DecompileDialect::Luau)
                    .then(|| {
                        effect_snapshot.get_or_insert_with(|| {
                            timings.record("closure-effects", || {
                                object_flow::collect_proto_effects(module, safety, dialect)
                            })
                        })
                    });
                let effects = effects.as_deref();
                let roots = || object_flow::RootAnalysisContext {
                    safety,
                    effects: effects.expect("root pass requires module effects"),
                };
                if index == 15 {
                    return repeat_root_lifetimes::mark_repeat_trailing_condition_roots(
                        module,
                        promotion_facts,
                        roots(),
                    );
                }
                if index == 16 {
                    return call_frames::restore_native_call_frames(
                        module,
                        promotion_facts,
                        &effects
                            .expect("native frames require module value facts")
                            .values,
                        dialect,
                    );
                }
                if index == 4 {
                    return apply_temp_inline_pass(
                        module,
                        readability,
                        promotion_facts,
                        &empty_facts,
                        dialect,
                        safety,
                        effects.map(|effects| &effects.values),
                    );
                }
                let chunk_entry = module.entry;
                apply_proto_pass(module, |proto| {
                    let facts = promotion_facts
                        .get_mut(proto.id.index())
                        .unwrap_or(&mut empty_facts);
                    match index {
                        0 => decision::simplify_decision_exprs_in_proto(proto, safety),
                        1 => boolean_shells::remove_boolean_materialization_shells_in_proto(
                            proto, facts,
                        ),
                        2 => logical_simplify::simplify_logical_exprs_in_proto(proto, dialect),
                        3 => table_constructors::stabilize_table_constructors_in_proto(
                            proto,
                            facts,
                            roots(),
                            table_constructors::TableConstructorStage::Rebuild,
                        ),
                        4 => unreachable!("temp-inline needs child proto body facts"),
                        5 => {
                            generic_for_iterators::fold_generic_for_iterators_in_proto(proto, facts)
                        }
                        6 => branch_value_folding::fold_branch_values_in_proto(
                            proto,
                            readability,
                            facts,
                            dialect,
                            safety,
                        ),
                        7 => locals::promote_temps_to_locals_in_proto_with_facts(
                            proto, facts, safety, dialect,
                        ),
                        8 => branch_control_folding::fold_branch_control_in_proto(
                            proto, facts, safety,
                        ),
                        9 => decision::eliminate_remaining_decisions_in_proto(proto, facts, safety),
                        10 => debug_scopes::materialize_tail_debug_scopes_in_proto(proto, dialect),
                        11 => close_scopes::materialize_tbc_close_scopes_in_proto(proto, safety),
                        12 => carried_locals::collapse_carried_local_handoffs_in_proto(
                            proto, facts, safety, dialect,
                        ),
                        13 => dead_temps::remove_dead_temp_materializations_in_proto(
                            proto,
                            facts,
                            safety,
                            dead_temps::DeadTempStage::BeforeNativeFrames,
                        ),
                        14 => dead_labels::remove_unused_labels_in_proto(proto),
                        16 => unreachable!("native frames require one immutable module snapshot"),
                        19 => table_constructors::stabilize_table_constructors_in_proto(
                            proto,
                            facts,
                            roots(),
                            table_constructors::TableConstructorStage::LowerFixedBatches,
                        ),
                        18 => source_frames::restore_materializations(
                            proto,
                            facts,
                            dialect,
                            proto.id == chunk_entry,
                        ),
                        20 => call_frames::restore_parameter_return_frames(proto, facts, dialect),
                        21 => call_frames::restore_tbc_initializer_frames(
                            proto,
                            facts,
                            dialect,
                            proto.id == chunk_entry,
                        ),
                        22 => dead_temps::remove_dead_temp_materializations_in_proto(
                            proto,
                            facts,
                            safety,
                            dead_temps::DeadTempStage::Final,
                        ),
                        _ => unreachable!("invalid HIR pass index: {index}"),
                    }
                })
            });

            if changed {
                effect_snapshot = None;
            }

            // pass 产生变化时输出 before/after diff
            if let Some(before) = before_snapshots.filter(|_| changed) {
                emit_hir_pass_diff_if_requested(name, &before, module, &dump_config.filters);
            }

            changed
        },
        MAX_SIMPLIFY_ITERATIONS,
    );
    if let InvalidationConvergence::LimitExceeded { rounds } = convergence {
        return Err(crate::decompile::DecompileError::PassLimitExceeded {
            stage: crate::decompile::DecompileStage::Hir,
            rounds,
        });
    }

    timings.record("method-rewrite-transactions", || {
        for proto in &mut module.protos {
            if let Some(facts) = promotion_facts.get_mut(proto.id.index()) {
                method_rewrite_transactions::finalize_method_rewrite_transactions(proto, facts);
                call_frames::restore_terminal_method_frames(proto, facts, dialect);
                call_frames::preserve_existing_call_prefixes(
                    proto,
                    facts,
                    dialect,
                    proto.id == module.entry,
                );
                source_frames::preserve_copy_prefixes(
                    proto,
                    facts,
                    dialect,
                    proto.id == module.entry,
                );
            }
        }
    });
    timings.record("plain-method-syntax", || {
        if dialect != crate::decompile::DecompileDialect::Lua54 {
            return;
        }
        // 最终声明/根事务已改变 HIR；在该不可变版本上重新取得值事实，不沿用旧快照。
        let effects = object_flow::collect_proto_effects(module, safety, dialect);
        plain_method_syntax::finalize(module, promotion_facts, &effects.values, dialect);
    });
    let residuals = residuals::finalize_hir_exit_requirements(module);
    if residuals.has_soft_residuals() && generate_mode != GenerateMode::Permissive {
        residuals::emit_hir_warning(format!(
            "HIR exit still contains residual nodes: decision={}, unresolved={}.",
            residuals.decisions, residuals.unresolved
        ));
    }
    Ok(())
}

fn apply_temp_inline_pass(
    module: &mut HirModule,
    readability: ReadabilityOptions,
    promotion_facts: &[ProtoPromotionFacts],
    empty_facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    safety: HirExprSafety,
    values: Option<&object_flow::ReturnValueFacts>,
) -> bool {
    // 在当前模块快照上冻结原单结果 producer 的值域证书。temp-inline 只搬移同值
    // producer/use，不更换 CALL 的输入；提交之后不再查询已失效的模块分析。
    let inert_results = module
        .protos
        .iter()
        .map(|proto| {
            values.map_or_else(std::collections::BTreeSet::new, |values| {
                values.inert_scalar_call_results(proto)
            })
        })
        .collect::<Vec<_>>();
    // HIR proto ids are allocated parent-first. Walk the flat arena backwards so every direct
    // child has already reached its current temp-inline shape before the parent decides whether
    // a one-use closure is substantial enough to keep as a named callee. Unknown/backward refs
    // stay conservative (`true`) instead of being inlined on incomplete body evidence.
    let mut substantial_closure_bodies = vec![true; module.protos.len()];
    let mut changed = false;
    for proto_index in (0..module.protos.len()).rev() {
        let proto_id = module.protos[proto_index].id.index();
        let facts = promotion_facts.get(proto_id).unwrap_or(empty_facts);
        let proto = &mut module.protos[proto_index];
        changed |= temp_inline::inline_temps_in_proto_with_facts(
            proto,
            readability,
            facts,
            dialect,
            temp_inline::InlineModuleFacts {
                substantial_closure_bodies: &substantial_closure_bodies,
                inert_call_results: &inert_results[proto_index],
            },
            safety,
        );
        if let Some(slot) = substantial_closure_bodies.get_mut(proto_id) {
            *slot = temp_inline::proto_body_prefers_named_callee(&proto.body);
        }
    }
    changed
}

#[cfg(feature = "decompile-debug")]
type HirPassSnapshots = Vec<(usize, String, bool)>;

#[cfg(not(feature = "decompile-debug"))]
type HirPassSnapshots = ();

#[cfg(feature = "decompile-debug")]
fn capture_hir_snapshots_if_requested(
    module: &HirModule,
    dump_config: &PassDumpConfig,
    pass_name: &str,
) -> Option<HirPassSnapshots> {
    dump_config
        .pass_names
        .iter()
        .any(|name| name == pass_name)
        .then(|| capture_hir_snapshots(module, &dump_config.filters))
}

#[cfg(not(feature = "decompile-debug"))]
fn capture_hir_snapshots_if_requested(
    _module: &HirModule,
    dump_config: &PassDumpConfig,
    _pass_name: &str,
) -> Option<HirPassSnapshots> {
    let _ = dump_config.pass_names.len();
    None
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
#[cfg(feature = "decompile-debug")]
fn capture_hir_snapshots(module: &HirModule, filters: &DebugFilters) -> Vec<(usize, String, bool)> {
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
#[cfg(feature = "decompile-debug")]
fn emit_hir_pass_diff_if_requested(
    pass_name: &str,
    before: &[(usize, String, bool)],
    module: &HirModule,
    filters: &DebugFilters,
) {
    let after = capture_hir_snapshots(module, filters);
    for ((idx, before_text, before_visible), (_, after_text, _)) in before.iter().zip(after.iter())
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

#[cfg(not(feature = "decompile-debug"))]
fn emit_hir_pass_diff_if_requested(
    _pass_name: &str,
    _before: &HirPassSnapshots,
    _module: &HirModule,
    _filters: &DebugFilters,
) {
}
