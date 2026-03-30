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
use crate::timing::TimingCollector;

#[derive(Clone, Copy)]
pub(super) struct ReadabilityContext {
    pub target: AstTargetDialect,
    pub options: ReadabilityOptions,
}

#[derive(Clone, Copy)]
struct ReadabilityPass {
    name: &'static str,
    apply: fn(&mut AstModule, ReadabilityContext) -> bool,
}

#[derive(Clone, Copy)]
struct ReadabilityStage {
    name: &'static str,
    passes: &'static [ReadabilityPass],
    cleanup_after_passes: bool,
}

const CLEANUP_PASS: ReadabilityPass = ReadabilityPass {
    name: "cleanup",
    apply: cleanup::apply,
};

const fn stage(name: &'static str, passes: &'static [ReadabilityPass]) -> ReadabilityStage {
    ReadabilityStage {
        name,
        passes,
        cleanup_after_passes: false,
    }
}

const fn stage_with_cleanup(
    name: &'static str,
    passes: &'static [ReadabilityPass],
) -> ReadabilityStage {
    ReadabilityStage {
        name,
        passes,
        cleanup_after_passes: true,
    }
}

const STRUCTURAL_CLEANUP_STAGE: ReadabilityStage = stage("structural-cleanup", &[CLEANUP_PASS]);

const EXPR_INLINE_STAGE: ReadabilityStage = stage_with_cleanup(
    "expr-inline",
    &[
        ReadabilityPass {
            name: "inline-exprs",
            apply: inline_exprs::apply,
        },
        ReadabilityPass {
            name: "field-access-sugar-post-inline",
            apply: field_access_sugar::apply,
        },
    ],
);

const ACCESS_SUGAR_STAGE: ReadabilityStage = stage(
    "access-sugar",
    &[ReadabilityPass {
        name: "field-access-sugar",
        apply: field_access_sugar::apply,
    }],
);

const STATEMENT_MERGE_STAGE: ReadabilityStage = stage_with_cleanup(
    "statement-merge",
    &[ReadabilityPass {
        name: "statement-merge",
        apply: statement_merge::apply,
    }],
);

const LOCAL_COALESCE_STAGE: ReadabilityStage = stage_with_cleanup(
    "local-coalesce",
    &[ReadabilityPass {
        name: "local-coalesce",
        apply: local_coalesce::apply,
    }],
);

const LOOP_HEADER_MERGE_STAGE: ReadabilityStage = stage_with_cleanup(
    "loop-header-merge",
    &[ReadabilityPass {
        name: "loop-header-merge",
        apply: loop_header_merge::apply,
    }],
);

const CONTROL_FLOW_PRETTY_STAGE: ReadabilityStage = stage(
    "control-flow-pretty",
    &[ReadabilityPass {
        name: "branch-pretty",
        apply: branch_pretty::apply,
    }],
);

const POST_CONTROL_FLOW_STATEMENT_MERGE_STAGE: ReadabilityStage = stage_with_cleanup(
    "post-control-flow-statement-merge",
    &[ReadabilityPass {
        name: "statement-merge-post-control-flow",
        apply: statement_merge::apply,
    }],
);

const POST_CONTROL_FLOW_LOCAL_COALESCE_STAGE: ReadabilityStage = stage_with_cleanup(
    "post-control-flow-local-coalesce",
    &[ReadabilityPass {
        name: "local-coalesce-post-control-flow",
        apply: local_coalesce::apply,
    }],
);

const SHORT_CIRCUIT_PRETTY_STAGE: ReadabilityStage = stage(
    "short-circuit-pretty",
    &[ReadabilityPass {
        name: "short-circuit-pretty",
        apply: short_circuit_pretty::apply,
    }],
);

const FUNCTION_SUGAR_STAGE: ReadabilityStage = stage_with_cleanup(
    "function-sugar",
    &[
        ReadabilityPass {
            name: "installer-iife",
            apply: installer_iife::apply,
        },
        ReadabilityPass {
            name: "function-sugar",
            apply: function_sugar::apply,
        },
    ],
);

const GLOBAL_DECL_PRETTY_STAGE: ReadabilityStage = stage_with_cleanup(
    "global-decl-pretty",
    &[ReadabilityPass {
        name: "global-decl-pretty",
        apply: global_decl_pretty::apply,
    }],
);

const LUAJIT_GOTO_SAFETY_STAGE: ReadabilityStage = stage(
    "luajit-goto-safety",
    &[ReadabilityPass {
        name: "luajit-goto-safety",
        apply: luajit_goto_safety::apply,
    }],
);

const TEMP_MATERIALIZE_STAGE: ReadabilityStage = stage(
    "temp-materialize",
    &[ReadabilityPass {
        name: "materialize-temps",
        apply: materialize_temps::apply,
    }],
);

// Stage 顺序本身就是 readability 契约的一部分：
// 1. 先把最机械的 local/stmt 壳压平，避免后续 sugar 看见被过度拆开的 AST。
// 2. 再做 access / control-flow / expr sugar，让表达式和结构更接近源码。
//    控制流整理之后，原先被 label/goto 壳挡住的 hoisted temp 往往会重新暴露成普通相邻
//    assign 形状，所以这里会补一轮已有的 statement-merge，而不是平行新长一个 pass。
//    同理，某些 carried local 直到 `branch_pretty` 把 goto 网收成普通 `if-else` 之后，
//    才能稳定看出“这个 seed local 正在吸收前面 hoist 出来的 carried temp”；
//    这里继续复用已有的 `local_coalesce`，而不是为 post-branch 形状再长一个新 pass。
//    `inline-exprs` 可能会重新露出 `"name"` 这类字符串索引，所以 access sugar
//    要在表达式内联之后再补一轮，避免新暴露的 key 停在 `["n"]` 这种半糖形态。
// 3. `materialize-temps` 必须先于 `installer-iife/function-sugar`，否则后者会把仍处在
//    临时槽位里的机械节点误当成稳定源码 binding，也没法给新引入的局部名分配 AST 自己的
//    synthetic local。
// 4. `function-sugar` 现在同时承接局部 alias 和已经物化出来的机械 direct call method sugar。
//    branch-local 值壳已经前推到 HIR；到了 AST 这里只剩 `obj.field(obj, ...)` 这种保守
//    调用形状，需要在同一个 owner 里统一决定能否收回 `obj:field(...)`。
// 5. `global-decl-pretty` 和 `luajit-goto-safety` 放在后面，只消费前面已经稳定下来的 AST。
const READABILITY_STAGES: &[ReadabilityStage] = &[
    STRUCTURAL_CLEANUP_STAGE,
    LOCAL_COALESCE_STAGE,
    STATEMENT_MERGE_STAGE,
    LOOP_HEADER_MERGE_STAGE,
    ACCESS_SUGAR_STAGE,
    CONTROL_FLOW_PRETTY_STAGE,
    POST_CONTROL_FLOW_STATEMENT_MERGE_STAGE,
    POST_CONTROL_FLOW_LOCAL_COALESCE_STAGE,
    EXPR_INLINE_STAGE,
    SHORT_CIRCUIT_PRETTY_STAGE,
    TEMP_MATERIALIZE_STAGE,
    FUNCTION_SUGAR_STAGE,
    GLOBAL_DECL_PRETTY_STAGE,
    LUAJIT_GOTO_SAFETY_STAGE,
];

const MAX_STAGE_ROUNDS: usize = 64;

/// 对外的 readability 入口。
pub fn make_readable(module: &AstModule, target: AstTargetDialect) -> AstModule {
    make_readable_with_options(module, target, ReadabilityOptions::default())
}

/// 对外的 readability 入口，允许调用方调节局部可读性策略。
pub fn make_readable_with_options(
    module: &AstModule,
    target: AstTargetDialect,
    options: ReadabilityOptions,
) -> AstModule {
    let timings = TimingCollector::disabled();
    make_readable_with_options_and_timing(module, target, options, &timings)
}

pub(crate) fn make_readable_with_options_and_timing(
    module: &AstModule,
    target: AstTargetDialect,
    options: ReadabilityOptions,
    timings: &TimingCollector,
) -> AstModule {
    let mut module = module.clone();
    let context = ReadabilityContext { target, options };
    for stage in READABILITY_STAGES {
        timings.record(stage.name, || {
            let mut rounds = 0;
            loop {
                let changed = timings.record("fixed-point-round", || {
                    let mut changed = false;
                    for pass in stage.passes {
                        changed |= timings.record(pass.name, || (pass.apply)(&mut module, context));
                    }
                    if stage.cleanup_after_passes {
                        changed |= timings.record(CLEANUP_PASS.name, || {
                            (CLEANUP_PASS.apply)(&mut module, context)
                        });
                    }
                    changed
                });
                if !changed {
                    break;
                }
                rounds += 1;
                assert!(
                    rounds < MAX_STAGE_ROUNDS,
                    "AST readability stage did not converge within {MAX_STAGE_ROUNDS} rounds"
                );
            }
        });
    }
    module
}
