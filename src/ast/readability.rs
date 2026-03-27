//! AST readability：把合法 AST 收敛成更接近源码的稳定形状。

mod binding_flow;
mod branch_pretty;
mod cleanup;
mod expr_analysis;
mod field_access_sugar;
mod function_sugar;
mod global_decl_pretty;
mod inline_exprs;
mod local_coalesce;
mod loop_header_merge;
mod materialize_temps;
mod short_circuit_pretty;
mod statement_merge;

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
}

const STRUCTURAL_CLEANUP_STAGE: ReadabilityStage = ReadabilityStage {
    name: "structural-cleanup",
    passes: &[ReadabilityPass {
        name: "cleanup",
        apply: cleanup::apply,
    }],
};

const EXPR_INLINE_STAGE: ReadabilityStage = ReadabilityStage {
    name: "expr-inline",
    passes: &[
        ReadabilityPass {
            name: "inline-exprs",
            apply: inline_exprs::apply,
        },
        ReadabilityPass {
            name: "cleanup",
            apply: cleanup::apply,
        },
    ],
};

const ACCESS_SUGAR_STAGE: ReadabilityStage = ReadabilityStage {
    name: "access-sugar",
    passes: &[ReadabilityPass {
        name: "field-access-sugar",
        apply: field_access_sugar::apply,
    }],
};

const STATEMENT_MERGE_STAGE: ReadabilityStage = ReadabilityStage {
    name: "statement-merge",
    passes: &[
        ReadabilityPass {
            name: "statement-merge",
            apply: statement_merge::apply,
        },
        ReadabilityPass {
            name: "cleanup",
            apply: cleanup::apply,
        },
    ],
};

const LOCAL_COALESCE_STAGE: ReadabilityStage = ReadabilityStage {
    name: "local-coalesce",
    passes: &[
        ReadabilityPass {
            name: "local-coalesce",
            apply: local_coalesce::apply,
        },
        ReadabilityPass {
            name: "cleanup",
            apply: cleanup::apply,
        },
    ],
};

const LOOP_HEADER_MERGE_STAGE: ReadabilityStage = ReadabilityStage {
    name: "loop-header-merge",
    passes: &[
        ReadabilityPass {
            name: "loop-header-merge",
            apply: loop_header_merge::apply,
        },
        ReadabilityPass {
            name: "cleanup",
            apply: cleanup::apply,
        },
    ],
};

const CONTROL_FLOW_PRETTY_STAGE: ReadabilityStage = ReadabilityStage {
    name: "control-flow-pretty",
    passes: &[ReadabilityPass {
        name: "branch-pretty",
        apply: branch_pretty::apply,
    }],
};

const SHORT_CIRCUIT_PRETTY_STAGE: ReadabilityStage = ReadabilityStage {
    name: "short-circuit-pretty",
    passes: &[ReadabilityPass {
        name: "short-circuit-pretty",
        apply: short_circuit_pretty::apply,
    }],
};

const FUNCTION_SUGAR_STAGE: ReadabilityStage = ReadabilityStage {
    name: "function-sugar",
    passes: &[
        ReadabilityPass {
            name: "function-sugar",
            apply: function_sugar::apply,
        },
        ReadabilityPass {
            name: "cleanup",
            apply: cleanup::apply,
        },
    ],
};

const GLOBAL_DECL_PRETTY_STAGE: ReadabilityStage = ReadabilityStage {
    name: "global-decl-pretty",
    passes: &[
        ReadabilityPass {
            name: "global-decl-pretty",
            apply: global_decl_pretty::apply,
        },
        ReadabilityPass {
            name: "cleanup",
            apply: cleanup::apply,
        },
    ],
};

const TEMP_MATERIALIZE_STAGE: ReadabilityStage = ReadabilityStage {
    name: "temp-materialize",
    passes: &[ReadabilityPass {
        name: "materialize-temps",
        apply: materialize_temps::apply,
    }],
};

const READABILITY_STAGES: &[ReadabilityStage] = &[
    STRUCTURAL_CLEANUP_STAGE,
    LOCAL_COALESCE_STAGE,
    STATEMENT_MERGE_STAGE,
    LOOP_HEADER_MERGE_STAGE,
    ACCESS_SUGAR_STAGE,
    CONTROL_FLOW_PRETTY_STAGE,
    EXPR_INLINE_STAGE,
    SHORT_CIRCUIT_PRETTY_STAGE,
    TEMP_MATERIALIZE_STAGE,
    FUNCTION_SUGAR_STAGE,
    GLOBAL_DECL_PRETTY_STAGE,
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
