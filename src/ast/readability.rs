//! AST readability：把合法 AST 收敛成更接近源码的稳定形状。

mod branch_pretty;
mod cleanup;
mod function_sugar;
mod inline_exprs;
mod short_circuit_pretty;
mod statement_merge;

use super::common::{AstModule, AstTargetDialect};
use crate::readability::ReadabilityOptions;

#[derive(Clone, Copy)]
pub(super) struct ReadabilityContext {
    pub target: AstTargetDialect,
    pub options: ReadabilityOptions,
}

#[derive(Clone, Copy)]
struct ReadabilityPass {
    apply: fn(&mut AstModule, ReadabilityContext) -> bool,
}

#[derive(Clone, Copy)]
struct ReadabilityStage {
    passes: &'static [ReadabilityPass],
}

const STRUCTURAL_CLEANUP_STAGE: ReadabilityStage = ReadabilityStage {
    passes: &[ReadabilityPass {
        apply: cleanup::apply,
    }],
};

const EXPR_INLINE_STAGE: ReadabilityStage = ReadabilityStage {
    passes: &[
        ReadabilityPass {
            apply: inline_exprs::apply,
        },
        ReadabilityPass {
            apply: cleanup::apply,
        },
    ],
};

const STATEMENT_MERGE_STAGE: ReadabilityStage = ReadabilityStage {
    passes: &[
        ReadabilityPass {
            apply: statement_merge::apply,
        },
        ReadabilityPass {
            apply: cleanup::apply,
        },
    ],
};

const CONTROL_FLOW_PRETTY_STAGE: ReadabilityStage = ReadabilityStage {
    passes: &[ReadabilityPass {
        apply: branch_pretty::apply,
    }],
};

const SHORT_CIRCUIT_PRETTY_STAGE: ReadabilityStage = ReadabilityStage {
    passes: &[ReadabilityPass {
        apply: short_circuit_pretty::apply,
    }],
};

const FUNCTION_SUGAR_STAGE: ReadabilityStage = ReadabilityStage {
    passes: &[
        ReadabilityPass {
            apply: function_sugar::apply,
        },
        ReadabilityPass {
            apply: cleanup::apply,
        },
    ],
};

const READABILITY_STAGES: &[ReadabilityStage] = &[
    STRUCTURAL_CLEANUP_STAGE,
    STATEMENT_MERGE_STAGE,
    CONTROL_FLOW_PRETTY_STAGE,
    EXPR_INLINE_STAGE,
    SHORT_CIRCUIT_PRETTY_STAGE,
    FUNCTION_SUGAR_STAGE,
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
    let mut module = module.clone();
    let context = ReadabilityContext { target, options };
    for stage in READABILITY_STAGES {
        let mut rounds = 0;
        loop {
            let mut changed = false;
            for pass in stage.passes {
                changed |= (pass.apply)(&mut module, context);
            }
            if !changed {
                break;
            }
            rounds += 1;
            assert!(
                rounds < MAX_STAGE_ROUNDS,
                "AST readability stage did not converge within {MAX_STAGE_ROUNDS} rounds"
            );
        }
    }
    module
}
