//! 输出方言选择与 best-effort 升级逻辑。
//!
//! 根据 AST 中实际出现的特性集合，决定最终输出使用的目标方言版本、
//! 代码生成模式（Strict / Permissive）以及需要向用户报告的警告。

use std::collections::BTreeSet;

use crate::ast::{
    AstDialectVersion, AstFeature, AstModule, AstTargetDialect,
    collect_ast_features, make_readable,
};
use crate::generate::GenerateMode;
use crate::timing::TimingCollector;

use super::options::DecompileDialect;

#[derive(Debug, Clone)]
pub(super) struct OutputPlan {
    pub readability: AstModule,
    pub target: AstTargetDialect,
    pub generate_mode: GenerateMode,
    pub warnings: Vec<String>,
}

pub(super) fn resolve_output_plan(
    ast: &AstModule,
    requested_target: AstTargetDialect,
    readability_options: crate::readability::ReadabilityOptions,
    mode: GenerateMode,
    timings: &TimingCollector,
) -> OutputPlan {
    match mode {
        GenerateMode::Strict => OutputPlan {
            readability: make_readable(
                ast,
                requested_target,
                readability_options,
                timings,
            ),
            target: requested_target,
            generate_mode: GenerateMode::Strict,
            warnings: Vec::new(),
        },
        GenerateMode::Permissive => {
            let readability = make_readable(
                ast,
                requested_target,
                readability_options,
                timings,
            );
            let unsupported = unsupported_ast_features(&readability, requested_target);
            let warnings = if unsupported.is_empty() {
                Vec::new()
            } else {
                vec![format!(
                    "requested target dialect `{}` does not support feature(s) {}; emitting permissive output.",
                    requested_target.version,
                    format_ast_features(&unsupported)
                )]
            };
            OutputPlan {
                readability,
                target: requested_target,
                generate_mode: GenerateMode::Permissive,
                warnings,
            }
        }
        GenerateMode::BestEffort => {
            let mut target =
                choose_best_effort_target(requested_target.version, &collect_ast_features(ast))
                    .unwrap_or(requested_target);

            loop {
                let readability = make_readable(
                    ast,
                    target,
                    readability_options,
                    timings,
                );
                let unsupported_in_target = unsupported_ast_features(&readability, target);
                if unsupported_in_target.is_empty() {
                    let unsupported_in_requested =
                        unsupported_ast_features(&readability, requested_target);
                    let warnings = if target.version != requested_target.version
                        && !unsupported_in_requested.is_empty()
                    {
                        vec![format!(
                            "upgraded output dialect from `{}` to `{}` to support feature(s) {}.",
                            requested_target.version,
                            target.version,
                            format_ast_features(&unsupported_in_requested)
                        )]
                    } else {
                        Vec::new()
                    };
                    return OutputPlan {
                        readability,
                        target,
                        generate_mode: GenerateMode::Strict,
                        warnings,
                    };
                }

                let final_features = collect_ast_features(&readability);
                let Some(upgraded) =
                    choose_best_effort_target(requested_target.version, &final_features)
                else {
                    let mut warnings = Vec::new();
                    let unsupported_in_requested =
                        unsupported_ast_features(&readability, requested_target);
                    if target.version != requested_target.version
                        && !unsupported_in_requested.is_empty()
                    {
                        warnings.push(format!(
                            "upgraded output dialect from `{}` to `{}` to support feature(s) {}.",
                            requested_target.version,
                            target.version,
                            format_ast_features(&unsupported_in_requested)
                        ));
                    }
                    warnings.push(format!(
                        "no single supported target dialect can express feature(s) {}; emitting permissive output.",
                        format_ast_features(&final_features)
                    ));
                    return OutputPlan {
                        readability,
                        target,
                        generate_mode: GenerateMode::Permissive,
                        warnings,
                    };
                };

                if upgraded == target {
                    let unsupported_in_requested =
                        unsupported_ast_features(&readability, requested_target);
                    let mut warnings = Vec::new();
                    if !unsupported_in_requested.is_empty() {
                        warnings.push(format!(
                            "requested target dialect `{}` does not support feature(s) {}; emitting permissive output.",
                            requested_target.version,
                            format_ast_features(&unsupported_in_requested)
                        ));
                    }
                    return OutputPlan {
                        readability,
                        target,
                        generate_mode: GenerateMode::Permissive,
                        warnings,
                    };
                }

                target = upgraded;
            }
        }
    }
}

fn unsupported_ast_features(module: &AstModule, target: AstTargetDialect) -> BTreeSet<AstFeature> {
    collect_ast_features(module)
        .into_iter()
        .filter(|feature| !target.supports_feature(*feature))
        .collect()
}

fn choose_best_effort_target(
    requested: AstDialectVersion,
    features: &BTreeSet<AstFeature>,
) -> Option<AstTargetDialect> {
    candidate_output_versions(requested)
        .into_iter()
        .map(AstTargetDialect::new)
        .find(|target| {
            features
                .iter()
                .all(|feature| target.supports_feature(*feature))
        })
}

fn candidate_output_versions(requested: AstDialectVersion) -> Vec<AstDialectVersion> {
    match requested {
        AstDialectVersion::Lua51 => vec![
            AstDialectVersion::Lua51,
            AstDialectVersion::Lua52,
            AstDialectVersion::Lua53,
            AstDialectVersion::Lua54,
            AstDialectVersion::Lua55,
            AstDialectVersion::LuaJit,
            AstDialectVersion::Luau,
        ],
        AstDialectVersion::Lua52 => vec![
            AstDialectVersion::Lua52,
            AstDialectVersion::Lua53,
            AstDialectVersion::Lua54,
            AstDialectVersion::Lua55,
            AstDialectVersion::LuaJit,
            AstDialectVersion::Luau,
        ],
        AstDialectVersion::Lua53 => vec![
            AstDialectVersion::Lua53,
            AstDialectVersion::Lua54,
            AstDialectVersion::Lua55,
            AstDialectVersion::LuaJit,
            AstDialectVersion::Luau,
        ],
        AstDialectVersion::Lua54 => vec![
            AstDialectVersion::Lua54,
            AstDialectVersion::Lua55,
            AstDialectVersion::LuaJit,
            AstDialectVersion::Luau,
        ],
        AstDialectVersion::Lua55 => vec![
            AstDialectVersion::Lua55,
            AstDialectVersion::LuaJit,
            AstDialectVersion::Luau,
        ],
        AstDialectVersion::LuaJit => vec![
            AstDialectVersion::LuaJit,
            AstDialectVersion::Lua52,
            AstDialectVersion::Lua53,
            AstDialectVersion::Lua54,
            AstDialectVersion::Lua55,
            AstDialectVersion::Luau,
        ],
        AstDialectVersion::Luau => vec![
            AstDialectVersion::Luau,
            AstDialectVersion::Lua52,
            AstDialectVersion::Lua53,
            AstDialectVersion::Lua54,
            AstDialectVersion::Lua55,
            AstDialectVersion::LuaJit,
        ],
    }
}

fn format_ast_features(features: &BTreeSet<AstFeature>) -> String {
    features
        .iter()
        .map(|feature| feature.label())
        .collect::<Vec<_>>()
        .join(", ")
}

pub(super) fn target_ast_dialect(dialect: DecompileDialect) -> AstTargetDialect {
    let version = match dialect {
        DecompileDialect::Lua51 => AstDialectVersion::Lua51,
        DecompileDialect::Lua52 => AstDialectVersion::Lua52,
        DecompileDialect::Lua53 => AstDialectVersion::Lua53,
        DecompileDialect::Lua54 => AstDialectVersion::Lua54,
        DecompileDialect::Lua55 => AstDialectVersion::Lua55,
        DecompileDialect::Luajit => AstDialectVersion::LuaJit,
        DecompileDialect::Luau => AstDialectVersion::Luau,
    };
    AstTargetDialect::new(version)
}

pub(super) fn ast_lowering_target(
    target: AstTargetDialect,
    mode: GenerateMode,
) -> AstTargetDialect {
    if mode == GenerateMode::Strict {
        target
    } else {
        AstTargetDialect::relaxed_for_lowering(target.version)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{AstBlock, AstExpr, AstGoto, AstLabel, AstLabelId, AstStmt, AstWhile};
    use crate::hir::HirProtoRef;

    fn module_with_stmts(stmts: Vec<AstStmt>) -> AstModule {
        AstModule {
            entry_function: HirProtoRef(0),
            body: AstBlock { stmts },
        }
    }

    #[test]
    fn best_effort_should_upgrade_lua51_goto_to_lua52() {
        let label = AstLabelId(1);
        let module = module_with_stmts(vec![
            AstStmt::Goto(Box::new(AstGoto { target: label })),
            AstStmt::Label(Box::new(AstLabel { id: label })),
        ]);

        let plan = resolve_output_plan(
            &module,
            AstTargetDialect::new(AstDialectVersion::Lua51),
            crate::readability::ReadabilityOptions::default(),
            GenerateMode::BestEffort,
            &TimingCollector::disabled(),
        );

        assert_eq!(plan.target.version, AstDialectVersion::Lua52);
        assert_eq!(plan.generate_mode, GenerateMode::Strict);
        assert!(unsupported_ast_features(&plan.readability, plan.target).is_empty());
        assert_eq!(plan.warnings.len(), 1);
    }

    #[test]
    fn best_effort_should_fall_back_to_permissive_when_no_single_dialect_fits() {
        let label = AstLabelId(1);
        let module = module_with_stmts(vec![
            AstStmt::While(Box::new(AstWhile {
                cond: AstExpr::Boolean(true),
                body: AstBlock {
                    stmts: vec![AstStmt::Continue],
                },
            })),
            AstStmt::Goto(Box::new(AstGoto { target: label })),
            AstStmt::Label(Box::new(AstLabel { id: label })),
        ]);

        let plan = resolve_output_plan(
            &module,
            AstTargetDialect::new(AstDialectVersion::Lua51),
            crate::readability::ReadabilityOptions::default(),
            GenerateMode::BestEffort,
            &TimingCollector::disabled(),
        );

        assert_eq!(plan.generate_mode, GenerateMode::Permissive);
        assert!(!plan.warnings.is_empty());
    }
}
