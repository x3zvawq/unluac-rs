//! 这个文件承载 decompile 模块的局部不变量测试。
//!
//! 覆盖 output_plan 的 best-effort 升级策略等 pipeline 内部逻辑。

use crate::ast::{
    AstBlock, AstDialectVersion, AstExpr, AstGoto, AstLabel, AstLabelId, AstModule, AstStmt,
    AstTargetDialect, AstWhile,
};
use crate::generate::GenerateMode;
use crate::hir::HirProtoRef;
use crate::readability::ReadabilityOptions;
use crate::timing::TimingCollector;

use super::output_plan::{resolve_output_plan, unsupported_ast_features};

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
        ReadabilityOptions::default(),
        GenerateMode::BestEffort,
        &TimingCollector::disabled(),
        &[],
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
        ReadabilityOptions::default(),
        GenerateMode::BestEffort,
        &TimingCollector::disabled(),
        &[],
    );

    assert_eq!(plan.generate_mode, GenerateMode::Permissive);
    assert!(!plan.warnings.is_empty());
}
