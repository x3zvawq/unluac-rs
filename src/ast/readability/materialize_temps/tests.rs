//! 这个文件承载 `materialize_temps` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use crate::ast::{
    AstBindingRef, AstBlock, AstExpr, AstLocalAttr, AstLocalBinding, AstLocalDecl, AstModule,
    AstNameRef, AstReturn, AstStmt,
};
use crate::hir::{HirProtoRef, TempId};

#[test]
fn materializes_remaining_temps_into_synthetic_locals() {
    let temp = TempId(2);
    let mut module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Temp(temp),
                        attr: AstLocalAttr::None,
                    }],
                    values: vec![AstExpr::Boolean(true)],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Var(AstNameRef::Temp(temp))],
                })),
            ],
        },
    };

    let changed = super::apply(
        &mut module,
        super::ReadabilityContext {
            target: crate::ast::AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
            options: crate::readability::ReadabilityOptions::default(),
        },
    );

    assert!(changed);
    let AstStmt::LocalDecl(local_decl) = &module.body.stmts[0] else {
        panic!("first stmt should stay local decl");
    };
    assert!(matches!(
        local_decl.bindings[0].id,
        AstBindingRef::SyntheticLocal(_)
    ));
    let AstStmt::Return(ret) = &module.body.stmts[1] else {
        panic!("second stmt should stay return");
    };
    assert!(matches!(
        ret.values[0],
        AstExpr::Var(AstNameRef::SyntheticLocal(_))
    ));
}
