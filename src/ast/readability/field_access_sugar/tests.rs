//! 这个文件承载 `field_access_sugar` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use crate::ast::{
    AstCallExpr, AstExpr, AstIndexAccess, AstModule, AstNameRef, AstReturn, AstStmt,
    AstTargetDialect,
};

use super::{ReadabilityContext, apply};

#[test]
fn rewrites_string_index_with_identifier_key_into_field_access() {
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![AstStmt::Return(Box::new(AstReturn {
                values: vec![AstExpr::Call(Box::new(AstCallExpr {
                    callee: AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Global(crate::ast::AstGlobalName {
                            text: "table".to_owned(),
                        })),
                        index: AstExpr::String("concat".to_owned()),
                    })),
                    args: vec![AstExpr::Var(AstNameRef::Local(crate::hir::LocalId(0)))],
                }))],
            }))],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: Default::default(),
        }
    ));

    let AstStmt::Return(ret) = &module.body.stmts[0] else {
        panic!("expected return");
    };
    let AstExpr::Call(call) = &ret.values[0] else {
        panic!("expected call");
    };
    assert!(
        matches!(&call.callee, AstExpr::FieldAccess(_)),
        "{module:#?}"
    );
}
