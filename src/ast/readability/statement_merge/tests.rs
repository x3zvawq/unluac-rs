//! 这个文件承载 `statement_merge` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use crate::ast::common::{AstCallExpr, AstCallKind, AstLocalBinding};
use crate::ast::{
    AstExpr, AstLValue, AstLocalAttr, AstLocalDecl, AstModule, AstNameRef, AstStmt,
    AstTargetDialect, make_readable_with_options,
};
use crate::hir::{LocalId, TempId};

#[test]
fn merges_empty_local_decl_followed_by_matching_assign() {
    let temp = TempId(0);
    let module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Temp(temp),
                        attr: AstLocalAttr::None,
                    }],
                    values: Vec::new(),
                })),
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                        args: vec![AstExpr::Integer(1)],
                    }))],
                })),
            ],
        },
    };

    let module = make_readable_with_options(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
        Default::default(),
    );
    assert_eq!(
        module.body.stmts,
        vec![AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: crate::ast::AstBindingRef::SyntheticLocal(crate::ast::AstSyntheticLocalId(
                    temp,
                )),
                attr: AstLocalAttr::None,
            }],
            values: vec![AstExpr::Call(Box::new(AstCallExpr {
                callee: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                args: vec![AstExpr::Integer(1)],
            }))],
        }))]
    );
}

#[test]
fn does_not_merge_when_assign_targets_do_not_match_decl_bindings() {
    let module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(LocalId(0)),
                        attr: AstLocalAttr::None,
                    }],
                    values: Vec::new(),
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(LocalId(1))),
                        args: vec![AstExpr::Integer(1)],
                    })),
                })),
            ],
        },
    };

    let module = make_readable_with_options(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
        Default::default(),
    );
    assert_eq!(module.body.stmts.len(), 2);
}
