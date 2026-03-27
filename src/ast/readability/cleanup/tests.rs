//! 这个文件承载 `cleanup` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use crate::ast::{
    AstBlock, AstExpr, AstFunctionExpr, AstIf, AstLocalFunctionDecl, AstModule, AstReturn, AstStmt,
    AstTargetDialect,
};
use crate::hir::{LocalId, ParamId, TempId};

use super::{ReadabilityContext, apply};

#[test]
fn removes_trailing_empty_return_from_module_and_function_bodies() {
    let local = LocalId(0);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalFunctionDecl(Box::new(AstLocalFunctionDecl {
                    name: crate::ast::AstBindingRef::Local(local),
                    func: AstFunctionExpr {
                        function: Default::default(),
                        params: vec![ParamId(0)],
                        is_vararg: false,
                        body: AstBlock {
                            stmts: vec![AstStmt::Return(Box::new(AstReturn { values: vec![] }))],
                        },
                    },
                })),
                AstStmt::Return(Box::new(AstReturn { values: vec![] })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: Default::default(),
        }
    ));

    let AstStmt::LocalFunctionDecl(local_fn) = &module.body.stmts[0] else {
        panic!("expected local function decl");
    };
    assert!(local_fn.func.body.stmts.is_empty(), "{module:#?}");
    assert_eq!(module.body.stmts.len(), 1, "{module:#?}");
}

#[test]
fn keeps_empty_return_inside_nested_control_flow_blocks() {
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![AstStmt::If(Box::new(AstIf {
                cond: AstExpr::Boolean(true),
                then_block: AstBlock {
                    stmts: vec![AstStmt::Return(Box::new(AstReturn { values: vec![] }))],
                },
                else_block: None,
            }))],
        },
    };

    assert!(!apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: Default::default(),
        }
    ));

    let AstStmt::If(ast_if) = &module.body.stmts[0] else {
        panic!("expected if statement");
    };
    assert!(matches!(
        ast_if.then_block.stmts.as_slice(),
        [AstStmt::Return(ret)] if ret.values.is_empty()
    ));
}

#[test]
fn drops_unused_synthetic_locals_but_keeps_bindings_assigned_later() {
    let unused = crate::ast::AstSyntheticLocalId(TempId(0));
    let assigned = crate::ast::AstSyntheticLocalId(TempId(1));
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![
                        crate::ast::AstLocalBinding {
                            id: crate::ast::AstBindingRef::SyntheticLocal(unused),
                            attr: crate::ast::AstLocalAttr::None,
                            origin: crate::ast::AstLocalOrigin::Recovered,
                        },
                        crate::ast::AstLocalBinding {
                            id: crate::ast::AstBindingRef::SyntheticLocal(assigned),
                            attr: crate::ast::AstLocalAttr::None,
                            origin: crate::ast::AstLocalOrigin::Recovered,
                        },
                    ],
                    values: Vec::new(),
                })),
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![crate::ast::AstLValue::Name(
                        crate::ast::AstNameRef::SyntheticLocal(assigned),
                    )],
                    values: vec![AstExpr::Integer(1)],
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: Default::default(),
        }
    ));

    let AstStmt::LocalDecl(local_decl) = &module.body.stmts[0] else {
        panic!("expected trimmed local decl");
    };
    assert_eq!(local_decl.bindings.len(), 1);
    assert_eq!(
        local_decl.bindings[0].id,
        crate::ast::AstBindingRef::SyntheticLocal(assigned)
    );
}
