//! 这个文件承载 `local_coalesce` 模块的局部不变量测试。

use super::ReadabilityContext;
use crate::ast::common::{
    AstBinaryExpr, AstBinaryOpKind, AstBindingRef, AstLocalBinding, AstLocalOrigin, AstNameRef,
};
use crate::ast::{
    AstBlock, AstExpr, AstLocalAttr, AstLocalDecl, AstModule, AstStmt, AstTargetDialect,
};
use crate::hir::LocalId;

fn apply_local_coalesce(module: &AstModule) -> AstModule {
    let mut module = module.clone();
    super::apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
            options: Default::default(),
        },
    );
    module
}

#[test]
fn coalesces_seed_local_into_carried_branch_local() {
    let seed = LocalId(0);
    let carried = LocalId(1);
    let branch_value = LocalId(2);
    let module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(seed),
                        attr: AstLocalAttr::None,
                        origin: AstLocalOrigin::DebugHinted,
                    }],
                    values: vec![AstExpr::Integer(0)],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(carried),
                        attr: AstLocalAttr::None,
                        origin: AstLocalOrigin::Recovered,
                    }],
                    values: Vec::new(),
                })),
                AstStmt::If(Box::new(crate::ast::AstIf {
                    cond: AstExpr::Boolean(true),
                    then_block: AstBlock {
                        stmts: vec![AstStmt::Assign(Box::new(crate::ast::AstAssign {
                            targets: vec![crate::ast::AstLValue::Name(AstNameRef::Local(carried))],
                            values: vec![AstExpr::Var(AstNameRef::Local(seed))],
                        }))],
                    },
                    else_block: Some(AstBlock {
                        stmts: vec![AstStmt::Assign(Box::new(crate::ast::AstAssign {
                            targets: vec![crate::ast::AstLValue::Name(AstNameRef::Local(carried))],
                            values: vec![AstExpr::Var(AstNameRef::Local(branch_value))],
                        }))],
                    }),
                })),
                AstStmt::Return(Box::new(crate::ast::AstReturn {
                    values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Add,
                        lhs: AstExpr::Var(AstNameRef::Local(carried)),
                        rhs: AstExpr::Integer(1),
                    }))],
                })),
            ],
        },
    };

    let module = apply_local_coalesce(&module);
    assert_eq!(module.body.stmts.len(), 3);
    let AstStmt::LocalDecl(local_decl) = &module.body.stmts[0] else {
        panic!("expected preserved seed local decl");
    };
    assert_eq!(local_decl.bindings[0].id, AstBindingRef::Local(seed));
    let AstStmt::If(if_stmt) = &module.body.stmts[1] else {
        panic!("expected branch after coalesce");
    };
    assert!(if_stmt.then_block.stmts.is_empty());
    let AstStmt::Return(ret) = &module.body.stmts[2] else {
        panic!("expected return after coalesce");
    };
    assert!(matches!(
        &ret.values[0],
        AstExpr::Binary(binary)
            if matches!(binary.lhs, AstExpr::Var(AstNameRef::Local(target)) if target == seed)
    ));
}

#[test]
fn does_not_coalesce_when_seed_is_used_for_other_purpose() {
    let seed = LocalId(0);
    let carried = LocalId(1);
    let module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(seed),
                        attr: AstLocalAttr::None,
                        origin: AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Integer(0)],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(carried),
                        attr: AstLocalAttr::None,
                        origin: AstLocalOrigin::Recovered,
                    }],
                    values: Vec::new(),
                })),
                AstStmt::Return(Box::new(crate::ast::AstReturn {
                    values: vec![
                        AstExpr::Var(AstNameRef::Local(seed)),
                        AstExpr::Var(AstNameRef::Local(carried)),
                    ],
                })),
            ],
        },
    };

    let module = apply_local_coalesce(&module);
    assert_eq!(module.body.stmts.len(), 3);
}
