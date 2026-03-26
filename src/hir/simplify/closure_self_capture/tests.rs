use crate::hir::{
    HirAssign, HirBlock, HirCapture, HirClosureExpr, HirExpr, HirLValue, HirLocalDecl, HirProto,
    HirProtoRef, HirStmt, LocalId, TempId,
};
use crate::parser::{ProtoLineRange, ProtoSignature};

use super::resolve_recursive_closure_self_captures_in_proto;

#[test]
fn rewrites_undefined_self_capture_temp_to_local_binding() {
    let mut proto = HirProto {
        id: HirProtoRef(0),
        source: None,
        line_range: ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: ProtoSignature {
            num_params: 0,
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
        },
        params: Vec::new(),
        locals: vec![LocalId(0)],
        upvalues: Vec::new(),
        temps: vec![TempId(0)],
        temp_debug_locals: Vec::new(),
        body: HirBlock {
            stmts: vec![HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![LocalId(0)],
                values: vec![HirExpr::Closure(Box::new(HirClosureExpr {
                    proto: HirProtoRef(1),
                    captures: vec![HirCapture {
                        value: HirExpr::TempRef(TempId(0)),
                    }],
                }))],
            }))],
        },
        children: vec![HirProtoRef(1)],
    };

    assert!(resolve_recursive_closure_self_captures_in_proto(&mut proto));

    let HirStmt::LocalDecl(local_decl) = &proto.body.stmts[0] else {
        panic!("expected local decl");
    };
    let HirExpr::Closure(closure) = &local_decl.values[0] else {
        panic!("expected closure initializer");
    };
    assert!(matches!(
        closure.captures.as_slice(),
        [HirCapture {
            value: HirExpr::LocalRef(LocalId(0))
        }]
    ));
}

#[test]
fn keeps_defined_parent_temp_capture_unchanged() {
    let mut proto = HirProto {
        id: HirProtoRef(0),
        source: None,
        line_range: ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: ProtoSignature {
            num_params: 0,
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
        },
        params: Vec::new(),
        locals: vec![LocalId(0)],
        upvalues: Vec::new(),
        temps: vec![TempId(0)],
        temp_debug_locals: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::Integer(1)],
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(0)],
                    values: vec![HirExpr::Closure(Box::new(HirClosureExpr {
                        proto: HirProtoRef(1),
                        captures: vec![HirCapture {
                            value: HirExpr::TempRef(TempId(0)),
                        }],
                    }))],
                })),
            ],
        },
        children: vec![HirProtoRef(1)],
    };

    assert!(!resolve_recursive_closure_self_captures_in_proto(
        &mut proto
    ));

    let HirStmt::LocalDecl(local_decl) = &proto.body.stmts[1] else {
        panic!("expected local decl");
    };
    let HirExpr::Closure(closure) = &local_decl.values[0] else {
        panic!("expected closure initializer");
    };
    assert!(matches!(
        closure.captures.as_slice(),
        [HirCapture {
            value: HirExpr::TempRef(TempId(0))
        }]
    ));
}

#[test]
fn rewrites_undefined_self_capture_temp_for_local_assignment_target() {
    let mut proto = HirProto {
        id: HirProtoRef(0),
        source: None,
        line_range: ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: ProtoSignature {
            num_params: 0,
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
        },
        params: Vec::new(),
        locals: vec![LocalId(0)],
        upvalues: Vec::new(),
        temps: vec![TempId(0)],
        temp_debug_locals: Vec::new(),
        body: HirBlock {
            stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(LocalId(0))],
                values: vec![HirExpr::Closure(Box::new(HirClosureExpr {
                    proto: HirProtoRef(1),
                    captures: vec![HirCapture {
                        value: HirExpr::TempRef(TempId(0)),
                    }],
                }))],
            }))],
        },
        children: vec![HirProtoRef(1)],
    };

    assert!(resolve_recursive_closure_self_captures_in_proto(&mut proto));

    let HirStmt::Assign(assign) = &proto.body.stmts[0] else {
        panic!("expected assign");
    };
    let HirExpr::Closure(closure) = &assign.values[0] else {
        panic!("expected closure assignment");
    };
    assert!(matches!(
        closure.captures.as_slice(),
        [HirCapture {
            value: HirExpr::LocalRef(LocalId(0))
        }]
    ));
}
