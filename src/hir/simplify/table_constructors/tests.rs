//! 这个文件承载 `table_constructors` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use super::*;

use crate::hir::common::{
    HirAssign, HirBlock, HirCallExpr, HirClosureExpr, HirExpr, HirGlobalRef, HirLValue,
    HirLocalDecl, HirReturn, HirStmt, HirTableField, HirTableKey, HirTableSetList,
};
use crate::parser::{ProtoLineRange, ProtoSignature};

#[test]
fn greedily_consumes_adjacent_set_list_chunks_in_single_pass() {
    let table = TempId(0);
    let value_a = TempId(1);
    let value_b = TempId(2);

    let mut proto = HirProto {
        id: crate::hir::common::HirProtoRef(0),
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
        locals: Vec::new(),
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        temps: vec![table, value_a, value_b],
        temp_debug_locals: vec![None, None, None],
        body: HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(table)],
                    values: vec![HirExpr::TableConstructor(Box::default())],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(value_a)],
                    values: vec![HirExpr::Integer(1)],
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::TempRef(table),
                    values: vec![HirExpr::TempRef(value_a)],
                    trailing_multivalue: None,
                    start_index: 1,
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(value_b)],
                    values: vec![HirExpr::Integer(2)],
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::TempRef(table),
                    values: vec![HirExpr::TempRef(value_b)],
                    trailing_multivalue: None,
                    start_index: 2,
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(table)],
                })),
            ],
        },
        children: Vec::new(),
    };

    let changed = stabilize_table_constructors_in_proto(&mut proto);
    assert!(changed);

    let body = &proto.body;
    assert_eq!(body.stmts.len(), 2);
    let HirStmt::Assign(assign) = &body.stmts[0] else {
        panic!("expected constructor seed assignment to remain");
    };
    let [HirExpr::TableConstructor(table)] = assign.values.as_slice() else {
        panic!("expected constructor seed to be rewritten into a table constructor");
    };
    assert_eq!(
        table.fields,
        vec![
            HirTableField::Array(HirExpr::Integer(1)),
            HirTableField::Array(HirExpr::Integer(2))
        ]
    );
    assert!(table.trailing_multivalue.is_none());
}

#[test]
fn absorbs_terminal_global_handoff_for_single_use_constructor_seed() {
    let table_local = LocalId(0);

    let mut proto = HirProto {
        id: crate::hir::common::HirProtoRef(0),
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
        locals: vec![table_local],
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![table_local],
                    values: vec![HirExpr::TableConstructor(Box::new(
                        crate::hir::common::HirTableConstructor {
                            fields: vec![
                                HirTableField::Record(crate::hir::common::HirRecordField {
                                    key: HirTableKey::Name("answer".to_owned()),
                                    value: HirExpr::Integer(42),
                                }),
                                HirTableField::Array(HirExpr::String("tail".to_owned())),
                            ],
                            trailing_multivalue: None,
                        },
                    ))],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Global(HirGlobalRef {
                        name: "payload".to_owned(),
                    })],
                    values: vec![HirExpr::LocalRef(table_local)],
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::GlobalRef(HirGlobalRef {
                        name: "payload".to_owned(),
                    })],
                })),
            ],
        },
        children: Vec::new(),
    };

    assert!(stabilize_table_constructors_in_proto(&mut proto));
    assert_eq!(proto.body.stmts.len(), 2);

    let HirStmt::Assign(assign) = &proto.body.stmts[0] else {
        panic!("constructor seed should retarget into final global assignment");
    };
    assert!(matches!(
        assign.targets.as_slice(),
        [HirLValue::Global(global)] if global.name == "payload"
    ));
    let [HirExpr::TableConstructor(constructor)] = assign.values.as_slice() else {
        panic!("retargeted handoff should keep constructor literal");
    };
    assert!(matches!(
        constructor.fields.as_slice(),
        [
            HirTableField::Record(field),
            HirTableField::Array(HirExpr::String(tail)),
        ] if matches!(field.key, HirTableKey::Name(ref name) if name == "answer")
            && matches!(field.value, HirExpr::Integer(42))
            && tail == "tail"
    ));
}

#[test]
fn absorbs_constructor_region_before_terminal_global_handoff() {
    let table_local = LocalId(0);

    let mut proto = HirProto {
        id: crate::hir::common::HirProtoRef(0),
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
        locals: vec![table_local],
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![table_local],
                    values: vec![HirExpr::TableConstructor(Box::default())],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::LocalRef(table_local),
                            key: HirExpr::String("answer".to_owned()),
                        },
                    ))],
                    values: vec![HirExpr::Integer(42)],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Global(HirGlobalRef {
                        name: "payload".to_owned(),
                    })],
                    values: vec![HirExpr::LocalRef(table_local)],
                })),
            ],
        },
        children: Vec::new(),
    };

    assert!(stabilize_table_constructors_in_proto(&mut proto));
    assert_eq!(proto.body.stmts.len(), 1);

    let HirStmt::Assign(assign) = &proto.body.stmts[0] else {
        panic!("constructor region should collapse into final global assignment");
    };
    let [HirExpr::TableConstructor(constructor)] = assign.values.as_slice() else {
        panic!("collapsed region should leave a constructor literal");
    };
    assert!(matches!(
        constructor.fields.as_slice(),
        [HirTableField::Record(field)]
            if matches!(field.key, HirTableKey::Name(ref name) if name == "answer")
                && matches!(field.value, HirExpr::Integer(42))
    ));
}

#[test]
fn keeps_constructor_seed_when_binding_is_used_after_handoff() {
    let table_local = LocalId(0);

    let mut proto = HirProto {
        id: crate::hir::common::HirProtoRef(0),
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
        locals: vec![table_local],
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![table_local],
                    values: vec![HirExpr::TableConstructor(Box::default())],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Global(HirGlobalRef {
                        name: "payload".to_owned(),
                    })],
                    values: vec![HirExpr::LocalRef(table_local)],
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::LocalRef(table_local)],
                })),
            ],
        },
        children: Vec::new(),
    };

    assert!(!stabilize_table_constructors_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [
            HirStmt::LocalDecl(_),
            HirStmt::Assign(_),
            HirStmt::Return(_)
        ]
    ));
}

#[test]
fn folds_set_list_with_trailing_multivalue_into_constructor_tail() {
    let closure = LocalId(0);
    let table_local = LocalId(1);
    let print_local = LocalId(2);
    let label_local = LocalId(3);
    let concat_local = LocalId(4);

    let mut proto = HirProto {
        id: crate::hir::common::HirProtoRef(0),
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
        locals: vec![closure, table_local, print_local, label_local, concat_local],
        upvalues: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        local_debug_hints: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![closure],
                    values: vec![HirExpr::GlobalRef(HirGlobalRef {
                        name: "returns".to_owned(),
                    })],
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![table_local],
                    values: vec![HirExpr::TableConstructor(Box::default())],
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(table_local),
                    values: vec![
                        HirExpr::Call(Box::new(HirCallExpr {
                            callee: HirExpr::LocalRef(closure),
                            args: Vec::new(),
                            multiret: false,
                            method: false,
                            method_name: None,
                        })),
                        HirExpr::String("tail".to_owned()),
                    ],
                    trailing_multivalue: Some(HirExpr::Call(Box::new(HirCallExpr {
                        callee: HirExpr::LocalRef(closure),
                        args: Vec::new(),
                        multiret: true,
                        method: false,
                        method_name: None,
                    }))),
                    start_index: 1,
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![print_local],
                    values: vec![HirExpr::GlobalRef(HirGlobalRef {
                        name: "print".to_owned(),
                    })],
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![label_local],
                    values: vec![HirExpr::String("ret".to_owned())],
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![concat_local],
                    values: vec![HirExpr::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::GlobalRef(HirGlobalRef {
                                name: "table".to_owned(),
                            }),
                            key: HirExpr::String("concat".to_owned()),
                        },
                    ))],
                })),
                HirStmt::CallStmt(Box::new(crate::hir::common::HirCallStmt {
                    call: HirCallExpr {
                        callee: HirExpr::LocalRef(print_local),
                        args: vec![
                            HirExpr::LocalRef(label_local),
                            HirExpr::Call(Box::new(HirCallExpr {
                                callee: HirExpr::LocalRef(concat_local),
                                args: vec![
                                    HirExpr::LocalRef(table_local),
                                    HirExpr::String(",".to_owned()),
                                ],
                                multiret: true,
                                method: false,
                                method_name: None,
                            })),
                        ],
                        multiret: false,
                        method: false,
                        method_name: None,
                    },
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::LocalRef(table_local)],
                })),
            ],
        },
        children: Vec::new(),
    };

    let changed = stabilize_table_constructors_in_proto(&mut proto);
    assert!(changed);

    assert_eq!(proto.body.stmts.len(), 7);
    assert!(
        proto
            .body
            .stmts
            .iter()
            .all(|stmt| !matches!(stmt, HirStmt::TableSetList(_)))
    );

    let HirStmt::LocalDecl(seed) = &proto.body.stmts[1] else {
        panic!("expected constructor seed to stay a local decl");
    };
    let [HirExpr::TableConstructor(table_ctor)] = seed.values.as_slice() else {
        panic!("expected constructor seed to be rewritten into a table constructor");
    };
    assert_eq!(table_ctor.fields.len(), 2);
    assert!(matches!(
        table_ctor.fields.as_slice(),
        [
            HirTableField::Array(HirExpr::Call(call)),
            HirTableField::Array(HirExpr::String(value)),
        ] if !call.multiret && value == "tail"
    ));
    assert!(matches!(
        table_ctor.trailing_multivalue.as_ref(),
        Some(HirExpr::Call(call)) if call.multiret
    ));
    let ret = proto
        .body
        .stmts
        .last()
        .expect("rewritten constructor region should still end with return");
    assert!(matches!(
        ret,
        HirStmt::Return(ret) if matches!(ret.values.as_slice(), [HirExpr::LocalRef(local)] if local == &table_local)
    ));
}

#[test]
fn folds_set_list_with_open_pack_barrier_into_constructor_tail() {
    let table_local = LocalId(0);
    let first_value = TempId(0);
    let second_value = TempId(1);

    let mut proto = HirProto {
        id: crate::hir::common::HirProtoRef(0),
        source: None,
        line_range: ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: ProtoSignature {
            num_params: 0,
            is_vararg: true,
            has_vararg_param_reg: false,
            named_vararg_table: false,
        },
        params: Vec::new(),
        locals: vec![table_local],
        upvalues: Vec::new(),
        temps: vec![first_value, second_value],
        temp_debug_locals: vec![None, None],
        local_debug_hints: vec![None],
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![table_local],
                    values: vec![HirExpr::TableConstructor(Box::default())],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(first_value), HirLValue::Temp(second_value)],
                    values: vec![HirExpr::VarArg],
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(table_local),
                    values: vec![
                        HirExpr::TempRef(first_value),
                        HirExpr::String("barrier".to_owned()),
                    ],
                    trailing_multivalue: Some(HirExpr::VarArg),
                    start_index: 1,
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::LocalRef(table_local)],
                })),
            ],
        },
        children: Vec::new(),
    };

    let changed = stabilize_table_constructors_in_proto(&mut proto);
    assert!(changed);
    assert_eq!(proto.body.stmts.len(), 2);
    assert!(
        proto
            .body
            .stmts
            .iter()
            .all(|stmt| !matches!(stmt, HirStmt::TableSetList(_) | HirStmt::Assign(_)))
    );

    let HirStmt::LocalDecl(seed) = &proto.body.stmts[0] else {
        panic!("expected constructor seed to stay a local decl");
    };
    let [HirExpr::TableConstructor(table_ctor)] = seed.values.as_slice() else {
        panic!("expected constructor seed to be rewritten into a table constructor");
    };
    assert_eq!(
        table_ctor.fields,
        vec![
            HirTableField::Array(HirExpr::VarArg),
            HirTableField::Array(HirExpr::String("barrier".to_owned())),
        ]
    );
    assert_eq!(table_ctor.trailing_multivalue, Some(HirExpr::VarArg));
}

#[test]
fn folds_mixed_record_and_array_constructor_with_closure_field_and_trailing_multivalue() {
    let table_local = LocalId(0);
    let v1 = LocalId(1);
    let v2 = LocalId(2);
    let v3 = LocalId(3);
    let v4 = LocalId(4);
    let v5 = LocalId(5);
    let byte_fn = LocalId(6);

    let mut proto = HirProto {
        id: crate::hir::common::HirProtoRef(0),
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
        locals: vec![table_local, v1, v2, v3, v4, v5, byte_fn],
        upvalues: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        local_debug_hints: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![table_local],
                    values: vec![HirExpr::TableConstructor(Box::default())],
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![v1],
                    values: vec![HirExpr::Integer(1)],
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![v2],
                    values: vec![HirExpr::Integer(2)],
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![v3],
                    values: vec![HirExpr::Integer(3)],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::LocalRef(table_local),
                            key: HirExpr::String("a".to_owned()),
                        },
                    ))],
                    values: vec![HirExpr::Integer(4)],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::LocalRef(table_local),
                            key: HirExpr::Integer(5),
                        },
                    ))],
                    values: vec![HirExpr::Integer(6)],
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![v4],
                    values: vec![HirExpr::Integer(7)],
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![v5],
                    values: vec![HirExpr::Integer(8)],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::LocalRef(table_local),
                            key: HirExpr::String("f".to_owned()),
                        },
                    ))],
                    values: vec![HirExpr::Closure(Box::new(HirClosureExpr {
                        proto: crate::hir::common::HirProtoRef(1),
                        captures: Vec::new(),
                    }))],
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![byte_fn],
                    values: vec![HirExpr::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::GlobalRef(HirGlobalRef {
                                name: "string".to_owned(),
                            }),
                            key: HirExpr::String("byte".to_owned()),
                        },
                    ))],
                })),
                HirStmt::TableSetList(Box::new(HirTableSetList {
                    base: HirExpr::LocalRef(table_local),
                    values: vec![
                        HirExpr::LocalRef(v1),
                        HirExpr::LocalRef(v2),
                        HirExpr::LocalRef(v3),
                        HirExpr::LocalRef(v4),
                        HirExpr::LocalRef(v5),
                    ],
                    trailing_multivalue: Some(HirExpr::Call(Box::new(HirCallExpr {
                        callee: HirExpr::LocalRef(byte_fn),
                        args: vec![HirExpr::String("A".to_owned())],
                        multiret: true,
                        method: false,
                        method_name: None,
                    }))),
                    start_index: 1,
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::LocalRef(table_local)],
                })),
            ],
        },
        children: vec![crate::hir::common::HirProtoRef(1)],
    };

    let changed = stabilize_table_constructors_in_proto(&mut proto);
    assert!(changed);
    assert!(
        proto
            .body
            .stmts
            .iter()
            .all(|stmt| !matches!(stmt, HirStmt::TableSetList(_)))
    );

    let HirStmt::LocalDecl(seed) = &proto.body.stmts[0] else {
        panic!("expected table seed local");
    };
    let [HirExpr::TableConstructor(table_ctor)] = seed.values.as_slice() else {
        panic!("expected rebuilt table constructor");
    };
    assert_eq!(table_ctor.fields.len(), 8);
    assert!(matches!(
        table_ctor.fields.as_slice(),
        [
            HirTableField::Array(HirExpr::Integer(1)),
            HirTableField::Array(HirExpr::Integer(2)),
            HirTableField::Array(HirExpr::Integer(3)),
            HirTableField::Record(record_a),
            HirTableField::Record(record_five),
            HirTableField::Array(HirExpr::Integer(7)),
            HirTableField::Array(HirExpr::Integer(8)),
            HirTableField::Record(record_f),
        ]
        if matches!(record_a.key, HirTableKey::Name(ref name) if name == "a")
            && matches!(record_a.value, HirExpr::Integer(4))
            && matches!(record_five.key, HirTableKey::Expr(HirExpr::Integer(5)))
            && matches!(record_five.value, HirExpr::Integer(6))
            && matches!(record_f.key, HirTableKey::Name(ref name) if name == "f")
            && matches!(record_f.value, HirExpr::Closure(_))
    ));
    let Some(HirExpr::Call(call)) = table_ctor.trailing_multivalue.as_ref() else {
        panic!("expected trailing multivalue call to be preserved");
    };
    assert!(call.multiret);
    let HirExpr::TableAccess(access) = &call.callee else {
        panic!("expected trailing call callee to inline into string.byte access");
    };
    assert!(matches!(
        access.base,
        HirExpr::GlobalRef(ref global) if global.name == "string"
    ));
    assert!(matches!(
        access.key,
        HirExpr::String(ref key) if key == "byte"
    ));
}

#[test]
fn does_not_fold_closure_backed_record_writes_into_constructor() {
    let table_local = LocalId(0);
    let closure_local = LocalId(1);

    let mut proto = HirProto {
        id: crate::hir::common::HirProtoRef(0),
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
        locals: vec![table_local, closure_local],
        upvalues: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        local_debug_hints: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![table_local],
                    values: vec![HirExpr::TableConstructor(Box::default())],
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![closure_local],
                    values: vec![HirExpr::Closure(Box::new(HirClosureExpr {
                        proto: crate::hir::common::HirProtoRef(1),
                        captures: Vec::new(),
                    }))],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::LocalRef(table_local),
                            key: HirExpr::String("method".to_owned()),
                        },
                    ))],
                    values: vec![HirExpr::LocalRef(closure_local)],
                })),
            ],
        },
        children: Vec::new(),
    };

    let changed = stabilize_table_constructors_in_proto(&mut proto);
    assert!(!changed);
    assert_eq!(proto.body.stmts.len(), 3);
    let HirStmt::LocalDecl(seed) = &proto.body.stmts[0] else {
        panic!("table seed should stay a local decl");
    };
    let [HirExpr::TableConstructor(table_ctor)] = seed.values.as_slice() else {
        panic!("expected original table constructor seed");
    };
    assert!(table_ctor.fields.is_empty());
}

#[test]
fn folds_expr_keyed_closure_backed_record_writes_into_constructor() {
    let table_local = LocalId(0);
    let closure_local = LocalId(1);

    let mut proto = HirProto {
        id: crate::hir::common::HirProtoRef(0),
        source: None,
        line_range: ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: ProtoSignature {
            num_params: 1,
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
        },
        params: vec![crate::hir::ParamId(0)],
        locals: vec![table_local, closure_local],
        upvalues: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        local_debug_hints: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![table_local],
                    values: vec![HirExpr::TableConstructor(Box::default())],
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![closure_local],
                    values: vec![HirExpr::Closure(Box::new(HirClosureExpr {
                        proto: crate::hir::common::HirProtoRef(1),
                        captures: Vec::new(),
                    }))],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::LocalRef(table_local),
                            key: HirExpr::ParamRef(crate::hir::ParamId(0)),
                        },
                    ))],
                    values: vec![HirExpr::LocalRef(closure_local)],
                })),
            ],
        },
        children: Vec::new(),
    };

    let changed = stabilize_table_constructors_in_proto(&mut proto);
    assert!(changed);
    assert_eq!(proto.body.stmts.len(), 1);
    let HirStmt::LocalDecl(seed) = &proto.body.stmts[0] else {
        panic!("table seed should stay a local decl");
    };
    let [HirExpr::TableConstructor(table_ctor)] = seed.values.as_slice() else {
        panic!("expected constructor seed to absorb expr-keyed closure record");
    };
    assert!(matches!(
        table_ctor.fields.as_slice(),
        [HirTableField::Record(field)]
            if matches!(&field.key, HirTableKey::Expr(HirExpr::ParamRef(crate::hir::ParamId(0))))
                && matches!(field.value, HirExpr::Closure(_))
    ));
}

#[test]
fn does_not_fold_recursive_local_function_slot_into_expr_keyed_constructor_field() {
    let table_local = LocalId(0);
    let function_local = LocalId(1);

    let mut proto = HirProto {
        id: crate::hir::common::HirProtoRef(0),
        source: None,
        line_range: ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: ProtoSignature {
            num_params: 1,
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
        },
        params: vec![crate::hir::ParamId(0)],
        locals: vec![table_local, function_local],
        upvalues: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        local_debug_hints: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![table_local],
                    values: vec![HirExpr::TableConstructor(Box::default())],
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![function_local],
                    values: vec![HirExpr::Closure(Box::new(HirClosureExpr {
                        proto: crate::hir::common::HirProtoRef(1),
                        captures: vec![crate::hir::common::HirCapture {
                            value: HirExpr::LocalRef(function_local),
                        }],
                    }))],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::LocalRef(table_local),
                            key: HirExpr::ParamRef(crate::hir::ParamId(0)),
                        },
                    ))],
                    values: vec![HirExpr::LocalRef(function_local)],
                })),
            ],
        },
        children: Vec::new(),
    };

    let changed = stabilize_table_constructors_in_proto(&mut proto);
    assert!(!changed);
    assert_eq!(proto.body.stmts.len(), 3);
}

#[test]
fn does_not_fold_direct_recursive_closure_when_capture_slot_has_no_surviving_binding_site() {
    let table_local = LocalId(0);
    let recursive_slot = LocalId(1);

    let mut proto = HirProto {
        id: crate::hir::common::HirProtoRef(0),
        source: None,
        line_range: ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: ProtoSignature {
            num_params: 1,
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
        },
        params: vec![crate::hir::ParamId(0)],
        locals: vec![table_local, recursive_slot],
        upvalues: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        local_debug_hints: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![table_local],
                    values: vec![HirExpr::TableConstructor(Box::default())],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::LocalRef(table_local),
                            key: HirExpr::ParamRef(crate::hir::ParamId(0)),
                        },
                    ))],
                    values: vec![HirExpr::Closure(Box::new(HirClosureExpr {
                        proto: crate::hir::common::HirProtoRef(1),
                        captures: vec![crate::hir::common::HirCapture {
                            value: HirExpr::LocalRef(recursive_slot),
                        }],
                    }))],
                })),
            ],
        },
        children: Vec::new(),
    };

    let changed = stabilize_table_constructors_in_proto(&mut proto);
    assert!(!changed);
    assert_eq!(proto.body.stmts.len(), 2);
}
