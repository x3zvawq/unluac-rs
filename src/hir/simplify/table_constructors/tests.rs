//! 这个文件承载 `table_constructors` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use super::*;

use crate::hir::common::{
    HirAssign, HirExpr, HirLValue, HirReturn, HirTableField, HirTableSetList,
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
