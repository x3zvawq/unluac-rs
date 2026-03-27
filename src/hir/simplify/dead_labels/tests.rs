use crate::hir::{HirBlock, HirGoto, HirLabel, HirLabelId, HirProto, HirProtoRef, HirStmt};
use crate::parser::{ProtoLineRange, ProtoSignature};

use super::remove_unused_labels_in_proto;

#[test]
fn drops_unreferenced_entry_and_pad_labels() {
    let mut proto = empty_proto(vec![
        HirStmt::Label(Box::new(HirLabel { id: HirLabelId(0) })),
        HirStmt::Label(Box::new(HirLabel { id: HirLabelId(1) })),
        HirStmt::Goto(Box::new(HirGoto {
            target: HirLabelId(2),
        })),
        HirStmt::Label(Box::new(HirLabel { id: HirLabelId(2) })),
    ]);

    assert!(remove_unused_labels_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Goto(_), HirStmt::Label(label)] if label.id == HirLabelId(2)
    ));
}

#[test]
fn keeps_referenced_nested_label() {
    let mut proto = empty_proto(vec![HirStmt::Block(Box::new(HirBlock {
        stmts: vec![
            HirStmt::Goto(Box::new(HirGoto {
                target: HirLabelId(1),
            })),
            HirStmt::Label(Box::new(HirLabel { id: HirLabelId(0) })),
            HirStmt::Label(Box::new(HirLabel { id: HirLabelId(1) })),
        ],
    }))]);

    assert!(remove_unused_labels_in_proto(&mut proto));
    let HirStmt::Block(block) = &proto.body.stmts[0] else {
        panic!("expected nested block");
    };
    assert!(matches!(
        block.stmts.as_slice(),
        [HirStmt::Goto(_), HirStmt::Label(label)] if label.id == HirLabelId(1)
    ));
}

fn empty_proto(stmts: Vec<HirStmt>) -> HirProto {
    HirProto {
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
        locals: Vec::new(),
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body: HirBlock { stmts },
        children: Vec::new(),
    }
}
