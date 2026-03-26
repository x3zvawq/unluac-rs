//! 这个文件存放 HIR 初始恢复阶段的通用拼装 helper。
//!
//! 这些函数本身没有复杂语义，它们存在的意义是把反复出现的样板节点构造集中起来，
//! 避免主分析流程被 `Assign/If/Goto/Label` 之类的机械拼装淹没。这样后续如果我们要
//! 调整 fallback 形态或者 debug 展示格式，只需要收敛修改这些公共入口。

use std::collections::BTreeMap;

use crate::cfg::{BlockRef, Cfg};
use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirGoto, HirIf, HirLValue, HirLabelId, HirProto, HirProtoRef,
    HirReturn, HirStmt, HirUnresolvedExpr, HirUnstructured,
};
use crate::transformer::InstrRef;

pub(super) fn assign_stmt(targets: Vec<HirLValue>, values: Vec<HirExpr>) -> HirStmt {
    HirStmt::Assign(Box::new(HirAssign { targets, values }))
}

pub(super) fn return_stmt(values: Vec<HirExpr>) -> HirStmt {
    HirStmt::Return(Box::new(HirReturn { values }))
}

pub(super) fn goto_stmt(target: HirLabelId) -> HirStmt {
    HirStmt::Goto(Box::new(HirGoto { target }))
}

pub(super) fn goto_block(target: HirLabelId) -> HirBlock {
    HirBlock {
        stmts: vec![goto_stmt(target)],
    }
}

pub(super) fn branch_stmt(
    cond: HirExpr,
    then_block: HirBlock,
    else_block: Option<HirBlock>,
) -> HirStmt {
    HirStmt::If(Box::new(HirIf {
        cond,
        then_block,
        else_block,
    }))
}

pub(super) fn unstructured_stmt(summary: impl Into<String>) -> HirStmt {
    HirStmt::Unstructured(Box::new(HirUnstructured {
        body: HirBlock::default(),
        summary: Some(summary.into()),
    }))
}

pub(super) fn unresolved_expr(summary: impl Into<String>) -> HirExpr {
    HirExpr::Unresolved(Box::new(HirUnresolvedExpr {
        summary: summary.into(),
    }))
}

pub(super) fn label_for_block(
    cfg: &Cfg,
    label_map: &BTreeMap<BlockRef, HirLabelId>,
    target: InstrRef,
) -> HirLabelId {
    let block = cfg.instr_to_block[target.index()];
    label_map[&block]
}

pub(super) fn build_label_map_for_summary(cfg: &Cfg) -> BTreeMap<BlockRef, HirLabelId> {
    cfg.block_order
        .iter()
        .filter(|block| cfg.reachable_blocks.contains(block))
        .enumerate()
        .map(|(index, block)| (*block, HirLabelId(index)))
        .collect()
}

pub(super) fn decode_raw_string(raw: &crate::parser::RawString) -> String {
    raw.text
        .as_ref()
        .map(|text| text.value.clone())
        .unwrap_or_else(|| String::from_utf8_lossy(&raw.bytes).into_owned())
}

pub(super) fn empty_proto(id: HirProtoRef) -> HirProto {
    HirProto {
        id,
        source: None,
        line_range: crate::parser::ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: crate::parser::ProtoSignature {
            num_params: 0,
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
        },
        params: Vec::new(),
        locals: Vec::new(),
        upvalues: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body: HirBlock::default(),
        children: Vec::new(),
    }
}
