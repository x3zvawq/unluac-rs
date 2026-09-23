//! 这个文件存放 HIR 初始恢复阶段的通用拼装 helper。
//!
//! 这些函数本身没有复杂语义，它们存在的意义是把反复出现的样板节点构造集中起来，
//! 避免主分析流程被 `Assign/If/Goto/Label` 之类的机械拼装淹没。这样后续如果我们要
//! 调整 fallback 形态或者 debug 展示格式，只需要收敛修改这些公共入口。

use std::collections::BTreeSet;

use crate::hir::common::{
    HirAssign, HirBinaryExpr, HirBinaryOpKind, HirBlock, HirExpr, HirGoto, HirIf, HirLValue,
    HirLabelId, HirProto, HirProtoRef, HirReturn, HirStmt, HirUnresolvedExpr, HirValuePack,
};

pub(super) fn assign_stmt(targets: Vec<HirLValue>, values: impl Into<HirValuePack>) -> HirStmt {
    HirStmt::Assign(Box::new(HirAssign {
        luau_compound_global: false,
        upvalue_write_source: None,
        is_phi_transfer: false,
        parallel_nil_frame: None,
        targets,
        values: values.into(),
        initializer_merge_transaction: None,
        generic_for_initializer_producer: None,
        generic_for_dispatch_release: None,
        method_rewrite_transaction: None,
    }))
}

pub(super) fn return_stmt(
    values: HirValuePack,
    frame_source: Option<crate::hir::common::HirSourceSite>,
    pending_cleanup_source: Option<crate::transformer::InstrRef>,
) -> HirStmt {
    HirStmt::Return(Box::new(HirReturn {
        frame_source,
        pending_cleanup_source,
        values,
    }))
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
        preserves_empty_test: false,
        then_block,
        else_block,
    }))
}

pub(super) fn unresolved_expr(summary: impl Into<String>) -> HirExpr {
    HirExpr::Unresolved(Box::new(HirUnresolvedExpr {
        summary: summary.into(),
    }))
}

pub(super) fn concat_expr(
    source_site: crate::hir::common::HirSourceSite,
    parts: impl IntoIterator<Item = HirExpr>,
) -> HirExpr {
    HirBinaryExpr::concat(source_site, parts.into_iter().collect())
        .unwrap_or_else(|| unresolved_expr("concat empty source"))
}

pub(super) fn binary_expr(
    source_site: crate::hir::common::HirSourceSite,
    op: HirBinaryOpKind,
    lhs: HirExpr,
    rhs: HirExpr,
) -> HirExpr {
    HirExpr::Binary(Box::new(HirBinaryExpr {
        source_site: Some(source_site),
        op,
        lhs,
        rhs,
    }))
}

pub(super) fn decode_raw_string(raw: &crate::parser::RawString) -> String {
    raw.text
        .as_ref()
        .map(|text| text.value.to_string())
        .unwrap_or_else(|| String::from_utf8_lossy(&raw.bytes).into_owned())
}

pub(super) fn raw_lua_string(raw: &crate::parser::RawString) -> crate::LuaString {
    crate::LuaString::from_raw(raw)
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
            legacy_arg_slot: false,
            legacy_arg_table: false,
        },
        params: Vec::new(),
        param_debug_hints: Vec::new(),
        local_count: 0,
        vararg_param_local: None,
        local_debug_hints: Vec::new(),
        local_debug_scopes: Vec::new(),
        debug_scopes: Vec::new(),
        physical_root_temps: BTreeSet::new(),
        physical_root_locals: BTreeSet::new(),
        inline_dispositions: Default::default(),
        upvalues: Vec::new(),
        environment_upvalues: BTreeSet::new(),
        lexical_environment_local: None,
        mutable_upvalues: BTreeSet::new(),
        upvalue_debug_hints: Vec::new(),
        temp_count: 0,
        temp_debug_locals: Vec::new(),
        temp_debug_scopes: Vec::new(),
        exit_requirements: Vec::new(),
        body: HirBlock::default(),
        children: Vec::new(),
        failure: None,
        detached_children: Vec::new(),
    }
}
