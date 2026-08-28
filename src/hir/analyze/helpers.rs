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
        targets,
        values: values.into(),
    }))
}

pub(super) fn return_stmt(values: HirValuePack) -> HirStmt {
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

pub(super) fn unresolved_expr(summary: impl Into<String>) -> HirExpr {
    HirExpr::Unresolved(Box::new(HirUnresolvedExpr {
        summary: summary.into(),
    }))
}

pub(super) fn concat_expr(parts: impl IntoIterator<Item = HirExpr>) -> HirExpr {
    let mut parts = parts.into_iter().collect::<Vec<_>>();
    let Some(last) = parts.pop() else {
        return unresolved_expr("concat empty source");
    };
    // Lua 源码里的 `..` 默认是右结合；CONCAT 指令只告诉我们“这一串值需要拼接”，
    // 不携带显式括号。这里统一用右折叠做 canonical shape，避免不同 lowering 路径
    // 各自长出一份左折叠实现，最后再让后层被迫补括号。
    parts.into_iter().rfold(last, |rhs, lhs| {
        HirExpr::Binary(Box::new(crate::hir::common::HirBinaryExpr {
            op: crate::hir::common::HirBinaryOpKind::Concat,
            lhs,
            rhs,
        }))
    })
}

pub(super) fn binary_expr(op: HirBinaryOpKind, lhs: HirExpr, rhs: HirExpr) -> HirExpr {
    HirExpr::Binary(Box::new(HirBinaryExpr { op, lhs, rhs }))
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
        },
        params: Vec::new(),
        param_debug_hints: Vec::new(),
        locals: Vec::new(),
        local_debug_hints: Vec::new(),
        physical_root_locals: BTreeSet::new(),
        upvalues: Vec::new(),
        upvalue_debug_hints: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        temp_debug_scopes: Vec::new(),
        body: HirBlock::default(),
        children: Vec::new(),
        failure: None,
        detached_children: Vec::new(),
    }
}
