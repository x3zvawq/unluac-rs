//! 这个文件负责 `locals` pass 内部的 temp -> local 引用改写。
//!
//! `locals` 的主文件决定哪些 temp 可以提升、何时复用已经被 closure 捕获的 local；
//! 本文件只消费已经确定的 `TempId -> LocalId` 映射，把表达式、左值、table 构造器和
//! closure capture 里的引用改成对应 local。它不会重新判断某个 temp 是否应该提升，
//! 也不会跨语句寻找新的绑定关系。
//!
//! 输入形状：`t2 = t1 + 1`，且主 pass 已确认 `t1 -> l0`。
//! 输出形状：`t2 = l0 + 1`。

use std::collections::BTreeMap;

use crate::hir::common::{
    HirBinding, HirCallExpr, HirCapture, HirExpr, HirLValue, HirStmt, HirValuePack, LocalId, TempId,
};

use super::super::walk::{self, HirRewritePass};

pub(super) fn call_expr(call: &mut HirCallExpr, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    let callee_changed = expr(&mut call.callee, mapping);
    let args_changed = value_pack(&mut call.args, mapping);
    callee_changed || args_changed
}

pub(super) fn value_pack(pack: &mut HirValuePack, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    let mut fixed_changed = false;
    for expr in &mut pack.fixed {
        fixed_changed |= self::expr(expr, mapping);
    }
    let tail_changed = pack
        .tail
        .as_mut()
        .and_then(crate::hir::HirPackTail::call_mut)
        .is_some_and(|call| call_expr(call, mapping));
    fixed_changed || tail_changed
}

pub(super) fn expr(node: &mut HirExpr, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    walk::rewrite_expr(node, &mut TempLocalRewrite { mapping })
}

pub(super) fn lvalue(node: &mut HirLValue, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    walk::rewrite_lvalue(node, &mut TempLocalRewrite { mapping })
}

struct TempLocalRewrite<'a> {
    mapping: &'a BTreeMap<TempId, LocalId>,
}

impl HirRewritePass for TempLocalRewrite<'_> {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        if let HirExpr::TempRef(temp) = expr
            && let Some(local) = self.mapping.get(temp)
        {
            *expr = HirExpr::LocalRef(*local);
            return true;
        }
        false
    }

    fn rewrite_lvalue(&mut self, lvalue: &mut HirLValue) -> bool {
        if let HirLValue::Temp(temp) = lvalue
            && let Some(local) = self.mapping.get(temp)
        {
            *lvalue = HirLValue::Local(*local);
            return true;
        }
        false
    }

    fn rewrite_capture(&mut self, capture: &mut HirCapture) -> bool {
        rewrite_capture(capture, self.mapping)
    }
}

fn rewrite_capture(capture: &mut HirCapture, mapping: &BTreeMap<TempId, LocalId>) -> bool {
    if let HirBinding::Temp(temp) = capture.binding
        && let Some(local) = mapping.get(&temp)
    {
        capture.binding = HirBinding::Local(*local);
        return true;
    }
    false
}

/// 对语句中 closure capture 里残留的 TempRef 做定向重写。
///
/// 互递归/前向声明模式下（`local a, b; a = function() b()… end; b = function() a()… end`），
/// 第一次遍历 promote_block 时 b 的 temp 尚未加入 mapping，导致 a 的 capture 仍是
/// TempRef。这里用最终 mapping 补一次定向重写，只处理 closure capture 这一种残留，
/// 避免做全量二次遍历。
pub(super) fn forward_capture_refs(stmt: &mut HirStmt, mapping: &BTreeMap<TempId, LocalId>) {
    walk::rewrite_stmts(
        std::slice::from_mut(stmt),
        &mut ForwardCaptureRefPass { mapping },
    );
}

struct ForwardCaptureRefPass<'a> {
    mapping: &'a BTreeMap<TempId, LocalId>,
}

impl HirRewritePass for ForwardCaptureRefPass<'_> {
    fn rewrite_capture(&mut self, capture: &mut HirCapture) -> bool {
        rewrite_capture(capture, self.mapping)
    }
}
