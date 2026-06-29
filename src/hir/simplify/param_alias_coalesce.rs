//! 这个 pass 负责消除“参数槽位被提升成 local 后又只作为参数别名”的机械拆分。
//!
//! HIR 的 `locals` pass 会把跨语句存活的 temp 提升成 `local`。当这个 temp 只是函数
//! 参数的 SSA merge 结果时，继续把它交给 AST readability 会让后层承担 binding
//! 身份修复。这里直接在 HIR 把窄形状 `local L = P` 收回为对参数 `P` 的读写。
//!
//! 输入形状 -> 输出形状：
//! ```text
//! local l0 = p0             if p0 > 0 then
//! if p0 > 0 then      =>      p0 = p0 + 1
//!   l0 = p0 + 1             end
//! end                       return p0
//! return l0
//! ```
//!
//! 这个 pass 不重新推断前层 phi，也不处理循环累加器。只在参数原值不会被后续读取、
//! alias local 没有被闭包捕获、且 alias 不在循环体内写入时才改写。

use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirLocalDecl, HirProto, HirStmt, LocalId, ParamId,
};

use super::mention::expr_mentions_local;
use super::visit::{self, HirVisitor};
use super::walk::{self, HirRewritePass};

pub(super) fn coalesce_param_aliases_in_proto(proto: &mut HirProto) -> bool {
    let Some((local, param)) = match_param_alias_first_stmt(&proto.body) else {
        return false;
    };
    let rest = &proto.body.stmts[1..];
    if rest.iter().any(|stmt| stmt_captures_local(stmt, local))
        || !rest_reads_of_param_safe_against_writes_of_local(rest, local, param)
        || any_local_write_inside_loop(rest, local)
    {
        return false;
    }

    let mut tail = proto.body.stmts.split_off(1);
    walk::rewrite_stmts(&mut tail, &mut LocalToParamRewrite { local, param });
    proto.body.stmts.append(&mut tail);
    proto.body.stmts.remove(0);
    true
}

fn match_param_alias_first_stmt(block: &HirBlock) -> Option<(LocalId, ParamId)> {
    let first = block.stmts.first()?;
    let HirStmt::LocalDecl(local_decl) = first else {
        return None;
    };
    let local = single_local_binding(local_decl)?;
    let [value] = local_decl.values.as_slice() else {
        return None;
    };
    let HirExpr::ParamRef(param) = value else {
        return None;
    };
    Some((local, *param))
}

fn single_local_binding(local_decl: &HirLocalDecl) -> Option<LocalId> {
    let [local] = local_decl.bindings.as_slice() else {
        return None;
    };
    Some(*local)
}

fn rest_reads_of_param_safe_against_writes_of_local(
    stmts: &[HirStmt],
    local: LocalId,
    param: ParamId,
) -> bool {
    let mut seen_local_write = false;
    for stmt in stmts {
        if stmt_reads_param(stmt, param) && seen_local_write {
            return false;
        }
        seen_local_write |= stmt_writes_local(stmt, local);
    }
    true
}

fn any_local_write_inside_loop(stmts: &[HirStmt], local: LocalId) -> bool {
    stmts
        .iter()
        .any(|stmt| stmt_has_local_write_inside_loop(stmt, local))
}

fn stmt_has_local_write_inside_loop(stmt: &HirStmt, local: LocalId) -> bool {
    match stmt {
        HirStmt::While(while_stmt) => block_writes_local(&while_stmt.body, local),
        HirStmt::Repeat(repeat_stmt) => block_writes_local(&repeat_stmt.body, local),
        HirStmt::NumericFor(numeric_for) => block_writes_local(&numeric_for.body, local),
        HirStmt::GenericFor(generic_for) => block_writes_local(&generic_for.body, local),
        HirStmt::If(if_stmt) => {
            any_local_write_inside_loop(&if_stmt.then_block.stmts, local)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| any_local_write_inside_loop(&block.stmts, local))
        }
        HirStmt::Block(block) => any_local_write_inside_loop(&block.stmts, local),
        HirStmt::Unstructured(unstructured) => {
            any_local_write_inside_loop(&unstructured.body.stmts, local)
        }
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

fn block_writes_local(block: &HirBlock, local: LocalId) -> bool {
    block
        .stmts
        .iter()
        .any(|stmt| stmt_writes_local(stmt, local))
}

fn stmt_writes_local(stmt: &HirStmt, local: LocalId) -> bool {
    let mut collector = LocalWriteCollector {
        local,
        written: false,
    };
    visit::visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.written
}

struct LocalWriteCollector {
    local: LocalId,
    written: bool,
}

impl HirVisitor for LocalWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.written |= matches!(lvalue, HirLValue::Local(local) if *local == self.local);
    }
}

fn stmt_reads_param(stmt: &HirStmt, param: ParamId) -> bool {
    let mut collector = ParamReadCollector { param, read: false };
    visit::visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.read
}

struct ParamReadCollector {
    param: ParamId,
    read: bool,
}

impl HirVisitor for ParamReadCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.read |= matches!(expr, HirExpr::ParamRef(param) if *param == self.param);
    }
}

fn stmt_captures_local(stmt: &HirStmt, local: LocalId) -> bool {
    let mut collector = LocalCaptureCollector {
        local,
        captured: false,
    };
    visit::visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.captured
}

struct LocalCaptureCollector {
    local: LocalId,
    captured: bool,
}

impl HirVisitor for LocalCaptureCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::Closure(closure) = expr {
            self.captured |= closure
                .captures
                .iter()
                .any(|capture| expr_mentions_local(&capture.value, self.local));
        }
    }
}

struct LocalToParamRewrite {
    local: LocalId,
    param: ParamId,
}

impl HirRewritePass for LocalToParamRewrite {
    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        if matches!(expr, HirExpr::LocalRef(local) if *local == self.local) {
            *expr = HirExpr::ParamRef(self.param);
            return true;
        }
        false
    }

    fn rewrite_lvalue(&mut self, lvalue: &mut HirLValue) -> bool {
        if matches!(lvalue, HirLValue::Local(local) if *local == self.local) {
            *lvalue = HirLValue::Param(self.param);
            return true;
        }
        false
    }
}
