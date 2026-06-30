//! 参数 alias 收敛是 locals pass 的后置步骤。
//!
//! locals pass 把跨语句存活的 temp 提升成 local 后，函数入口处可能出现机械别名：
//! `local L = P` 或 `local L; L = P`。如果后续代码只通过这个别名继续读写参数槽位，
//! 保留新 local 会把同一个源码身份拆成两个 binding，并把修复压力推给 AST/Naming。
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
//! 这里不重新推断前层 phi，也不处理循环累加器；只有参数原值不会在 alias 写入后继续
//! 被读取、alias local 没有被闭包捕获、且 alias 不在循环体内写入时才改写。

use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirLocalDecl, HirProto, HirStmt, LocalId, ParamId,
};

use super::super::mention::stmt_captures_local;
use super::super::visit::{self, HirVisitor};
use super::super::walk::{self, HirRewritePass};

pub(super) fn coalesce_param_aliases_in_proto(proto: &mut HirProto) -> bool {
    let Some(alias) = match_param_alias_prefix(&proto.body) else {
        return false;
    };
    let rest = &proto.body.stmts[alias.consumed..];
    if rest
        .iter()
        .any(|stmt| stmt_captures_local(stmt, alias.local))
        || !rest_reads_of_param_safe_against_writes_of_local(rest, alias.local, alias.param)
        || any_local_write_inside_loop(rest, alias.local)
    {
        return false;
    }

    let mut tail = proto.body.stmts.split_off(alias.consumed);
    walk::rewrite_stmts(
        &mut tail,
        &mut LocalToParamRewrite {
            local: alias.local,
            param: alias.param,
        },
    );
    proto.body.stmts.append(&mut tail);
    proto.body.stmts.drain(..alias.consumed);
    true
}

#[derive(Clone, Copy)]
struct ParamAliasPrefix {
    local: LocalId,
    param: ParamId,
    consumed: usize,
}

fn match_param_alias_prefix(block: &HirBlock) -> Option<ParamAliasPrefix> {
    match_param_alias_local_decl(block).or_else(|| match_param_alias_decl_assign(block))
}

fn match_param_alias_local_decl(block: &HirBlock) -> Option<ParamAliasPrefix> {
    let HirStmt::LocalDecl(local_decl) = block.stmts.first()? else {
        return None;
    };
    let local = single_local_binding(local_decl)?;
    let [value] = local_decl.values.as_slice() else {
        return None;
    };
    let HirExpr::ParamRef(param) = value else {
        return None;
    };
    Some(ParamAliasPrefix {
        local,
        param: *param,
        consumed: 1,
    })
}

fn match_param_alias_decl_assign(block: &HirBlock) -> Option<ParamAliasPrefix> {
    let [HirStmt::LocalDecl(local_decl), HirStmt::Assign(assign), ..] = block.stmts.as_slice()
    else {
        return None;
    };
    if !local_decl.values.is_empty() {
        return None;
    }
    let local = single_local_binding(local_decl)?;
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.as_slice() else {
        return None;
    };
    if !matches!(target, HirLValue::Local(target) if *target == local) {
        return None;
    }
    let HirExpr::ParamRef(param) = value else {
        return None;
    };
    Some(ParamAliasPrefix {
        local,
        param: *param,
        consumed: 2,
    })
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
