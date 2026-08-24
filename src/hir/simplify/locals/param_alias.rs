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
//! 这里不重新推断前层 phi，也不处理任意 local 对；它只沿结构化语句证明参数与 alias
//! 从入口相同值开始不会被分别观察。alias 一旦在某条路径写入，该路径后续不得再读取
//! 原参数；循环还会用“alias 已写入”的状态验证下一轮。参数写入、引用 capture 与 goto
//! 会直接拒绝，alias local 被任意 closure 捕获时也不会改写。
//! alias 后续写入会提前覆盖参数，因此还要求两者属于同一可信物理 home；仅有显式读写
//! 等价不足以排除弱表、`__gc` 或异常 cleanup 对旧参数存活期的观察。
//! 实际发生的 `Local -> Param` 引用改写还会把失效的 home provenance 传播到参数，避免
//! deferred carried-local 的下一轮把换壳后的参数重新当作可信物理槽。

use crate::hir::common::{
    HirBlock, HirExpr, HirLValue, HirLocalDecl, HirProto, HirStmt, LocalId, ParamId,
};
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::mention::{
    expr_mentions_local, stmt_captures_local, stmts_reference_captured_bindings,
};
use super::super::visit::{self, HirVisitor};
use super::super::walk::{self, HirRewritePass};

pub(super) fn coalesce_param_aliases_in_proto(
    proto: &mut HirProto,
    promotion_facts: &mut ProtoPromotionFacts,
) -> bool {
    let Some(alias) = match_param_alias_prefix(&proto.body) else {
        return false;
    };
    let shares_exact_home = promotion_facts
        .trusted_local_home_slot(alias.local)
        .zip(promotion_facts.trusted_param_home_slot(alias.param))
        .is_some_and(|(local, param)| local == param);
    let rest = &proto.body.stmts[alias.consumed..];
    if promotion_facts.compacts_home_slots()
        || promotion_facts.entry_nil_writes_were_pruned(alias.local)
        || !shares_exact_home
        || rest
            .iter()
            .any(|stmt| stmt_captures_local(stmt, alias.local))
        || !rest_preserves_param_alias_identity(rest, alias.local, alias.param)
    {
        return false;
    }

    let mut tail = proto.body.stmts.split_off(alias.consumed);
    let rewritten = walk::rewrite_stmts(
        &mut tail,
        &mut LocalToParamRewrite {
            local: alias.local,
            param: alias.param,
        },
    );
    if rewritten {
        promotion_facts.record_local_to_param_merge(alias.local, alias.param);
    }
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
    let [value] = local_decl.values.fixed.as_slice() else {
        return None;
    };
    if local_decl.values.tail.is_some() {
        return None;
    }
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
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
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

fn rest_preserves_param_alias_identity(stmts: &[HirStmt], local: LocalId, param: ParamId) -> bool {
    if stmts_reference_captured_bindings(stmts)
        .params
        .contains(&param)
        || stmts_write_param(stmts, param)
    {
        return false;
    }
    validate_alias_flow(stmts, local, param, false).is_some()
}

fn validate_alias_flow(
    stmts: &[HirStmt],
    local: LocalId,
    param: ParamId,
    mut local_written: bool,
) -> Option<bool> {
    for stmt in stmts {
        local_written = validate_alias_stmt(stmt, local, param, local_written)?;
    }
    Some(local_written)
}

fn validate_alias_stmt(
    stmt: &HirStmt,
    local: LocalId,
    param: ParamId,
    local_written: bool,
) -> Option<bool> {
    match stmt {
        HirStmt::If(if_stmt) => {
            reject_param_read_after_local_write(&if_stmt.cond, param, local_written)?;
            let then_written =
                validate_alias_flow(&if_stmt.then_block.stmts, local, param, local_written)?;
            let else_written = if let Some(else_block) = &if_stmt.else_block {
                validate_alias_flow(&else_block.stmts, local, param, local_written)?
            } else {
                local_written
            };
            Some(then_written || else_written)
        }
        HirStmt::While(while_stmt) => {
            reject_param_read_after_local_write(&while_stmt.cond, param, local_written)?;
            let body_written =
                validate_repeating_body(&while_stmt.body, local, param, local_written)?;
            if body_written && !local_written {
                reject_param_read_after_local_write(&while_stmt.cond, param, true)?;
            }
            Some(body_written)
        }
        HirStmt::Repeat(repeat_stmt) => {
            let body_written =
                validate_repeating_body(&repeat_stmt.body, local, param, local_written)?;
            reject_param_read_after_local_write(&repeat_stmt.cond, param, body_written)?;
            Some(body_written)
        }
        HirStmt::NumericFor(numeric_for) => {
            if numeric_for.binding == local {
                return None;
            }
            for expr in [&numeric_for.start, &numeric_for.limit, &numeric_for.step] {
                reject_param_read_after_local_write(expr, param, local_written)?;
            }
            validate_repeating_body(&numeric_for.body, local, param, local_written)
        }
        HirStmt::GenericFor(generic_for) => {
            if generic_for.bindings.contains(&local) {
                return None;
            }
            for expr in &generic_for.iterator {
                reject_param_read_after_local_write(expr, param, local_written)?;
            }
            validate_repeating_body(&generic_for.body, local, param, local_written)
        }
        HirStmt::Block(block) => validate_alias_flow(&block.stmts, local, param, local_written),
        HirStmt::ToBeClosed(to_be_closed) => {
            // close-scopes 依赖 direct local/temp 身份配对 TBC；参数不能替代该 binding。
            if expr_mentions_local(&to_be_closed.value, local) {
                return None;
            }
            reject_param_read_after_local_write(&to_be_closed.value, param, local_written)?;
            Some(local_written)
        }
        HirStmt::Goto(_) | HirStmt::Label(_) => None,
        HirStmt::LocalDecl(local_decl) if local_decl.bindings.contains(&local) => None,
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Close(_)
        | HirStmt::Break
        | HirStmt::Continue => {
            if local_written && stmt_reads_param(stmt, param) {
                return None;
            }
            Some(local_written || stmt_writes_local(stmt, local))
        }
    }
}

fn validate_repeating_body(
    body: &HirBlock,
    local: LocalId,
    param: ParamId,
    local_written: bool,
) -> Option<bool> {
    let body_written = validate_alias_flow(&body.stmts, local, param, local_written)?;
    if body_written && !local_written {
        validate_alias_flow(&body.stmts, local, param, true)?;
    }
    Some(body_written)
}

fn reject_param_read_after_local_write(
    expr: &HirExpr,
    param: ParamId,
    local_written: bool,
) -> Option<()> {
    (!local_written || !expr_reads_param(expr, param)).then_some(())
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

fn stmts_write_param(stmts: &[HirStmt], param: ParamId) -> bool {
    let mut collector = ParamWriteCollector {
        param,
        written: false,
    };
    visit::visit_stmts(stmts, &mut collector);
    collector.written
}

struct ParamWriteCollector {
    param: ParamId,
    written: bool,
}

impl HirVisitor for ParamWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.written |= matches!(lvalue, HirLValue::Param(param) if *param == self.param);
    }
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

fn expr_reads_param(expr: &HirExpr, param: ParamId) -> bool {
    let mut collector = ParamReadCollector { param, read: false };
    visit::visit_expr(expr, &mut collector);
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
