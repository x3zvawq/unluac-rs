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
    if promotion_facts.compacts_home_slots() {
        // 候选拒绝[SemanticBarrier:Lifetime]：regress lua54_01_close#7 中跨槽把 alias 写回 param 会提前释放原参数 GC root；compaction 下 trusted 同槽不能作为正向证明。
        return false;
    }
    if promotion_facts.entry_nil_writes_were_pruned(alias.local) {
        // 候选拒绝[ProofIncomplete]：entry-nil 已改变 alias 的写入历史，当前 flow state 未携带被裁剪路径；应把 nil-prune provenance 纳入 alias 初态后再判定。
        return false;
    }
    if !shares_exact_home {
        // 候选拒绝[SemanticBarrier:Lifetime]：`local l=p; weak[p]=true; l={}; GC` 中跨槽合并会覆盖 p 并让原对象提前回收，原程序的参数槽仍应持有它。
        return false;
    }
    if rest
        .iter()
        .any(|stmt| stmt_captures_local(stmt, alias.local))
    {
        // 候选拒绝[ProofIncomplete]：alias local 的任意 capture 被 blanket 拒绝；当前没有证明该 capture cell 与同 home 参数 cell 在全部写入路径上可合并。
        return false;
    }
    if !rest_preserves_param_alias_identity(rest, alias.local, alias.param) {
        // 候选拒绝[SemanticBarrier:ValueFlow]：flow proof 发现 alias 写入后仍可读旧参数时，`local l=p; l=1; return p` 合并后会错误返回 1。
        // 候选拒绝[ProofIncomplete]：同一出口也包含 goto/label 与 path-insensitive join 等尚未分析形状，不能把所有失败都视为已证不等价。
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
    {
        // 候选拒绝[SemanticBarrier:Capture]：`local l=p; local f=function() return p end; l=1; return f()` 若合并，f 会观察 1 而非原参数值。
        return false;
    }
    if stmts_write_param(stmts, param) {
        // 候选拒绝[SemanticBarrier:ValueFlow]：`local l=p; p=2; return l` 若删除 alias 并统一为 p，会从原值变成 2。
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
            // 候选拒绝[ProofIncomplete]：这里用 may-written OR 合流，导致一臂写后退出、另一臂未写后继续的安全路径也被后续 param-read guard 拒绝；应传播逐出口状态集合。
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
                // 候选拒绝[ConvergenceGuard]：alias LocalId 同时作为 numeric-for 新 binding 违反唯一声明身份；rewriter 也不能把 LocalId binder 改成 ParamId。
                return None;
            }
            for expr in [&numeric_for.start, &numeric_for.limit, &numeric_for.step] {
                reject_param_read_after_local_write(expr, param, local_written)?;
            }
            validate_repeating_body(&numeric_for.body, local, param, local_written)
        }
        HirStmt::GenericFor(generic_for) => {
            if generic_for.bindings.contains(&local) {
                // 候选拒绝[ConvergenceGuard]：alias LocalId 同时出现在 generic-for binding 列表违反唯一声明身份，不能在删除入口声明后继续复用。
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
                // 候选拒绝[SemanticBarrier:Resource]：`local l=p; <TBC l>; l=q` 若改为参数，会更换 close owner，并可能关闭错误值或改变关闭时点。
                return None;
            }
            reject_param_read_after_local_write(&to_be_closed.value, param, local_written)?;
            Some(local_written)
        }
        HirStmt::Goto(_) | HirStmt::Label(_) => {
            // 候选拒绝[ProofIncomplete]：结构化 flow state 没有 label/goto 的 predecessor 合流，无法证明跳转路径上的 alias/param 同步状态。
            None
        }
        HirStmt::LocalDecl(local_decl) if local_decl.bindings.contains(&local) => {
            // 候选拒绝[ConvergenceGuard]：候选 LocalId 在后缀再次声明违反唯一 binding 不变量；删除前缀会改变该异常 HIR 的作用域。
            None
        }
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
                // 候选拒绝[SemanticBarrier:ValueFlow]：`l=1; return p` 的 p 仍应是入口值，合并后却会读取刚写入的 1。
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
        // 候选拒绝[SemanticBarrier:ValueFlow]：循环首轮写 alias 后，下一轮若读取原 param，合并会把旧入口值替换为上一轮 alias 值。
        validate_alias_flow(&body.stmts, local, param, true)?;
    }
    Some(body_written)
}

fn reject_param_read_after_local_write(
    expr: &HirExpr,
    param: ParamId,
    local_written: bool,
) -> Option<()> {
    // 候选拒绝[SemanticBarrier:ValueFlow]：任一路径写 alias 后再读 param（如 `l=1; use(p)`）可观察两个 binding，不能收敛为同一参数。
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
