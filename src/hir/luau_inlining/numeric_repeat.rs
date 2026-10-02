//! 数值计数循环内的条件查表与 repeat 退出合同。
//! 提取完整函数体和原显式更新；调用帧负责参数特化后的物理槽与观察次序。

use super::*;
use crate::hir::{HirBinaryOpKind, HirLValue, LocalId};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct NumericRepeatTemplate {
    pub initial: i64,
    pub start: i64,
    pub limit: i64,
    pub step: i64,
    pub increment: i64,
    pub rejected_increment: i64,
    pub tail_increment: i64,
}

impl NumericRepeatTemplate {
    fn supported_profiles(self) -> bool {
        use crate::hir::luau_loop_cost::{Cost, trips};
        let Some(count) = trips(self.start, self.limit, self.step) else {
            return false;
        };
        let update = Cost::fixed(1);
        let lookup_exit = Cost::fixed(3); // GETTABLE、条件分支和 break。
        let skipped = update.add(update.multiply(3));
        let observed = update.add(lookup_exit.add(Cost::fixed(1)).multiply(3));
        // 最终 AST 可把 continue 的 else 提升到其后；采用两种表示中较低的
        // 基线成本，不能靠额外 else JMP 抬高内联收益。参数1只贡献裸条件的零成本。
        let baseline = update
            .add(
                Cost::fixed(1)
                    .add(lookup_exit)
                    .add(Cost::fixed(3))
                    .add(update)
                    .multiply(3),
            )
            .add(Cost::fixed(1))
            .multiply(count);
        let function_cost = |body: Cost| body.add(Cost::fixed(1)).multiply(count);
        !skipped.blocks_unroll(self.start, self.limit, self.step)
            && observed.blocks_unroll(self.start, self.limit, self.step)
            && function_cost(skipped).permits_inline(baseline)
            && function_cost(observed).permits_inline(baseline)
            && !baseline.permits_inline(baseline)
    }
}

fn update(stmt: &HirStmt, state: LocalId) -> Option<i64> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([HirLValue::Local(target)], [HirExpr::Binary(binary)], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    // loop carrier 的写入可同时带 phi 标记；这里核对的是仍留在原位的
    // 显式 ADD。纯 COPY 没有此原操作来源，不能冒充这次计数更新。
    if *target != state
        || assign.initializer_merge_transaction.is_some()
        || assign.generic_for_initializer_producer.is_some()
        || assign.root_release.is_some()
        || assign.method_rewrite_transaction.is_some()
        || assign.parallel_nil_frame.is_some()
        || binary.op != HirBinaryOpKind::Add
        || binary.source_site.is_none()
        || binary.lhs != HirExpr::LocalRef(state)
    {
        return None;
    }
    small_integer(&binary.rhs)
}

pub(crate) fn numeric_repeat_template(proto: &HirProto) -> Option<NumericRepeatTemplate> {
    if proto.params.as_slice() != [ParamId(0), ParamId(1), ParamId(2)]
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [
        HirStmt::LocalDecl(decl),
        HirStmt::NumericFor(loop_),
        HirStmt::Return(ret),
    ] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    let ([state], [initial], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    if decl.initializer_merge_transaction.is_some()
        || decl.generic_for_initializer_producer.is_some()
        || loop_.binding == *state
        || ret.values.tail.is_some()
        || ret.pending_cleanup_source.is_some()
        || ret.values.fixed.as_slice() != [HirExpr::LocalRef(*state)]
    {
        return None;
    }
    let [first, HirStmt::Repeat(repeat)] = loop_.body.stmts.as_slice() else {
        return None;
    };
    let [HirStmt::If(guard), tail] = repeat.body.stmts.as_slice() else {
        return None;
    };
    if repeat.cond != HirExpr::ParamRef(ParamId(1))
        || guard.cond != HirExpr::ParamRef(ParamId(0))
        || guard
            .else_block
            .as_ref()
            .is_some_and(|block| !block.stmts.is_empty())
    {
        return None;
    }
    // continue 之后的 else 可由结构恢复提升为同块后缀；两个形式保留
    // 同一条显式更新，回编译时不能依赖原输入是否写出了 else。
    let (lookup, continued, rejected) = match guard.then_block.stmts.as_slice() {
        [HirStmt::If(lookup), HirStmt::If(continued)] => {
            let [rejected] = continued.else_block.as_ref()?.stmts.as_slice() else {
                return None;
            };
            (lookup, continued, rejected)
        }
        [HirStmt::If(lookup), HirStmt::If(continued), rejected]
            if continued
                .else_block
                .as_ref()
                .is_none_or(|block| block.stmts.is_empty()) =>
        {
            (lookup, continued, rejected)
        }
        _ => return None,
    };
    let HirExpr::TableAccess(access) = &lookup.cond else {
        return None;
    };
    if access.base != HirExpr::ParamRef(ParamId(2))
        || access.key != HirExpr::LocalRef(*state)
        || !matches!(lookup.then_block.stmts.as_slice(), [HirStmt::Break])
        || lookup
            .else_block
            .as_ref()
            .is_some_and(|block| !block.stmts.is_empty())
        || continued.cond != HirExpr::ParamRef(ParamId(0))
        || !matches!(continued.then_block.stmts.as_slice(), [HirStmt::Continue])
    {
        return None;
    }
    let template = NumericRepeatTemplate {
        initial: small_integer(initial)?,
        start: small_integer(&loop_.start)?,
        limit: small_integer(&loop_.limit)?,
        step: small_integer(&loop_.step)?,
        increment: update(first, *state)?,
        rejected_increment: update(rejected, *state)?,
        tail_increment: update(tail, *state)?,
    };
    // 候选拒绝[TargetConstraint]：发布前已证明两类调用均内联，只有无索引
    // 配置展开数值循环；最终 AST 仍须重新核对实际成本。
    template.supported_profiles().then_some(template)
}
