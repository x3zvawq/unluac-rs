//! 为普通字段调用签发最终冒号语法许可，不生成原 SELF 身份。
//!
//! 返回值 owner 证明当前字段必为新表中的闭包，Promotion 核对原 lookup/CALL 槽。
//! `local r=factory(); r.m(r)` 可写成 `local r=factory(); r:m()`；receiver 声明及
//! 原根保留，GETFIELD 与 SELF 的差别只发生在无观察的字段查找内部。此步位于所有
//! HIR 改写之后，AST build 消费许可，不由 AST 重建表逃逸或读取物理寄存器。

use super::object_flow::ReturnValueFacts;
use super::walk::{HirRewritePass, rewrite_proto};
use crate::decompile::DecompileDialect;
use crate::hir::common::{HirCallExpr, HirExpr, HirModule, HirOperationSources};
use crate::hir::promotion::ProtoPromotionFacts;
use crate::transformer::ValuePack;

pub(super) fn finalize(
    module: &mut HirModule,
    promotion: &[ProtoPromotionFacts],
    values: &ReturnValueFacts,
    dialect: DecompileDialect,
) {
    if dialect != DecompileDialect::Lua54 {
        // 候选拒绝[ProofIncomplete]：其它方言的字段 key 与 receiver 准备布局尚未签证。
        return;
    }
    struct Pass<'a> {
        facts: &'a ProtoPromotionFacts,
        values: &'a ReturnValueFacts,
    }
    impl HirRewritePass for Pass<'_> {
        fn rewrite_call(&mut self, call: &mut HirCallExpr) -> bool {
            call.plain_method_syntax = permits(call, self.facts, self.values);
            false
        }
    }
    for proto in &mut module.protos {
        if let Some(facts) = promotion.get(proto.id.index()) {
            rewrite_proto(proto, &mut Pass { facts, values });
        }
    }
}

fn permits(call: &HirCallExpr, facts: &ProtoPromotionFacts, values: &ReturnValueFacts) -> bool {
    if call.is_method() || call.fastcall.is_some() {
        return false;
    }
    let HirExpr::TableAccess(access) = &call.callee else {
        return false;
    };
    if !matches!(access.key, HirExpr::String(_)) || call.args.first() != Some(&access.base) {
        return false;
    }
    if call.args.fixed.len() != 1 || call.args.tail.is_some() {
        // 候选拒绝[ProofIncomplete]：这里只签发无额外参数的完整普通字段调用。
        return false;
    }
    let receiver = match access.base {
        HirExpr::LocalRef(local) => facts.trusted_local_home_slot(local),
        HirExpr::ParamRef(param) => facts.trusted_param_home_slot(param),
        _ => return false,
    };
    let Some(receiver) = receiver else {
        return false;
    };
    let (Some(layout), Some(read)) = (
        facts.native_call_layout(call),
        facts.native_table_read_layout(access),
    ) else {
        return false;
    };
    let HirOperationSources::Single(source) = access.sources else {
        return false;
    };
    let ValuePack::Fixed(args) = layout.args else {
        return false;
    };
    if read.base != receiver
        || read.key.is_some()
        || facts.operation_result_home(source) != Some(layout.home)
        || args.len != 1
        || args.start.index() != layout.home.slot() + 1
        || !layout.arguments_unaliased
    {
        // 候选拒绝[ProofIncomplete]：原直接 key、callee/receiver 槽与非捕获参数区必须完整匹配。
        return false;
    }
    // 只有当前新表的确定闭包字段才为 TableAccess callee 提供目标。未知或观察后失效的字段
    // 不领此许可；普通 receiver 的 __index 可观察旧参数根（methods_05）。
    values.call_target(call).is_some()
}
