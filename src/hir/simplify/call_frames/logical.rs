//! Luau 短路值树的完整调用准备，消费已有 CALL 来源和原逻辑结果 home。
//!
//! 值叶写结果槽，只作真假判断的叶在其高一槽调用。例如 `(a() and b()) or c()`
//! 的 a 不产生最终值，CALL 位于 result+1；b/c 则写 result。temp-inline 必须保留
//! 逻辑结果及后继异槽 COPY，不能从首个 CALL 推测整棵树的结果身份。本模块只投影
//! 已有源码树的值/条件语境；事件、callee/参数 Def 和生命周期仍由共享 builder 证明。
//! 只用于已经预留结果槽的 local initializer；普通 Assign 的额外结果准备不属于此合同。

use super::*;

#[derive(Clone, Copy)]
enum LogicalUse {
    Value,
    Condition { retain_value: bool, truthy: bool },
}

impl FrameBuilder<'_> {
    pub(super) fn luau_logical_value(
        &mut self,
        expr: &HirExpr,
        before: usize,
        result: HomeSlotKey,
    ) -> Option<HirExpr> {
        self.luau_logical_tree(expr, before, result, LogicalUse::Value)
    }

    fn luau_logical_tree(
        &mut self,
        expr: &HirExpr,
        before: usize,
        result: HomeSlotKey,
        usage: LogicalUse,
    ) -> Option<HirExpr> {
        match expr {
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                let and = matches!(expr, HirExpr::LogicalAnd(_));
                let (left_use, right_use) = match usage {
                    LogicalUse::Value => (
                        LogicalUse::Condition {
                            retain_value: true,
                            truthy: !and,
                        },
                        LogicalUse::Value,
                    ),
                    LogicalUse::Condition {
                        retain_value,
                        truthy,
                    } => (
                        LogicalUse::Condition {
                            retain_value: retain_value && truthy != and,
                            truthy: if truthy == and { !truthy } else { truthy },
                        },
                        usage,
                    ),
                };
                let lhs = self.luau_logical_tree(&logical.lhs, before, result, left_use)?;
                let checkpoint = (self.first_event, self.next_event);
                let rhs = self.luau_logical_tree(&logical.rhs, before, result, right_use)?;
                // 右臂的准备必须原本就在条件路径中；不从前方吸收无条件定义。
                if checkpoint != (self.first_event, self.next_event) {
                    return None;
                }
                let logical = Box::new(crate::hir::common::HirLogicalExpr { lhs, rhs });
                Some(if and {
                    HirExpr::LogicalAnd(logical)
                } else {
                    HirExpr::LogicalOr(logical)
                })
            }
            HirExpr::Call(call) => {
                let predicate = matches!(
                    usage,
                    LogicalUse::Condition {
                        retain_value: false,
                        ..
                    }
                );
                let home = if call.fastcall.is_some() {
                    self.facts.native_fastcall_frame(call)?.home
                } else {
                    self.facts.native_call_frame(call)?.home
                };
                let native = self.native?;
                if (if predicate {
                    home.slot() != result.slot() + 1
                } else {
                    home != result
                }) || native.barred.contains(&home)
                    || native.closed.contains(&home)
                    || !self
                        .facts
                        .operation_result_reference_unaliased(call.source_site?)
                {
                    return None;
                }
                self.expr(expr, before, home.slot(), None, false, false, None)
            }
            HirExpr::Binary(_) if matches!(usage, LogicalUse::Value) => {
                self.expr(expr, before, result.slot(), None, false, false, None)
            }
            _ => None,
        }
    }
}
