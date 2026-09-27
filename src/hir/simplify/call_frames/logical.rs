//! 短路值树的完整调用准备，消费已有 CALL 来源和原逻辑结果 home。
//!
//! Luau 的值/条件叶使用不同准备槽；单次 CALL 与标量备用值则消费原分支合流事实。
//! 事件、callee/参数 Def 和生命周期由共享 builder 证明，实际源码前缀由 native owner 核对。

use super::*;

#[derive(Clone, Copy)]
enum LogicalUse {
    Value,
    Condition { retain_value: bool, truthy: bool },
}

impl FrameBuilder<'_> {
    /// 原入口 COPY 是这棵值树的初值；按 Def 与 home 消费，不能沿展示 local 猜来源。
    pub(super) fn luau_copy_value(
        &mut self,
        expr: &HirExpr,
        before: usize,
        initial: crate::hir::common::TempId,
        home: HomeSlotKey,
    ) -> Option<HirExpr> {
        let owner = self.facts.promoted_local_for_temp(initial)?;
        let mut rebuilt = expr.clone();
        let mut head = &mut rebuilt;
        while let HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) = head {
            head = &mut logical.lhs;
        }
        if *head != HirExpr::LocalRef(owner) {
            return None;
        }
        *head = self.expr(head, before, home.slot(), None, false, true, Some(initial))?;
        self.luau_logical_value(&rebuilt, before, home)
    }

    pub(super) fn scalar_call_selection_layout(
        &self,
        logical: &crate::hir::common::HirLogicalExpr,
        before: usize,
        logical_and: bool,
    ) -> Option<(HomeSlotKey, HomeSlotKey)> {
        let lhs = match &logical.lhs {
            HirExpr::LocalRef(local) => scalar_local(self.run[self.definition(*local, before)?])?.1,
            lhs => lhs,
        };
        let HirExpr::Call(call) = lhs else {
            return None;
        };
        self.facts
            .short_circuit_call_homes(call, &logical.rhs, logical_and)
    }

    pub(super) fn scalar_call_selection(
        &mut self,
        logical: &crate::hir::common::HirLogicalExpr,
        before: usize,
        slot: usize,
        logical_and: bool,
        (input, result): (HomeSlotKey, HomeSlotKey),
    ) -> Option<HirExpr> {
        let context = self.native?;
        // Luau 可先保留逻辑结果，在高一槽调用后按分支 COPY；O0 与 PUC/JIT 可直接复用结果槽。
        if result != HomeSlotKey::new(slot, 0)
            || !(input == result
                || self.dialect == DecompileDialect::Luau && input.slot() == slot + 1)
            || context.barred.contains(&input)
            || context.closed.contains(&input)
            || context.closed.contains(&result)
        {
            return None;
        }
        let lhs = self.expr(&logical.lhs, before, input.slot(), None, false, true, None)?;
        let rebuilt = Box::new(crate::hir::common::HirLogicalExpr {
            preserves_boolean_prewrite: logical.preserves_boolean_prewrite,
            lhs,
            rhs: logical.rhs.clone(),
        });
        Some(if logical_and {
            HirExpr::LogicalAnd(rebuilt)
        } else {
            HirExpr::LogicalOr(rebuilt)
        })
    }

    /// 值叶写结果槽，只作真假判断的叶在其高一槽调用，例如 `(a() and b()) or c()`
    /// 的 a。声明 initializer 预留结果槽，现存低槽写回则保留独立 RHS 暂存槽。
    pub(super) fn luau_logical_value(
        &mut self,
        expr: &HirExpr,
        before: usize,
        result: HomeSlotKey,
    ) -> Option<HirExpr> {
        if let HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) = expr
            && let Some(layout) = self.scalar_call_selection_layout(
                logical,
                before,
                matches!(expr, HirExpr::LogicalAnd(_)),
            )
        {
            return self.scalar_call_selection(
                logical,
                before,
                result.slot(),
                matches!(expr, HirExpr::LogicalAnd(_)),
                layout,
            );
        }
        let previous = self.boolean_frame.replace(result.slot());
        let value = self.luau_logical_tree(expr, before, result, LogicalUse::Value);
        self.boolean_frame = previous;
        value
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
                // Boolean 化是结构层对 false 分支的表示；真假选择的右值已知为
                // truthy 时恢复 `predicate and value or false`，避免输出 synthetic NOT
                // 令复编译产生原 chunk 没有的运算。原生 NOT 有来源，不能走此规约。
                if and
                    && matches!(
                        rhs,
                        HirExpr::Boolean(true)
                            | HirExpr::String(_)
                            | HirExpr::Integer(_)
                            | HirExpr::Number(_)
                    )
                    && let HirExpr::Unary(outer) = &lhs
                    && outer.source_site.is_none()
                    && outer.op == crate::hir::common::HirUnaryOpKind::Not
                    && let HirExpr::Unary(inner) = &outer.expr
                    && inner.source_site.is_none()
                    && inner.op == crate::hir::common::HirUnaryOpKind::Not
                {
                    return Some(HirExpr::LogicalOr(Box::new(
                        crate::hir::common::HirLogicalExpr {
                            preserves_boolean_prewrite: logical.preserves_boolean_prewrite,
                            lhs: HirExpr::LogicalAnd(Box::new(
                                crate::hir::common::HirLogicalExpr {
                                    preserves_boolean_prewrite: false,
                                    lhs: inner.expr.clone(),
                                    rhs,
                                },
                            )),
                            rhs: HirExpr::Boolean(false),
                        },
                    )));
                }
                let logical = Box::new(crate::hir::common::HirLogicalExpr {
                    preserves_boolean_prewrite: logical.preserves_boolean_prewrite,
                    lhs,
                    rhs,
                });
                Some(if and {
                    HirExpr::LogicalAnd(logical)
                } else {
                    HirExpr::LogicalOr(logical)
                })
            }
            HirExpr::Unary(outer)
                if outer.source_site.is_none()
                    && outer.op == crate::hir::common::HirUnaryOpKind::Not
                    && matches!(&outer.expr, HirExpr::Unary(inner)
                        if inner.source_site.is_none()
                            && inner.op == crate::hir::common::HirUnaryOpKind::Not) =>
            {
                let HirExpr::Unary(inner) = &outer.expr else {
                    unreachable!()
                };
                // 结构恢复的 Boolean 化包装把 CALL 结果转成真假，值槽仍是外层
                // 逻辑结果；CALL 只作谓词，须在高一槽按原准备事件重放。
                let value = self.luau_logical_tree(
                    &inner.expr,
                    before,
                    result,
                    LogicalUse::Condition {
                        retain_value: false,
                        truthy: true,
                    },
                )?;
                let mut inner = inner.as_ref().clone();
                inner.expr = value;
                let mut outer = outer.as_ref().clone();
                outer.expr = HirExpr::Unary(Box::new(inner));
                Some(HirExpr::Unary(Box::new(outer)))
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
            HirExpr::Binary(binary)
                if matches!(usage, LogicalUse::Condition { .. })
                    && matches!(
                        binary.op,
                        crate::hir::common::HirBinaryOpKind::Eq
                            | crate::hir::common::HirBinaryOpKind::Lt
                            | crate::hir::common::HirBinaryOpKind::Le
                            | crate::hir::common::HirBinaryOpKind::Gt
                            | crate::hir::common::HirBinaryOpKind::Ge
                    ) =>
            {
                // 比较仍位于值树原来的条件位置；外层已消费该结果槽的 Boolean
                // 预写，既保留低槽读取，也不把整个值树改成无写回的纯谓词。
                self.expr(expr, before, result.slot(), None, false, true, None)
            }
            HirExpr::Binary(_) if matches!(usage, LogicalUse::Value) => {
                self.expr(expr, before, result.slot(), None, false, false, None)
            }
            HirExpr::Unary(unary) if unary.op == crate::hir::common::HirUnaryOpKind::Neg => {
                let predicate = matches!(
                    usage,
                    LogicalUse::Condition {
                        retain_value: false,
                        ..
                    }
                );
                let slot = result.slot() + usize::from(predicate);
                self.expr(expr, before, slot, None, false, false, None)
            }
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_) => Some(expr.clone()),
            HirExpr::LocalRef(_) | HirExpr::ParamRef(_)
                if self
                    .direct_home(expr)
                    .is_some_and(|home| home.slot() < self.base) =>
            {
                Some(expr.clone())
            }
            _ => None,
        }
    }
}
