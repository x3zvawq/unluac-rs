//! 短路值树的完整准备，消费原操作来源和逻辑结果 home。
//!
//! Luau 的值/条件叶使用不同准备槽；单次调用或查表与标量备用值消费原分支合流事实。
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
        self.luau_logical_value(&rebuilt, before, home, None)
    }

    pub(super) fn scalar_selection_layout(
        &self,
        logical: &crate::hir::common::HirLogicalExpr,
        before: usize,
        logical_and: bool,
    ) -> Option<(HomeSlotKey, HomeSlotKey)> {
        let lhs = match &logical.lhs {
            HirExpr::LocalRef(local) => scalar_local(self.run[self.definition(*local, before)?])?.1,
            lhs => lhs,
        };
        let source = match lhs {
            HirExpr::Call(call) => call.source_site?,
            HirExpr::TableAccess(access) => match access.sources {
                crate::hir::common::HirOperationSources::Single(source) => source,
                _ => return None,
            },
            _ => return None,
        };
        self.facts
            .short_circuit_scalar_homes(source, &logical.rhs, logical_and)
    }

    pub(super) fn scalar_selection(
        &mut self,
        logical: &crate::hir::common::HirLogicalExpr,
        before: usize,
        slot: usize,
        logical_and: bool,
        (input, result): (HomeSlotKey, HomeSlotKey),
    ) -> Option<HirExpr> {
        let context = self.native?;
        // Luau 可先保留逻辑结果，在高一槽调用或查表后按分支 COPY；O0 与 PUC/JIT 可直接复用结果槽。
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
        producer: Option<crate::hir::TempId>,
    ) -> Option<HirExpr> {
        if let HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) = expr
            && let Some(layout) = self.scalar_selection_layout(
                logical,
                before,
                matches!(expr, HirExpr::LogicalAnd(_)),
            )
        {
            return self.scalar_selection(
                logical,
                before,
                result.slot(),
                matches!(expr, HirExpr::LogicalAnd(_)),
                layout,
            );
        }
        let mut upvalues = producer.and_then(|producer| {
            let (home, expected) = self.facts.value_upvalue_frame(producer)?;
            (home == result).then_some(UpvalueFrameUse {
                result: producer,
                expected,
                reads: BTreeSet::new(),
            })
        });
        let previous = self.boolean_frame.replace(result);
        let value = self.luau_logical_tree(expr, before, result, LogicalUse::Value, &mut upvalues);
        self.boolean_frame = previous;
        // 每个原值叶恰好重发一次；仅有同名上值不能授权省略或复制读取。
        upvalues
            .is_none_or(|frame| frame.reads.len() == frame.expected)
            .then_some(value)
            .flatten()
    }

    fn luau_logical_tree(
        &mut self,
        expr: &HirExpr,
        before: usize,
        result: HomeSlotKey,
        usage: LogicalUse,
        upvalues: &mut Option<UpvalueFrameUse>,
    ) -> Option<HirExpr> {
        match expr {
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                let and = matches!(expr, HirExpr::LogicalAnd(_));
                if and
                    && matches!(usage, LogicalUse::Value)
                    && !logical.preserves_boolean_prewrite
                    && crate::hir::value_facts::value_facts(&logical.lhs).is_boolean()
                    && let HirExpr::LogicalOr(tail) = &logical.rhs
                    && !tail.preserves_boolean_prewrite
                    && tail.rhs == HirExpr::Boolean(false)
                    && let HirExpr::UpvalueRef(upvalue) = tail.lhs
                    && let Some(frame) = upvalues.as_ref()
                    && self.facts.boolean_value_prewrite(frame.result).is_none()
                    && self
                        .facts
                        .value_upvalue_leaf(frame.result, upvalue)
                        .is_some_and(|leaf| leaf.home == result && leaf.copy_and.is_none())
                {
                    // 结构值树可以把 false 尾臂结合进右子树，但 Luau 会将该形状编译为
                    // 高槽 GETUPVAL + ORK。原叶直接写结果槽时，恢复外层 or 的条件取值
                    // 形状；Boolean 谓词保证结合变化不会把原 nil 结果改成 false。
                    let condition = LogicalUse::Condition {
                        retain_value: true,
                        truthy: false,
                    };
                    let lhs =
                        self.luau_logical_tree(&logical.lhs, before, result, condition, upvalues)?;
                    let checkpoint = (self.first_event, self.next_event);
                    let rhs =
                        self.luau_logical_tree(&tail.lhs, before, result, condition, upvalues)?;
                    if checkpoint != (self.first_event, self.next_event) {
                        return None;
                    }
                    return Some(HirExpr::LogicalOr(Box::new(
                        crate::hir::common::HirLogicalExpr {
                            preserves_boolean_prewrite: false,
                            lhs: HirExpr::LogicalAnd(Box::new(
                                crate::hir::common::HirLogicalExpr {
                                    preserves_boolean_prewrite: false,
                                    lhs,
                                    rhs,
                                },
                            )),
                            rhs: HirExpr::Boolean(false),
                        },
                    )));
                }
                if let HirExpr::UpvalueRef(upvalue) = logical.lhs
                    && tables::literal_rk(&logical.rhs)
                    && self.native?.constants_fit_rk
                    && let Some(frame) = upvalues.as_mut()
                    && let Some(leaf) = self.facts.value_upvalue_leaf(frame.result, upvalue)
                    && leaf.copy_and == Some(and)
                    && leaf.home.slot() == result.slot() + 1
                {
                    // Luau ANDK/ORK 先在高槽读取 cell，再选择 COPY/常量写入结果。
                    // 原极性和两端 Def 已核对；不能把这个读改成结果槽上的直接 GETUPVAL。
                    return frame.reads.insert(upvalue).then(|| expr.clone());
                }
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
                let lhs =
                    self.luau_logical_tree(&logical.lhs, before, result, left_use, upvalues)?;
                let checkpoint = (self.first_event, self.next_event);
                let rhs =
                    self.luau_logical_tree(&logical.rhs, before, result, right_use, upvalues)?;
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
                    upvalues,
                )?;
                let mut inner = inner.as_ref().clone();
                inner.expr = value;
                let mut outer = outer.as_ref().clone();
                outer.expr = HirExpr::Unary(Box::new(inner));
                Some(HirExpr::Unary(Box::new(outer)))
            }
            HirExpr::TableAccess(access) => {
                // 仅作谓词的查表与 CALL 一样在结果上方准备；真正取值的末叶
                // 仍写共同结果槽。原 GETTABLE 的输入布局和事件继续由 lookup owner 核对。
                let predicate = matches!(
                    usage,
                    LogicalUse::Condition {
                        retain_value: false,
                        ..
                    }
                );
                self.luau_lookup(access, before, result.slot() + usize::from(predicate))
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
                // 原 CALL 的未捕获事实绑定 Def；未来同槽创建的 cell 不能回溯阻止
                // 本次准备。已发生的关闭边界及完整调用/前缀证明仍独立核对。
                if (if predicate {
                    home.slot() != result.slot() + 1
                } else {
                    home != result
                }) || native.closed.contains(&home)
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
                self.comparison_tree(expr, before, result.slot(), true)
            }
            HirExpr::Unary(unary)
                if unary.op == crate::hir::common::HirUnaryOpKind::Neg
                    || unary.op == crate::hir::common::HirUnaryOpKind::Not
                        && unary.source_site.is_some() =>
            {
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
            HirExpr::LocalRef(local)
                if self.definition(*local, before).is_some_and(|index| {
                    matches!(scalar_local(self.run[index]), Some((_, HirExpr::Unary(unary)))
                        if unary.source_site.is_some()
                            && matches!(unary.op,
                                crate::hir::common::HirUnaryOpKind::Neg
                                | crate::hir::common::HirUnaryOpKind::Not))
                }) =>
            {
                // 首叶的一元运算可能因 Boolean 取值身份保留为独立声明。
                // 按该叶的值/条件位置重放原 NOT/NEG；expr 核对 Def、输入槽与准备事件。
                let predicate = matches!(
                    usage,
                    LogicalUse::Condition {
                        retain_value: false,
                        ..
                    }
                );
                self.expr(
                    expr,
                    before,
                    result.slot() + usize::from(predicate),
                    None,
                    false,
                    false,
                    None,
                )
            }
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_) => Some(expr.clone()),
            HirExpr::UpvalueRef(upvalue)
                if !matches!(
                    usage,
                    LogicalUse::Condition {
                        retain_value: false,
                        ..
                    }
                ) =>
            {
                let frame = upvalues.as_mut()?;
                (self
                    .facts
                    .value_upvalue_leaf(frame.result, *upvalue)
                    .is_some_and(|leaf| leaf.home == result && leaf.copy_and.is_none())
                    && frame.reads.insert(*upvalue))
                .then(|| expr.clone())
            }
            HirExpr::LocalRef(_) | HirExpr::ParamRef(_)
                if self
                    .direct_home(expr)
                    .is_some_and(|home| home.slot() < self.base) =>
            {
                Some(expr.clone())
            }
            // 其余叶复用既有比较/读取证明；只有逻辑节点和 CALL 需要本层的值/条件
            // 路由。不能因共用值树 owner 而丢掉字段、全局和已准备 local 的支持。
            _ => self.comparison_tree(expr, before, result.slot(), true),
        }
    }
}
