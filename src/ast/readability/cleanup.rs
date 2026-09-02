//! 这个文件负责清理已经没有源码意义的机械 AST 壳。
//!
//! 它依赖前面的结构恢复和 readability pass 已经把真正需要保留的局部作用域、
//! 控制流和显式 return 暴露出来；这里专门删除“只剩形式意义”的 do-end、空 local、
//! 以及 chunk/function 结尾的无值 return。尾部 do-end 的作用域证明显式区分普通
//! block 出口和 repeat 的 `until` 条件：前者与父 block 同时退出，后者仍会在父域中
//! 求值。它不会越权合并业务语句，也不会把仍有词法意义的块错误拍平。
//!
//! 例子：
//! - `do print(x) end` 会在内部没有局部作用域意义时折成 `print(x)`
//! - `local t0` 这种只剩机械 temp 壳、且没有值也没有使用的声明会被删除
//! - 未使用的 recovered `local t0 = side_effect()` 会保留为 `side_effect()` 调用
//! - 函数尾部的 `return` 会在没有返回值时被去掉

use std::collections::{BTreeMap, BTreeSet};

use super::super::common::{
    AstBinaryOpKind, AstBindingRef, AstBlock, AstCallKind, AstCallStmt, AstExpr, AstLValue,
    AstLocalAttr, AstLocalBinding, AstLocalDecl, AstLocalOrigin, AstModule, AstNameRef,
    AstRewriteAuthority, AstStmt, AstTargetDialect, AstUnaryOpKind,
};
use super::ReadabilityContext;
use super::binding_flow::{BindingUseIndex, binding_mentions_in_expr, binding_mentions_in_stmt};
use super::expr_analysis::is_discard_safe_expr_for_target;
use super::global_decl_pretty::{VisibleGlobals, extending_global_scope_preserves_expr};
use super::repeat_lifetime::{
    binding_must_live_through_condition, hir_binding_may_end_before_condition,
};
use super::walk::{self, AstRewritePass, BlockKind, ScopedAstRewritePass};
use crate::ast::traverse::traverse_expr_children;
use crate::hir::HirRepeatConditionLifetimeFacts;

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    let mut changed = walk::rewrite_module(
        module,
        &mut CleanupPass {
            target: context.target,
        },
    );
    changed |= walk::rewrite_module_scoped(
        module,
        &VisibleGlobals::default(),
        &mut RepeatTailCleanupPass,
    );
    changed
}

struct CleanupPass {
    target: AstTargetDialect,
}

impl AstRewritePass for CleanupPass {
    fn rewrite_block(&mut self, block: &mut AstBlock, kind: BlockKind) -> bool {
        cleanup_block(
            block,
            matches!(kind, BlockKind::ModuleBody | BlockKind::FunctionBody),
            None,
            self.target,
        )
    }

    fn rewrite_repeat_body(&mut self, block: &mut AstBlock, condition: &AstExpr) -> bool {
        cleanup_block(block, false, Some(condition), self.target)
    }
}

struct RepeatTailCleanupPass;

impl ScopedAstRewritePass for RepeatTailCleanupPass {
    type Scope = VisibleGlobals;

    fn enter_block(
        &mut self,
        _block: &mut AstBlock,
        _kind: BlockKind,
        incoming: &Self::Scope,
    ) -> (bool, Self::Scope) {
        (false, incoming.clone())
    }

    fn enter_repeat_body(
        &mut self,
        block: &mut AstBlock,
        condition: &AstExpr,
        lifetime: &HirRepeatConditionLifetimeFacts,
        incoming: &Self::Scope,
    ) -> (bool, Self::Scope) {
        (
            flatten_repeat_tail_do_blocks(block, condition, lifetime, incoming),
            incoming.clone(),
        )
    }

    fn scope_for_stmt_children(&mut self, stmt: &AstStmt, scope: &Self::Scope) -> Self::Scope {
        // `global function f()` 的名字在函数体内即可见；普通 global declaration 的
        // initializer 则必须继续使用声明前环境。与 global-decl-pretty 共用同一规则。
        if matches!(stmt, AstStmt::FunctionDecl(_)) {
            scope.after_stmt(stmt)
        } else {
            scope.clone()
        }
    }

    fn scope_after_stmt(&mut self, stmt: &AstStmt, scope: &Self::Scope) -> Self::Scope {
        scope.after_stmt(stmt)
    }
}

fn cleanup_block(
    block: &mut AstBlock,
    allow_trailing_empty_return_elision: bool,
    trailing_condition: Option<&AstExpr>,
    target: AstTargetDialect,
) -> bool {
    let mut changed = false;

    let old_stmts = std::mem::take(&mut block.stmts);
    let mut flattened_stmts = Vec::with_capacity(old_stmts.len());
    let stmt_count = old_stmts.len();
    for (index, stmt) in old_stmts.into_iter().enumerate() {
        match stmt {
            AstStmt::DoBlock(nested)
                if nested.stmts.len() == 1
                    && can_elide_single_stmt_do_block(&nested.stmts[0])
                    // repeat 条件在正文末句之后求值；尾 do 必须交给下方携带 condition
                    // 的证明，否则通用单句清理会抢先删除唯一能在条件前释放 root 的作用域。
                    && !(trailing_condition.is_some() && index + 1 == stmt_count) =>
            {
                // 这里专门清理“只剩一条非局部作用域语句”的机械 do-end。
                // 它通常是前层为了暂存中间 local 范围而留下来的壳；一旦内部局部已经被
                // 其他 pass 收回，这层壳继续保留只会让源码多出无意义缩进。
                flattened_stmts.extend(nested.stmts);
                changed = true;
            }
            other => flattened_stmts.push(other),
        }
    }
    block.stmts = flattened_stmts;

    // A recovered call result can be an implementation-only value that is immediately
    // overwritten before any read. Keep the call at its original evaluation point, but
    // declare the binding with the value that actually survives. This removes a misleading
    // `local x = f(); x = value` pair without moving a call across another statement.
    changed |= split_overwritten_call_result_locals(block, target);

    // A capture owner may force the producer and its final temp assignment into a lexical
    // block while the one-value return remains immediately outside it.  Return the value from
    // that block directly so the synthetic carrier does not survive into final source.
    changed |= inline_terminal_scoped_temp_return(block);

    // 尾部 do-end 展开：当 do-end 是块的最后一条语句时，其内部 local 的作用域
    // 在父块结束处同样终止，do-end 仅是多余的缩进壳。
    // 典型来源：guard-flip 把 `if cond then BODY else return end` 拉平成
    // `if not cond then return end; do BODY end`，其中 BODY 含 local 声明。
    // repeat body 与 until 条件共享外层作用域；只有这种尾条件存在时，global、`<close>`
    // local 和局部 closure 才需要额外边界。普通 block 的尾 do 与父 block 同时退出，
    // 因而可安全去掉缩进壳（regress344 覆盖函数尾 `<close>` + return）。
    while trailing_condition.is_none()
        && let Some(AstStmt::DoBlock(nested)) = block.stmts.last()
        && trailing_do_block_is_scope_neutral(nested, None)
    {
        let Some(AstStmt::DoBlock(nested)) = block.stmts.pop() else {
            unreachable!();
        };
        block.stmts.extend(nested.stmts);
        changed = true;
    }

    let binding_flow = BlockBindingFlow::new(block, trailing_condition);
    changed |= trim_unused_initialized_local_suffix(block, &binding_flow);
    let original_stmts = std::mem::take(&mut block.stmts);
    let mut retained_stmts = Vec::with_capacity(original_stmts.len());
    for stmt in original_stmts {
        match stmt {
            // 候选拒绝[SemanticBarrier:ValueArity]：多目标声明只允许上面的 helper 删除连续
            // 尾槽。删除未使用前缀/中间槽会移动后续 binding 对应的返回值，例如
            // `local dead, keep = pair()` 会让 keep 从第二返回值错取第一返回值。
            // 候选拒绝[SemanticBarrier:Lifetime]：有 initializer 的 `<close>` 即使无普通 use
            // 也必须在域末执行 `__close`（regress246）。`<const>` 没有退出动作，在其 binding
            // 无引用且 initializer 可安全丢弃/保留为 call 时允许清理。
            // 候选拒绝[SemanticBarrier:DebugScope]：DebugHinted 声明的可见期可被 line hook /
            // debug.getlocal 观察；删除会抹掉源码 binding 身份（regress_341、regress_420）。
            // 候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot 可能由弱表/`__gc` 观察，
            // 不能按普通未使用 local 删除。
            // 候选拒绝[SemanticBarrier:Scope]：声明外仍有读取、capture 或写入时，删除 local
            // 会改变读取值、捕获 cell，或让后续 name target 解析成外层/global。
            AstStmt::LocalDecl(mut local_decl)
                if local_decl.bindings.len() == 1
                    && local_decl.values.len() == 1
                    && local_decl.bindings[0].attr != AstLocalAttr::Close
                    && local_decl.bindings[0].origin == AstLocalOrigin::Recovered
                    && local_decl.bindings[0]
                        .rewrite_authority
                        .may_remove_binding()
                    && !binding_flow.keeps_decl_alive(local_decl.bindings[0].id) =>
            {
                if is_discard_safe_expr_for_target(&local_decl.values[0], target) {
                    // 候选接受：表达式无求值副作用，且 binding-flow 已证明域内外均无读取、
                    // capture 或写入；删除声明不会移除可观察求值或词法槽。
                    changed = true;
                } else {
                    let Some(value) = local_decl.values.pop() else {
                        retained_stmts.push(AstStmt::LocalDecl(local_decl));
                        continue;
                    };
                    match into_call_kind(value) {
                        Ok(call) => {
                            // 候选接受：call 仍在原语句位置执行一次，仅丢弃未使用的结果。
                            retained_stmts.push(AstStmt::CallStmt(Box::new(AstCallStmt { call })));
                            changed = true;
                        }
                        Err(value) => {
                            match unused_value_rejection(&value, target) {
                                UnusedValueRejection::EvalCount => {
                                    // 候选拒绝[SemanticBarrier:EvalCount]：删除 lookup 或嵌套 call
                                    // 会少一次可观察求值（regress178）。
                                }
                                UnusedValueRejection::ControlFlow => {
                                    // 候选拒绝[SemanticBarrier:ControlFlow]：未证明类型的动态运算
                                    // 可能调用元方法或抛错；regress245/regress390 覆盖两类反例。
                                }
                                UnusedValueRejection::Allocation => {
                                    // 候选拒绝[SemanticBarrier:Allocation]：literal concat、table 与
                                    // closure 会分配；删除会改变 GC 推进或内存错误事件。
                                }
                                UnusedValueRejection::TargetConstraint => {
                                    // 候选拒绝[TargetConstraint]：Lua 5.1/5.2 没有携带
                                    // integral-number 位宽与溢出语义；Auto 还没有确定 dynamic
                                    // primitive equality 是否可能进入方言专属元方法。
                                }
                                UnusedValueRejection::PolicyBoundary => {
                                    // 候选拒绝[PolicyBoundary]：AstExpr::Error 是 best-effort 输出
                                    // 必须保留的失败证据，cleanup 不把它当作可丢弃的纯值。
                                }
                            }
                            local_decl.values.push(value);
                            retained_stmts.push(AstStmt::LocalDecl(local_decl));
                        }
                    }
                }
            }
            other => retained_stmts.push(other),
        }
    }
    block.stmts = retained_stmts;

    let binding_flow = BlockBindingFlow::new(block, trailing_condition);
    let live_empty_bindings = collect_live_empty_bindings(block, &binding_flow);
    for stmt in &mut block.stmts {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            continue;
        };
        if !local_decl.values.is_empty() {
            continue;
        }
        let original_len = local_decl.bindings.len();
        local_decl.bindings.retain(|binding| {
            if !binding.rewrite_authority.may_remove_binding() {
                // 候选拒绝[LayerBoundary]：HIR 已冻结该 binding 的语义生命周期；即使
                // AST 当前看不到普通 use，也不能删除空声明或其 nil 初始化。
                return true;
            }
            if binding.origin.is_physical_root() {
                // 候选拒绝[SemanticBarrier:Lifetime]：空 PhysicalRoot declaration 会在 hoist
                // 点用 nil 清空复用的 VM home；删除后旧对象会跨过后续 GC 继续存活
                // （regress_435）。
                return true;
            }
            if binding.origin.is_debug_hinted() {
                // 候选拒绝[SemanticBarrier:DebugScope]：DebugHinted 空声明的可见期可被
                // line hook / debug.getlocal 观察（regress_341、regress_420）。
                return true;
            }

            let is_live = live_empty_bindings.contains(&binding.id);
            if is_live {
                // 候选拒绝[SemanticBarrier:Scope]：仍有读取、capture 或写入的 recovered
                // binding 必须保留，否则引用会失去原词法槽或写到外层名字。
            } else {
                // 候选接受：普通空 declaration 只把新 binding 初始化为 nil；即使带
                // `<close>` 也没有对象 root/关闭动作。binding-flow 又证明它没有域内外
                // 引用，因此删除不改变求值、生命周期或名字解析。
            }
            is_live
        });
        if local_decl.bindings.len() != original_len {
            local_decl.initializer_root_profile = None;
            changed = true;
        }
    }

    let original_len = block.stmts.len();
    // 候选接受：前一步只会产生 binding/value 同为空的声明壳；删除空 stmt 不再改变
    // initializer 求值或任何 binding 的作用域。
    block.stmts.retain(|stmt| match stmt {
        AstStmt::LocalDecl(local_decl) => {
            !(local_decl.bindings.is_empty() && local_decl.values.is_empty())
        }
        _ => true,
    });
    changed |= block.stmts.len() != original_len;

    if allow_trailing_empty_return_elision
        && matches!(
            block.stmts.last(),
            Some(AstStmt::Return(ret)) if ret.values.is_empty()
        )
    {
        // 候选接受：仅限 chunk/function 顶层 block 的最后一条无值 return；自然落出返回
        // 同样的零个结果，且不存在后继语句或 repeat 尾条件。
        block.stmts.pop();
        changed = true;
    }

    changed
}

fn inline_terminal_scoped_temp_return(block: &mut AstBlock) -> bool {
    let Some(prefix_len) = block.stmts.len().checked_sub(3) else {
        return false;
    };
    let [
        AstStmt::LocalDecl(decl),
        AstStmt::DoBlock(scoped),
        AstStmt::Return(ret),
    ] = &block.stmts[prefix_len..]
    else {
        return false;
    };
    let ([binding], [], [AstExpr::Var(returned)]) = (
        decl.bindings.as_slice(),
        decl.values.as_slice(),
        ret.values.as_slice(),
    ) else {
        return false;
    };
    if !binding.id.matches_name_ref(returned) {
        return false;
    }
    if binding.attr != AstLocalAttr::None
        || binding.origin != AstLocalOrigin::Recovered
        || !binding.rewrite_authority.may_remove_binding()
    {
        // 候选拒绝[SemanticBarrier:DebugScope]：DebugHinted carrier 的函数级可见期可由
        // debug.getlocal 观察；候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot carrier
        // 在外层 return 前仍承担精确对象 root，不能按普通 synthetic temp 消除。
        return false;
    }
    let Some(AstStmt::Assign(assign)) = scoped.stmts.last() else {
        return false;
    };
    let ([AstLValue::Name(target)], [value]) =
        (assign.targets.as_slice(), assign.values.as_slice())
    else {
        return false;
    };
    if !binding.id.matches_name_ref(target) {
        return false;
    }

    let candidate = binding.id;
    if block.stmts[..prefix_len]
        .iter()
        .any(|stmt| binding_mentions_in_stmt(stmt).contains(&candidate))
        || scoped.stmts[..scoped.stmts.len() - 1]
            .iter()
            .any(|stmt| binding_mentions_in_stmt(stmt).contains(&candidate))
        || binding_mentions_in_expr(value).contains(&candidate)
    {
        // 候选拒绝[SemanticBarrier:Scope]：carrier 在 producer 之外仍被读取、写入或捕获
        // 时，删除外层声明会留下未绑定引用，或把返回值固定到错误的 value epoch。
        return false;
    }
    if scoped.stmts.iter().any(|stmt| {
        stmt_declares_debug_binding(stmt)
            || matches!(stmt, AstStmt::LocalDecl(local_decl)
                if local_decl.bindings.iter().any(|binding| binding.attr == AstLocalAttr::Close))
    }) {
        // 候选拒绝[SemanticBarrier:DebugScope]：把 return 移进 scope 会让 Return hook 多看到
        // 直属 debug local；候选拒绝[SemanticBarrier:ValueFlow]：`<close>` 可在离域时改写
        // 外层 carrier，原程序随后读取新值，而内移 return 会先冻结 producer 值。
        return false;
    }

    let mut scoped = scoped.as_ref().clone();
    let Some(AstStmt::Assign(assign)) = scoped.stmts.pop() else {
        unreachable!("validated scoped return producer must remain an assignment")
    };
    let [value] = assign.values.as_slice() else {
        unreachable!("validated scoped return producer must remain single-valued")
    };
    let value = match value {
        // The assignment projected one result before the outer return read the carrier.  Keep
        // that width when the producer itself can reopen a value pack in return position.
        AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg => {
            AstExpr::SingleValue(Box::new(value.clone()))
        }
        _ => value.clone(),
    };
    scoped
        .stmts
        .push(AstStmt::Return(Box::new(super::super::common::AstReturn {
            values: vec![value],
        })));
    block.stmts.truncate(prefix_len);
    block.stmts.push(AstStmt::DoBlock(Box::new(scoped)));
    true
}

fn trim_unused_initialized_local_suffix(
    block: &mut AstBlock,
    binding_flow: &BlockBindingFlow,
) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            continue;
        };
        if local_decl.bindings.len() <= 1 || local_decl.values.is_empty() {
            continue;
        }

        let retained_len = local_decl
            .bindings
            .iter()
            .rposition(|binding| {
                binding.attr == AstLocalAttr::Close
                    || binding.origin != AstLocalOrigin::Recovered
                    || !binding.rewrite_authority.may_remove_binding()
                    || binding_flow.keeps_decl_alive(binding.id)
            })
            .map_or(1, |index| index + 1);
        if retained_len < local_decl.bindings.len() {
            // 候选接受：只删除逐 binding 证明无 use/capture/write 的连续尾槽；RHS
            // 完整保留，因此既不改变求值，也不移动任何保留 binding 的返回值位置。
            // 全部尾槽都满足时仍留一个，交由既有单槽事务按 initializer 类型处理。
            local_decl.bindings.truncate(retained_len);
            if let Some(profile) = &mut local_decl.initializer_root_profile {
                profile.truncate(retained_len);
            }
            changed = true;
        }
    }
    changed
}

fn split_overwritten_call_result_locals(block: &mut AstBlock, target: AstTargetDialect) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut rewritten = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        if let Some((call, declaration)) = old_stmts
            .get(index)
            .zip(old_stmts.get(index + 1))
            .and_then(|(declaration, overwrite)| {
                split_overwritten_call_result(declaration, overwrite, target)
            })
        {
            rewritten.push(AstStmt::CallStmt(Box::new(AstCallStmt { call })));
            rewritten.push(AstStmt::LocalDecl(Box::new(declaration)));
            index += 2;
            changed = true;
        } else {
            rewritten.push(
                old_stmts
                    .get(index)
                    .cloned()
                    .expect("cleanup scan index must stay in bounds"),
            );
            index += 1;
        }
    }

    block.stmts = rewritten;
    changed
}

fn split_overwritten_call_result(
    declaration: &AstStmt,
    overwrite: &AstStmt,
    target: AstTargetDialect,
) -> Option<(AstCallKind, AstLocalDecl)> {
    let AstStmt::LocalDecl(local_decl) = declaration else {
        // pair 首句不是 local declaration。
        return None;
    };
    let AstStmt::Assign(assign) = overwrite else {
        // 相邻后继不是 overwrite assignment。
        return None;
    };
    if local_decl.bindings.is_empty() {
        // 空 declaration 不产生 call-result 候选。
        return None;
    }
    if local_decl.values.is_empty() {
        // 空 value declaration 不产生 call-result 候选。
        return None;
    }
    let mut call = None;
    for value in &local_decl.values {
        match into_call_kind(value.clone()) {
            Ok(candidate) if call.is_none() => call = Some(candidate),
            Ok(_) => {
                // 候选拒绝[SemanticBarrier:Lifetime]：第一个 call 的结果原本作为 pending
                // RHS root 活过第二个 call；拆成两个 statement 会允许 GC 提前回收
                // （regress388）。
                return None;
            }
            Err(_) if is_discard_safe_expr_for_target(value, target) => {}
            Err(_) => {
                // 候选拒绝[SemanticBarrier:EvalCount]：非 call sibling 的 lookup、分配、
                // 元方法或错误事件不能随 overwritten value 一起删除。
                return None;
            }
        }
    }
    let call = call?;
    if assign.targets.len() != local_decl.bindings.len() {
        // 当前事务只消费按声明顺序完整覆盖全部 binding 的 overwrite；
        // 缺少 target 必须保留未覆盖 call result，额外 target 则包含外部写入。
        return None;
    }
    if assign.values.is_empty() {
        // 空 RHS 不产生可转入 local declaration 的 replacement。
        return None;
    }
    if !local_decl
        .bindings
        .iter()
        .zip(&assign.targets)
        .all(|(binding, target)| {
            matches!(target, AstLValue::Name(name) if binding.id.matches_name_ref(name))
        })
    {
        // 后继不是按声明顺序直接覆盖每一个同 ID binding；乱序、
        // field/index target 或部分外部写入都不属于本事务。
        return None;
    }

    if local_decl
        .bindings
        .iter()
        .any(|binding| binding.attr != AstLocalAttr::None)
    {
        // `<const>` 与 `<close>` 都不允许合法 Lua 源码中的后继
        // overwrite；这种非法 AST pair 不属于 call-result split 候选。
        return None;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| binding.origin.is_debug_hinted())
    {
        // 候选拒绝[SemanticBarrier:DebugScope]：split 会移动整组 DebugHinted 声明起点；
        // overwrite RHS 内的 line/call hook 可观察旧 local 是否已进入 debug.getlocal 范围
        // （regress_341）。
        return None;
    }
    if local_decl
        .bindings
        .iter()
        .any(|binding| !binding.rewrite_authority.may_move_scope_start())
    {
        // 候选拒绝[LayerBoundary]：把声明移动到 overwrite 点会改写 HIR 冻结的 binding
        // 起点；AST 无权用当前局部语法重新证明这段生命周期可缩短。
        return None;
    }
    if local_decl
        .bindings
        .iter()
        .enumerate()
        .any(|(index, binding)| {
            binding.origin.is_physical_root()
                && local_decl
                    .initializer_root_profile
                    .as_ref()
                    .is_none_or(|profile| profile.may_affect_collectable_lifetime(index))
        })
        && !assign
            .values
            .iter()
            .all(|value| is_discard_safe_expr_for_target(value, target))
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：事件性 RHS 求值期间，确实接到潜在可回收
        // initializer 的 PhysicalRoot 槽必须仍存活；regress388 用 RHS call 内 GC 同时
        // 证明 scalar 与 multi-home 反例。只接到 primitive/nil-fill 的 root 槽不构成屏障。
        return None;
    }

    let binding_ids = local_decl
        .bindings
        .iter()
        .map(|binding| binding.id)
        .collect::<BTreeSet<_>>();
    if assign
        .values
        .iter()
        .any(|value| !binding_mentions_in_expr(value).is_disjoint(&binding_ids))
    {
        // 候选拒绝[SemanticBarrier:Scope]：`local a,b=f(); a,b=1,use(a)` 改成
        // `f(); local a,b=1,use(a)` 后 RHS 的旧 binding 引用会解析到外层。
        return None;
    }

    // 候选接受：initializer 恰有一个 call，其余 sibling 都是无事件读取/primitive；完整
    // overwrite 相邻且 RHS 不读取任一旧 binding。非尾 call 原本被 scalarize，尾 call 原本
    // 可展开，但两者的全部结果都会在下一语句覆盖；CallStmt 同样只执行一次并丢弃结果，
    // 因此无需保留结果宽度。原 sibling 已由共享 target-aware discard proof 证明无事件；
    // copy/vararg 的来源 binding 或调用帧仍跨 call 存活，其余可丢弃 literal/运算也不产生
    // 可由 call 观察的独占 pending root，所以删除 sibling 不改变求值轨迹或生命周期。
    // replacement RHS 仍在新 local declaration 的 initializer 位置求值，同批 binding 在
    // 求值期间仍不可见，完整 RHS 的 nil fill、尾值截断和最终 binding 映射保持不变。
    // PhysicalRoot 额外要求 RHS 全部通过 target-aware 的无事件、无分配 discard proof；
    // 它们仍在原 overwrite 位置求值，所以旧 root 在这段纯求值期间提前结束不可观察。
    Some((
        call,
        AstLocalDecl {
            bindings: local_decl.bindings.clone(),
            values: assign.values.clone(),
            initializer_merge_transaction: None,
            initializer_root_profile: None,
        },
    ))
}

fn flatten_repeat_tail_do_blocks(
    block: &mut AstBlock,
    condition: &AstExpr,
    lifetime: &HirRepeatConditionLifetimeFacts,
    incoming_globals: &VisibleGlobals,
) -> bool {
    let mut changed = false;
    while let Some(AstStmt::DoBlock(nested)) = block.stmts.last() {
        if !trailing_do_block_is_scope_neutral(nested, Some(lifetime)) {
            break;
        }

        let globals_before_tail = block.stmts[..block.stmts.len() - 1]
            .iter()
            .fold(incoming_globals.clone(), |globals, stmt| {
                globals.after_stmt(stmt)
            });
        if !extending_global_scope_preserves_expr(&globals_before_tail, &nested.stmts, condition) {
            // 候选拒绝[SemanticBarrier:Scope]：展开会把尾 do 的直属 global/global-function
            // 声明延伸到 repeat condition。先从 repeat body incoming 环境只推进未移动的
            // 直属 prefix，再由共享词法解释器逐访问比较 condition 在扩域前后的许可；
            // 与 tail 无关、尚待 Deferred owner 补齐的 missing global 不会挡住本候选。
            break;
        }

        let Some(AstStmt::DoBlock(nested)) = block.stmts.pop() else {
            unreachable!("repeat tail candidate was checked above");
        };
        block.stmts.extend(nested.stmts);
        changed = true;
    }
    changed
}

fn trailing_do_block_is_scope_neutral(
    block: &AstBlock,
    repeat_lifetime: Option<&HirRepeatConditionLifetimeFacts>,
) -> bool {
    let Some(repeat_lifetime) = repeat_lifetime else {
        if block.stmts.iter().any(|stmt| {
            stmt_declares_debug_binding(stmt) || stmt_declares_hir_preserved_binding(stmt)
        }) {
            // 候选拒绝[SemanticBarrier:DebugScope]：函数 Return hook 可以在 return event
            // 观察直属 local。拍平尾 do 会把原本在 Return 前结束的 debug local 延长到
            // 函数作用域；regress420 固定运行反例，direct unit 覆盖 LocalDecl 与
            // LocalFunctionDecl 两种身份。
            return false;
        }
        // 候选接受：尾 do 与普通父 block 在同一控制流出口结束；展开不会移动任何后继
        // 求值；DebugHinted 声明已由上面的语义 guard 排除。
        return true;
    };

    let scoped_bindings = block
        .stmts
        .iter()
        .flat_map(|stmt| match stmt {
            AstStmt::LocalDecl(local_decl) => local_decl.bindings.clone(),
            AstStmt::LocalFunctionDecl(function_decl) => vec![AstLocalBinding {
                id: function_decl.name,
                attr: AstLocalAttr::None,
                origin: function_decl.origin,
                rewrite_authority: function_decl.rewrite_authority.clone(),
            }],
            _ => Vec::new(),
        })
        .map(|binding| (binding.id, binding))
        .collect::<BTreeMap<_, _>>();

    !block.stmts.iter().any(|stmt| match stmt {
        // global/global-function 的词法环境由 scoped repeat-tail owner 在 mutation 前通过
        // shared global-scope query 验证；这里仅负责正交的 lifetime/debug 边界。
        AstStmt::GlobalDecl(_) => false,
        AstStmt::LocalDecl(local_decl) => local_decl.bindings.iter().any(|binding| {
            binding_must_live_through_condition(binding, repeat_lifetime)
                || matches!(binding.rewrite_authority, AstRewriteAuthority::AstOwned)
                    && (binding.origin.is_physical_root()
                        || local_decl.values.iter().any(expr_contains_function))
        }),
        AstStmt::LocalFunctionDecl(function_decl) => {
            let binding = scoped_bindings
                .get(&function_decl.name)
                .expect("direct local function must be indexed as a scoped binding");
            binding_must_live_through_condition(binding, repeat_lifetime)
                // AST-owned local function 没有 HIR endpoint certificate；其闭包 root 继续
                // 由当前候选的源码层保守证明约束。
                || matches!(binding.rewrite_authority, AstRewriteAuthority::AstOwned)
        }
        AstStmt::Assign(assign) => {
            // HIR-origin scoped binding 已在直属声明处消费 endpoint certificate。这里只
            // 保留 AST-owned binding 与未能确认来源的 hoisted carrier。
            assign.values.iter().any(expr_contains_function)
                && assign.targets.iter().any(|target| {
                    matches!(
                        target,
                        AstLValue::Name(name)
                            if AstBindingRef::from_name_ref(name).is_some_and(|binding| {
                                closure_target_needs_scope_barrier(
                                    binding,
                                    &scoped_bindings,
                                    repeat_lifetime,
                                )
                            })
                    )
                })
        }
        AstStmt::FunctionDecl(function_decl) => {
            let path = match &function_decl.target {
                crate::ast::common::AstFunctionName::Plain(path)
                | crate::ast::common::AstFunctionName::Method(path, _) => path,
            };
            // 候选拒绝[SemanticBarrier:Lifetime]：`local holder={}; function holder.f() end`
            // 让当前 do 的 holder 持有函数 root；拍平会把 holder 延寿到 condition 之后。
            AstBindingRef::from_name_ref(&path.root).is_some_and(|binding| {
                closure_target_needs_scope_barrier(binding, &scoped_bindings, repeat_lifetime)
            })
        }
        _ => {
            // 候选接受：其余语句不在 repeat 条件前引入 global、资源 local，或由当前
            // do binding 持有的 closure root；展开只删除机械缩进，控制流和求值顺序不变。
            false
        }
    })
}

fn stmt_declares_debug_binding(stmt: &AstStmt) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .bindings
            .iter()
            .any(|binding| binding.origin.is_debug_hinted()),
        AstStmt::LocalFunctionDecl(function_decl) => function_decl.origin.is_debug_hinted(),
        _ => false,
    }
}

fn stmt_declares_hir_preserved_binding(stmt: &AstStmt) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl
            .bindings
            .iter()
            .any(|binding| binding.rewrite_authority.must_preserve()),
        AstStmt::LocalFunctionDecl(function_decl) => {
            function_decl.rewrite_authority.must_preserve()
        }
        _ => false,
    }
}

fn closure_target_needs_scope_barrier(
    binding: AstBindingRef,
    scoped_bindings: &BTreeMap<AstBindingRef, AstLocalBinding>,
    lifetime: &HirRepeatConditionLifetimeFacts,
) -> bool {
    if let Some(binding) = scoped_bindings.get(&binding) {
        return matches!(binding.rewrite_authority, AstRewriteAuthority::AstOwned);
    }
    match binding {
        AstBindingRef::Temp(_) => !hir_binding_may_end_before_condition(binding, lifetime),
        // 缺少 declaration authority 时，SyntheticLocal 可能是 AST 自建身份，不能只凭
        // 数字碰巧相同就借用 HIR temp certificate。
        AstBindingRef::SyntheticLocal(_) => true,
        AstBindingRef::Local(_) => false,
    }
}

fn expr_contains_function(expr: &AstExpr) -> bool {
    if matches!(expr, AstExpr::FunctionExpr(_)) {
        return true;
    }
    let mut found = false;
    traverse_expr_children!(
        expr,
        iter = iter,
        borrow = [&],
        expr(child) => {
            found |= expr_contains_function(child);
        },
        function(_function) => {
            found = true;
        }
    );
    found
}

fn can_elide_single_stmt_do_block(stmt: &AstStmt) -> bool {
    match stmt {
        AstStmt::Assign(_)
        | AstStmt::CallStmt(_)
        | AstStmt::Return(_)
        | AstStmt::If(_)
        | AstStmt::While(_)
        | AstStmt::Repeat(_)
        | AstStmt::NumericFor(_)
        | AstStmt::GenericFor(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::Label(_) => {
            // 候选接受：唯一语句不声明外层可见 binding；label/goto 使用稳定 AstLabelId，
            // 生成名也由 ID 唯一确定，删除空 do 不会重新绑定已有控制流边。
            true
        }
        // 候选拒绝[SemanticBarrier:Lifetime]：单句 local 移出 do 会把对象 root/`<close>`
        // 延长到父域末；lua54_01_close#18 与 regress246 分别观察普通 root 和 close 时点。
        AstStmt::LocalDecl(_) => false,
        // 候选拒绝[SemanticBarrier:Scope]：`do global x=1 end; print(x)` 在 Lua 5.5 中
        // 原形拒绝未声明 x，拍平后却打印 1；global declaration 不能越过普通父块后继。
        AstStmt::GlobalDecl(_) => false,
        // 候选拒绝[SemanticBarrier:Scope]：`do local function f() end end; print(f)` 原形
        // 读取 global f，拍平后读取新 local f。
        AstStmt::LocalFunctionDecl(_) => false,
        // 候选接受：外层 do 内只有另一个 do，所有声明/label/goto 仍受内层 block 约束；
        // 删除空的外层词法层不扩大任何内部 binding 或控制流实体的作用域。
        AstStmt::DoBlock(_) => true,
        // 候选接受：Error statement 本体仍原位保留；do 壳不承载额外诊断内容或词法
        // identity，删除它不会丢失 best-effort 失败证据。
        AstStmt::Error(_) => true,
    }
}

struct BlockBindingFlow {
    mention_counts: BTreeMap<AstBindingRef, usize>,
    use_index: BindingUseIndex,
}

impl BlockBindingFlow {
    fn new(block: &AstBlock, trailing_condition: Option<&AstExpr>) -> Self {
        let mut mention_counts = BTreeMap::<AstBindingRef, usize>::new();
        for stmt in &block.stmts {
            for binding in binding_mentions_in_stmt(stmt) {
                *mention_counts.entry(binding).or_default() += 1;
            }
        }
        if let Some(condition) = trailing_condition {
            for binding in super::binding_flow::binding_mentions_in_expr(condition) {
                *mention_counts.entry(binding).or_default() += 1;
            }
        }
        let use_index =
            BindingUseIndex::for_stmts_with_trailing_expr(&block.stmts, trailing_condition);
        Self {
            mention_counts,
            use_index,
        }
    }

    fn mentioned_outside_own_decl(&self, binding: AstBindingRef) -> bool {
        // local 声明自身也算一次 mention；只有声明外还有提及时，才需要保留词法槽位。
        self.mention_counts.get(&binding).copied().unwrap_or(0) > 1
    }

    fn used_or_captured(&self, binding: AstBindingRef) -> bool {
        self.use_index.count_uses_in_suffix(0, binding) != 0
    }

    fn keeps_decl_alive(&self, binding: AstBindingRef) -> bool {
        self.mentioned_outside_own_decl(binding) || self.used_or_captured(binding)
    }
}

fn collect_live_empty_bindings(
    block: &AstBlock,
    binding_flow: &BlockBindingFlow,
) -> BTreeSet<AstBindingRef> {
    let mut live_bindings = BTreeSet::new();
    for stmt in &block.stmts {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            continue;
        };
        for binding in &local_decl.bindings {
            if binding_flow.keeps_decl_alive(binding.id) {
                live_bindings.insert(binding.id);
            }
        }
    }
    live_bindings
}

fn into_call_kind(expr: AstExpr) -> Result<AstCallKind, AstExpr> {
    match expr {
        AstExpr::Call(call) => Ok(AstCallKind::Call(call)),
        AstExpr::MethodCall(call) => Ok(AstCallKind::MethodCall(call)),
        AstExpr::SingleValue(inner) => {
            into_call_kind(*inner).map_err(|inner| AstExpr::SingleValue(Box::new(inner)))
        }
        other => Err(other),
    }
}

#[derive(Clone, Copy)]
enum UnusedValueRejection {
    EvalCount,
    ControlFlow,
    Allocation,
    TargetConstraint,
    PolicyBoundary,
}

fn unused_value_rejection(expr: &AstExpr, target: AstTargetDialect) -> UnusedValueRejection {
    debug_assert!(!is_discard_safe_expr_for_target(expr, target));

    let rejected_child = |child: &AstExpr| {
        (!is_discard_safe_expr_for_target(child, target))
            .then(|| unused_value_rejection(child, target))
    };
    match expr {
        AstExpr::SingleValue(inner) => unused_value_rejection(inner, target),
        AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => {
            unused_value_rejection(&unary.expr, target)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => rejected_child(&logical.lhs)
            .or_else(|| rejected_child(&logical.rhs))
            .unwrap_or(UnusedValueRejection::ControlFlow),
        AstExpr::Unary(unary) => {
            rejected_child(&unary.expr).unwrap_or_else(|| operation_rejection(expr, target))
        }
        AstExpr::Binary(binary) => rejected_child(&binary.lhs)
            .or_else(|| rejected_child(&binary.rhs))
            .unwrap_or_else(|| {
                if binary.op == AstBinaryOpKind::Concat {
                    UnusedValueRejection::Allocation
                } else {
                    operation_rejection(expr, target)
                }
            }),
        AstExpr::Var(AstNameRef::Global(_))
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_) => UnusedValueRejection::EvalCount,
        AstExpr::TableConstructor(_) | AstExpr::FunctionExpr(_) => UnusedValueRejection::Allocation,
        AstExpr::Error(_) => UnusedValueRejection::PolicyBoundary,
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg => {
            debug_assert!(
                is_discard_safe_expr_for_target(expr, target),
                "discard-safe leaf reached rejection classifier"
            );
            UnusedValueRejection::PolicyBoundary
        }
    }
}

fn operation_rejection(expr: &AstExpr, target: AstTargetDialect) -> UnusedValueRejection {
    if matches!(
        target.version,
        crate::decompile::DecompileDialect::Auto
            | crate::decompile::DecompileDialect::Lua51
            | crate::decompile::DecompileDialect::Lua52
    ) && is_discard_safe_expr_for_target(
        expr,
        AstTargetDialect::new(crate::decompile::DecompileDialect::Lua53),
    ) {
        UnusedValueRejection::TargetConstraint
    } else {
        UnusedValueRejection::ControlFlow
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::common::{
        AstAssign, AstCallExpr, AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstGlobalAttr,
        AstGlobalBinding, AstGlobalBindingTarget, AstGlobalDecl, AstGlobalName, AstLValue,
        AstLocalBinding, AstLocalFunctionDecl, AstLogicalExpr, AstNamePath, AstNameRef, AstRepeat,
        AstReturn,
    };
    use crate::hir::{
        HirExpr, HirInlineDisposition, HirPackTail, HirProtoRef, HirRepeatBinding, HirValuePack,
        LocalId, ParamId, TempId, initializer_root_profile,
    };

    fn recovered_binding() -> AstLocalBinding {
        AstLocalBinding {
            id: AstBindingRef::Local(LocalId(0)),
            attr: AstLocalAttr::None,
            origin: AstLocalOrigin::Recovered,
            rewrite_authority: crate::ast::common::AstRewriteAuthority::AstOwned,
        }
    }

    fn call_value() -> AstExpr {
        AstExpr::Call(Box::new(AstCallExpr {
            callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                text: "factory".to_owned(),
            })),
            args: vec![],
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
        }))
    }

    fn function_value() -> AstExpr {
        AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
            function: HirProtoRef(1),
            params: vec![],
            is_vararg: false,
            named_vararg: None,
            body: AstBlock::default(),
            captured_bindings: BTreeSet::new(),
            captured_params: BTreeSet::new(),
            capture_names_by_upvalue: std::collections::BTreeMap::new(),
            capture_write_names: BTreeSet::new(),
        }))
    }

    #[test]
    fn splits_recovered_call_result_before_direct_overwrite() {
        let target = AstTargetDialect::new(crate::decompile::DecompileDialect::Lua54);
        let binding = recovered_binding();
        let declaration = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![binding.clone()],
            values: vec![call_value()],
            initializer_merge_transaction: None,
            initializer_root_profile: None,
        }));
        let overwrite = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(binding.id.to_name_ref())],
            values: vec![AstExpr::Integer(9), call_value()],
            initializer_merge_transaction: None,
            method_rewrite_transaction: None,
        }));

        let (call, rewritten) = split_overwritten_call_result(&declaration, &overwrite, target)
            .expect("a recovered call result with a direct overwrite is safe to split");
        assert!(matches!(call, AstCallKind::Call(_)));
        assert_eq!(rewritten.bindings, vec![binding.clone()]);
        assert_eq!(rewritten.values, vec![AstExpr::Integer(9), call_value()]);

        let missing_target = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![],
            values: vec![AstExpr::Integer(9)],
            initializer_merge_transaction: None,
            method_rewrite_transaction: None,
        }));
        assert!(split_overwritten_call_result(&declaration, &missing_target, target).is_none());
        let extra_target = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![
                AstLValue::Name(binding.id.to_name_ref()),
                AstLValue::Name(AstNameRef::Global(AstGlobalName {
                    text: "sink".to_owned(),
                })),
            ],
            values: vec![AstExpr::Integer(9), AstExpr::Integer(10)],
            initializer_merge_transaction: None,
            method_rewrite_transaction: None,
        }));
        assert!(split_overwritten_call_result(&declaration, &extra_target, target).is_none());

        let multiple_initializers = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![binding.clone()],
            values: vec![call_value(), call_value()],
            initializer_merge_transaction: None,
            initializer_root_profile: None,
        }));
        assert!(
            split_overwritten_call_result(&multiple_initializers, &overwrite, target).is_none()
        );

        let one_call_with_primitive_sibling = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![binding],
            values: vec![AstExpr::Integer(0), call_value()],
            initializer_merge_transaction: None,
            initializer_root_profile: None,
        }));
        assert!(
            split_overwritten_call_result(&one_call_with_primitive_sibling, &overwrite, target)
                .is_some()
        );
    }

    #[test]
    fn keeps_debug_and_later_rhs_reads_but_splits_same_id_initializer() {
        let target = AstTargetDialect::new(crate::decompile::DecompileDialect::Lua54);
        let mut debug_binding = recovered_binding();
        debug_binding.origin = AstLocalOrigin::DebugHinted;
        let debug_decl = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![debug_binding.clone()],
            values: vec![call_value()],
            initializer_merge_transaction: None,
            initializer_root_profile: None,
        }));
        let debug_write = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(debug_binding.id.to_name_ref())],
            values: vec![AstExpr::Integer(9)],
            initializer_merge_transaction: None,
            method_rewrite_transaction: None,
        }));
        assert!(split_overwritten_call_result(&debug_decl, &debug_write, target).is_none());

        let binding = recovered_binding();
        let self_call = AstExpr::Call(Box::new(AstCallExpr {
            callee: AstExpr::Var(binding.id.to_name_ref()),
            args: vec![],
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
        }));
        let declaration = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![binding.clone()],
            values: vec![self_call],
            initializer_merge_transaction: None,
            initializer_root_profile: None,
        }));
        let overwrite = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(binding.id.to_name_ref())],
            values: vec![AstExpr::Integer(9)],
            initializer_merge_transaction: None,
            method_rewrite_transaction: None,
        }));
        let (call, _) = split_overwritten_call_result(&declaration, &overwrite, target)
            .expect("the call stays before the local lexical scope in both shapes");
        let AstCallKind::Call(call) = call else {
            panic!("same-id initializer should preserve the direct call");
        };
        assert_eq!(call.callee, AstExpr::Var(binding.id.to_name_ref()));

        let declaration = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![binding.clone()],
            values: vec![call_value()],
            initializer_merge_transaction: None,
            initializer_root_profile: None,
        }));
        let later_rhs_read = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(binding.id.to_name_ref())],
            values: vec![AstExpr::Integer(9), AstExpr::Var(binding.id.to_name_ref())],
            initializer_merge_transaction: None,
            method_rewrite_transaction: None,
        }));
        assert!(split_overwritten_call_result(&declaration, &later_rhs_read, target).is_none());

        let mut physical_binding = recovered_binding();
        physical_binding.origin = AstLocalOrigin::PhysicalRoot;
        let physical_decl = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![physical_binding.clone()],
            values: vec![call_value()],
            initializer_merge_transaction: None,
            initializer_root_profile: None,
        }));
        let copy_overwrite = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(physical_binding.id.to_name_ref())],
            values: vec![AstExpr::Var(AstNameRef::Param(ParamId(0)))],
            initializer_merge_transaction: None,
            method_rewrite_transaction: None,
        }));
        let (_, rewritten) = split_overwritten_call_result(&physical_decl, &copy_overwrite, target)
            .expect("an eventless parameter copy cannot observe early root release");
        assert_eq!(
            rewritten.values,
            vec![AstExpr::Var(AstNameRef::Param(ParamId(0)))]
        );

        let eventful_overwrite = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(physical_binding.id.to_name_ref())],
            values: vec![call_value()],
            initializer_merge_transaction: None,
            method_rewrite_transaction: None,
        }));
        assert!(
            split_overwritten_call_result(&physical_decl, &eventful_overwrite, target).is_none()
        );

        let recovered_second = AstLocalBinding {
            id: AstBindingRef::Local(LocalId(1)),
            attr: AstLocalAttr::None,
            origin: AstLocalOrigin::Recovered,
            rewrite_authority: crate::ast::common::AstRewriteAuthority::AstOwned,
        };
        let primitive_physical_decl = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![physical_binding.clone(), recovered_second.clone()],
            values: vec![AstExpr::Integer(0), call_value()],
            initializer_merge_transaction: None,
            initializer_root_profile: Some(initializer_root_profile(
                target.version,
                &HirValuePack::fixed(vec![HirExpr::Integer(0), HirExpr::LocalRef(LocalId(1))]),
                2,
            )),
        }));
        let eventful_full_overwrite = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![
                AstLValue::Name(physical_binding.id.to_name_ref()),
                AstLValue::Name(recovered_second.id.to_name_ref()),
            ],
            values: vec![call_value()],
            initializer_merge_transaction: None,
            method_rewrite_transaction: None,
        }));
        assert!(
            split_overwritten_call_result(
                &primitive_physical_decl,
                &eventful_full_overwrite,
                target,
            )
            .is_some()
        );

        let mut physical_second = recovered_second;
        physical_second.origin = AstLocalOrigin::PhysicalRoot;
        let expanded_tail_physical_decl = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![recovered_binding(), physical_second.clone()],
            values: vec![call_value()],
            initializer_merge_transaction: None,
            initializer_root_profile: Some(initializer_root_profile(
                target.version,
                &HirValuePack::expanding(Vec::new(), HirPackTail::open(HirExpr::VarArg)),
                2,
            )),
        }));
        assert!(
            split_overwritten_call_result(
                &expanded_tail_physical_decl,
                &eventful_full_overwrite,
                target,
            )
            .is_none()
        );

        let scalar_tail_physical_decl = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![recovered_binding(), physical_second],
            values: vec![AstExpr::SingleValue(Box::new(call_value()))],
            initializer_merge_transaction: None,
            initializer_root_profile: Some(initializer_root_profile(
                target.version,
                &HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(0))]),
                2,
            )),
        }));
        assert!(
            split_overwritten_call_result(
                &scalar_tail_physical_decl,
                &eventful_full_overwrite,
                target,
            )
            .is_some()
        );
    }

    #[test]
    fn returns_terminal_scoped_producer_without_a_hoisted_carrier() {
        let binding = recovered_binding();
        let mut block = AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![binding.clone()],
                    values: vec![],
                    initializer_merge_transaction: None,
                    initializer_root_profile: None,
                })),
                AstStmt::DoBlock(Box::new(AstBlock {
                    stmts: vec![AstStmt::Assign(Box::new(AstAssign {
                        targets: vec![AstLValue::Name(binding.id.to_name_ref())],
                        values: vec![function_value()],
                        initializer_merge_transaction: None,
                        method_rewrite_transaction: None,
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Var(binding.id.to_name_ref())],
                })),
            ],
        };

        assert!(inline_terminal_scoped_temp_return(&mut block));
        let [AstStmt::DoBlock(scoped)] = block.stmts.as_slice() else {
            panic!("the exact producer scope should own the terminal return")
        };
        assert!(matches!(
            scoped.stmts.as_slice(),
            [AstStmt::Return(ret)] if matches!(ret.values.as_slice(), [AstExpr::FunctionExpr(_)])
        ));
    }

    #[test]
    fn keeps_scoped_carrier_when_close_can_rewrite_it_before_return() {
        let binding = recovered_binding();
        let close_binding = AstLocalBinding {
            id: AstBindingRef::Local(LocalId(1)),
            attr: AstLocalAttr::Close,
            origin: AstLocalOrigin::Recovered,
            rewrite_authority: crate::ast::common::AstRewriteAuthority::AstOwned,
        };
        let mut block = AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![binding.clone()],
                    values: vec![],
                    initializer_merge_transaction: None,
                    initializer_root_profile: None,
                })),
                AstStmt::DoBlock(Box::new(AstBlock {
                    stmts: vec![
                        AstStmt::LocalDecl(Box::new(AstLocalDecl {
                            bindings: vec![close_binding],
                            values: vec![AstExpr::Var(AstNameRef::Global(AstGlobalName {
                                text: "resource".to_owned(),
                            }))],
                            initializer_merge_transaction: None,
                            initializer_root_profile: None,
                        })),
                        AstStmt::Assign(Box::new(AstAssign {
                            targets: vec![AstLValue::Name(binding.id.to_name_ref())],
                            values: vec![AstExpr::Integer(1)],
                            initializer_merge_transaction: None,
                            method_rewrite_transaction: None,
                        })),
                    ],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Var(binding.id.to_name_ref())],
                })),
            ],
        };

        assert!(!inline_terminal_scoped_temp_return(&mut block));
    }

    #[test]
    fn keeps_repeat_tail_global_declaration_scope() {
        assert!(can_elide_single_stmt_do_block(&AstStmt::Error(
            "diagnostic".to_owned()
        )));

        let global_name = |text: &str| AstGlobalName {
            text: text.to_owned(),
        };
        let named_decl = |name: &AstGlobalName, attr| {
            AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
                bindings: vec![AstGlobalBinding {
                    target: AstGlobalBindingTarget::Name(name.clone()),
                    attr,
                }],
                values: vec![],
            }))
        };
        let wildcard_decl = |attr| {
            AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
                bindings: vec![AstGlobalBinding {
                    target: AstGlobalBindingTarget::Wildcard,
                    attr,
                }],
                values: vec![],
            }))
        };
        let nested_write = |name: &AstGlobalName| {
            AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                function: HirProtoRef(2),
                params: vec![],
                is_vararg: false,
                named_vararg: None,
                body: AstBlock {
                    stmts: vec![AstStmt::Assign(Box::new(AstAssign {
                        targets: vec![AstLValue::Name(AstNameRef::Global(name.clone()))],
                        values: vec![AstExpr::Integer(1)],
                        initializer_merge_transaction: None,
                        method_rewrite_transaction: None,
                    }))],
                },
                captured_bindings: BTreeSet::new(),
                captured_params: BTreeSet::new(),
                capture_names_by_upvalue: BTreeMap::new(),
                capture_write_names: BTreeSet::new(),
            }))
        };

        let stop = global_name("stop");
        let missing = global_name("missing");
        let mut named_const_extension = AstBlock {
            stmts: vec![
                named_decl(&stop, AstGlobalAttr::None),
                AstStmt::DoBlock(Box::new(AstBlock {
                    stmts: vec![named_decl(&stop, AstGlobalAttr::Const)],
                })),
            ],
        };
        assert!(!flatten_repeat_tail_do_blocks(
            &mut named_const_extension,
            &AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                lhs: AstExpr::Var(AstNameRef::Global(missing.clone())),
                rhs: nested_write(&stop),
            })),
            &Default::default(),
            &VisibleGlobals::default(),
        ));
        assert!(matches!(
            named_const_extension.stmts.last(),
            Some(AstStmt::DoBlock(_))
        ));

        let mut named_none_extension = AstBlock {
            stmts: vec![
                named_decl(&stop, AstGlobalAttr::Const),
                AstStmt::DoBlock(Box::new(AstBlock {
                    stmts: vec![named_decl(&stop, AstGlobalAttr::None)],
                })),
            ],
        };
        assert!(flatten_repeat_tail_do_blocks(
            &mut named_none_extension,
            &AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                lhs: AstExpr::Var(AstNameRef::Global(missing)),
                rhs: AstExpr::Var(AstNameRef::Global(stop)),
            })),
            &Default::default(),
            &VisibleGlobals::default(),
        ));

        let marker = global_name("marker");
        let mut wildcard_extension = AstModule {
            entry_function: HirProtoRef(0),
            body: AstBlock {
                stmts: vec![
                    wildcard_decl(AstGlobalAttr::None),
                    AstStmt::Repeat(Box::new(AstRepeat {
                        body: AstBlock {
                            stmts: vec![AstStmt::DoBlock(Box::new(AstBlock {
                                stmts: vec![wildcard_decl(AstGlobalAttr::Const)],
                            }))],
                        },
                        cond: nested_write(&marker),
                        lifetime: Default::default(),
                    })),
                ],
            },
        };
        assert!(!walk::rewrite_module_scoped(
            &mut wildcard_extension,
            &VisibleGlobals::default(),
            &mut RepeatTailCleanupPass,
        ));
        let AstStmt::Repeat(repeat_stmt) = &wildcard_extension.body.stmts[1] else {
            panic!("repeat statement should remain in place");
        };
        assert!(matches!(
            repeat_stmt.body.stmts.as_slice(),
            [AstStmt::DoBlock(_)]
        ));

        let function_name = global_name("recur");
        let AstExpr::FunctionExpr(function) = nested_write(&function_name) else {
            unreachable!("test helper always returns a function expression");
        };
        let mut global_function_extension = AstBlock {
            stmts: vec![
                wildcard_decl(AstGlobalAttr::Const),
                AstStmt::DoBlock(Box::new(AstBlock {
                    stmts: vec![AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                        target: AstFunctionName::Plain(AstNamePath {
                            root: AstNameRef::Global(function_name.clone()),
                            fields: vec![],
                        }),
                        func: *function,
                    }))],
                })),
            ],
        };
        assert!(flatten_repeat_tail_do_blocks(
            &mut global_function_extension,
            &AstExpr::Var(AstNameRef::Global(function_name)),
            &Default::default(),
            &VisibleGlobals::default(),
        ));
    }

    #[test]
    fn keeps_direct_debug_binding_scope_with_or_without_return() {
        let mut debug_binding = recovered_binding();
        debug_binding.origin = AstLocalOrigin::DebugHinted;
        let declaration = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![debug_binding.clone()],
            values: vec![AstExpr::Integer(1)],
            initializer_merge_transaction: None,
            initializer_root_profile: None,
        }));
        let return_stmt = AstStmt::Return(Box::new(AstReturn { values: vec![] }));

        let returning_local = AstBlock {
            stmts: vec![declaration.clone(), return_stmt.clone()],
        };
        assert!(!trailing_do_block_is_scope_neutral(&returning_local, None));
        let falling_through_local = AstBlock {
            stmts: vec![declaration],
        };
        assert!(!trailing_do_block_is_scope_neutral(
            &falling_through_local,
            None
        ));

        let function = match function_value() {
            AstExpr::FunctionExpr(function) => *function,
            _ => unreachable!(),
        };
        let local_function = AstStmt::LocalFunctionDecl(Box::new(AstLocalFunctionDecl {
            name: debug_binding.id,
            origin: AstLocalOrigin::DebugHinted,
            rewrite_authority: crate::ast::common::AstRewriteAuthority::AstOwned,
            func: function,
        }));
        let returning_function = AstBlock {
            stmts: vec![local_function.clone(), return_stmt],
        };
        assert!(!trailing_do_block_is_scope_neutral(
            &returning_function,
            None
        ));
        let falling_through_function = AstBlock {
            stmts: vec![local_function],
        };
        assert!(!trailing_do_block_is_scope_neutral(
            &falling_through_function,
            None
        ));
    }

    #[test]
    fn keeps_repeat_tail_closure_roots_owned_by_nested_locals() {
        let condition = AstExpr::Boolean(true);
        let lifetime = HirRepeatConditionLifetimeFacts::default();
        let binding = recovered_binding();
        let assigned_closure = AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![binding.clone()],
                    values: vec![],
                    initializer_merge_transaction: None,
                    initializer_root_profile: None,
                })),
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(binding.id.to_name_ref())],
                    values: vec![function_value()],
                    initializer_merge_transaction: None,
                    method_rewrite_transaction: None,
                })),
            ],
        };
        assert!(!trailing_do_block_is_scope_neutral(
            &assigned_closure,
            Some(&lifetime)
        ));

        let hoisted_temp = AstBindingRef::Temp(TempId(7));
        let hoisted_closure = AstBlock {
            stmts: vec![AstStmt::Assign(Box::new(AstAssign {
                targets: vec![AstLValue::Name(hoisted_temp.to_name_ref())],
                values: vec![AstExpr::SingleValue(Box::new(function_value()))],
                initializer_merge_transaction: None,
                method_rewrite_transaction: None,
            }))],
        };
        assert!(!trailing_do_block_is_scope_neutral(
            &hoisted_closure,
            Some(&lifetime)
        ));
        let mut repeat_body = AstBlock {
            stmts: vec![AstStmt::DoBlock(Box::new(hoisted_closure))],
        };
        assert!(!cleanup_block(
            &mut repeat_body,
            false,
            Some(&condition),
            AstTargetDialect::new(crate::decompile::DecompileDialect::Lua54),
        ));
        assert!(matches!(
            repeat_body.stmts.as_slice(),
            [AstStmt::DoBlock(_)]
        ));

        let rooted_function_decl = AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![binding.clone()],
                    values: vec![],
                    initializer_merge_transaction: None,
                    initializer_root_profile: None,
                })),
                AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                    target: AstFunctionName::Plain(AstNamePath {
                        root: binding.id.to_name_ref(),
                        fields: vec!["method".to_owned()],
                    }),
                    func: match function_value() {
                        AstExpr::FunctionExpr(function) => *function,
                        _ => unreachable!(),
                    },
                })),
            ],
        };
        assert!(!trailing_do_block_is_scope_neutral(
            &rooted_function_decl,
            Some(&lifetime)
        ));

        let outer_binding = AstBindingRef::Local(LocalId(99));
        let outer_assignment = AstBlock {
            stmts: vec![AstStmt::Assign(Box::new(AstAssign {
                targets: vec![AstLValue::Name(outer_binding.to_name_ref())],
                values: vec![function_value()],
                initializer_merge_transaction: None,
                method_rewrite_transaction: None,
            }))],
        };
        assert!(trailing_do_block_is_scope_neutral(
            &outer_assignment,
            Some(&lifetime)
        ));
    }

    #[test]
    fn repeat_tail_hir_closure_requires_its_endpoint_certificate() {
        let mut binding = recovered_binding();
        binding.rewrite_authority = AstRewriteAuthority::Hir(HirInlineDisposition::Unknown);
        let hir_closure = AstBlock {
            stmts: vec![AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: vec![binding],
                values: vec![function_value()],
                initializer_merge_transaction: None,
                initializer_root_profile: None,
            }))],
        };

        assert!(!trailing_do_block_is_scope_neutral(
            &hir_closure,
            Some(&HirRepeatConditionLifetimeFacts::default())
        ));

        let certified = HirRepeatConditionLifetimeFacts {
            may_end_before_condition: BTreeSet::from([HirRepeatBinding::Local(LocalId(0))]),
        };
        assert!(trailing_do_block_is_scope_neutral(
            &hir_closure,
            Some(&certified)
        ));

        let ast_owned_closure = AstBlock {
            stmts: vec![AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: vec![recovered_binding()],
                values: vec![function_value()],
                initializer_merge_transaction: None,
                initializer_root_profile: None,
            }))],
        };
        assert!(!trailing_do_block_is_scope_neutral(
            &ast_owned_closure,
            Some(&certified)
        ));
    }
}
