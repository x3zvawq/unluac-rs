//! 这个文件负责清理已经没有源码意义的机械 AST 壳。
//!
//! 它依赖前面的结构恢复和 readability pass 已经把真正需要保留的局部作用域、
//! 控制流和显式 return 暴露出来；这里专门删除“只剩形式意义”的 do-end、空 local、
//! 以及 chunk/function 结尾的无值 return。它不会越权合并业务语句，也不会把仍有
//! 词法意义的块错误拍平。
//!
//! 例子：
//! - `do print(x) end` 会在内部没有局部作用域意义时折成 `print(x)`
//! - `local t0` 这种只剩机械 temp 壳、且没有值也没有使用的声明会被删除
//! - 未使用的 recovered `local t0 = side_effect()` 会保留为 `side_effect()` 调用
//! - 函数尾部的 `return` 会在没有返回值时被去掉

use std::collections::{BTreeMap, BTreeSet};

use super::super::common::{
    AstBindingRef, AstBlock, AstCallKind, AstCallStmt, AstExpr, AstLocalAttr, AstLocalDecl,
    AstLocalOrigin, AstModule, AstStmt,
};
use super::ReadabilityContext;
use super::binding_flow::{BindingUseIndex, binding_mentions_in_expr, binding_mentions_in_stmt};
use super::expr_analysis::is_discard_safe_expr;
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    walk::rewrite_module(module, &mut CleanupPass)
}

struct CleanupPass;

impl AstRewritePass for CleanupPass {
    fn rewrite_block(&mut self, block: &mut AstBlock, kind: BlockKind) -> bool {
        cleanup_block(
            block,
            matches!(kind, BlockKind::ModuleBody | BlockKind::FunctionBody),
            None,
        )
    }

    fn rewrite_repeat_body(&mut self, block: &mut AstBlock, condition: &AstExpr) -> bool {
        cleanup_block(block, false, Some(condition))
    }
}

fn cleanup_block(
    block: &mut AstBlock,
    allow_trailing_empty_return_elision: bool,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let mut changed = false;

    let old_stmts = std::mem::take(&mut block.stmts);
    let mut flattened_stmts = Vec::with_capacity(old_stmts.len());
    for stmt in old_stmts {
        match stmt {
            AstStmt::DoBlock(nested)
                if nested.stmts.len() == 1 && can_elide_single_stmt_do_block(&nested.stmts[0]) =>
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
    changed |= split_overwritten_call_result_locals(block);

    // 尾部 do-end 展开：当 do-end 是块的最后一条语句时，其内部 local 的作用域
    // 在父块结束处同样终止，do-end 仅是多余的缩进壳。
    // 典型来源：guard-flip 把 `if cond then BODY else return end` 拉平成
    // `if not cond then return end; do BODY end`，其中 BODY 含 local 声明。
    // 例外：global 声明、`<close>` local 和局部 closure 的 do-end 有实际作用域语义，
    // 保留。尤其 repeat body 与 until 条件共享外层作用域，拍平资源块会把关闭时点推迟到
    // 条件之后；局部 closure 则会把自身和 captured value 的 root 生命周期延长到父块末尾。
    while let Some(AstStmt::DoBlock(nested)) = block.stmts.last()
        && trailing_do_block_is_scope_neutral(nested)
    {
        let Some(AstStmt::DoBlock(nested)) = block.stmts.pop() else {
            unreachable!();
        };
        block.stmts.extend(nested.stmts);
        changed = true;
    }

    let binding_flow = BlockBindingFlow::new(block, trailing_condition);
    let original_stmts = std::mem::take(&mut block.stmts);
    let mut retained_stmts = Vec::with_capacity(original_stmts.len());
    for stmt in original_stmts {
        match stmt {
            AstStmt::LocalDecl(mut local_decl)
                if local_decl.bindings.len() == 1
                    && local_decl.values.len() == 1
                    && local_decl.bindings[0].attr == AstLocalAttr::None
                    && local_decl.bindings[0].origin == AstLocalOrigin::Recovered
                    && !binding_flow.keeps_decl_alive(local_decl.bindings[0].id) =>
            {
                if is_discard_safe_expr(&local_decl.values[0]) {
                    changed = true;
                } else {
                    let Some(value) = local_decl.values.pop() else {
                        retained_stmts.push(AstStmt::LocalDecl(local_decl));
                        continue;
                    };
                    match into_call_kind(value) {
                        Ok(call) => {
                            retained_stmts.push(AstStmt::CallStmt(Box::new(AstCallStmt { call })));
                            changed = true;
                        }
                        Err(value) => {
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
    let live_mechanical_bindings = collect_live_mechanical_bindings(block, &binding_flow);
    for stmt in &mut block.stmts {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            continue;
        };
        if !local_decl.values.is_empty() {
            continue;
        }
        let original_len = local_decl.bindings.len();
        local_decl.bindings.retain(|binding| match binding.id {
            AstBindingRef::Temp(_) | AstBindingRef::SyntheticLocal(_) => {
                live_mechanical_bindings.contains(&binding.id)
            }
            AstBindingRef::Local(_) => true,
        });
        changed |= local_decl.bindings.len() != original_len;
    }

    let original_len = block.stmts.len();
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
        // 尾部无值 return 只是 VM 的函数/chunk 结束痕迹，不是值得保留到源码层的语句。
        block.stmts.pop();
        changed = true;
    }

    changed
}

fn split_overwritten_call_result_locals(block: &mut AstBlock) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut rewritten = Vec::with_capacity(old_stmts.len());
    let mut changed = false;
    let mut index = 0;

    while index < old_stmts.len() {
        if let Some((call, declaration)) =
            old_stmts.get(index).zip(old_stmts.get(index + 1)).and_then(
                |(declaration, overwrite)| split_overwritten_call_result(declaration, overwrite),
            )
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
) -> Option<(AstCallKind, AstLocalDecl)> {
    let AstStmt::LocalDecl(local_decl) = declaration else {
        return None;
    };
    let AstStmt::Assign(assign) = overwrite else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [call_value] = local_decl.values.as_slice() else {
        return None;
    };
    if binding.attr != AstLocalAttr::None || binding.origin != AstLocalOrigin::Recovered {
        return None;
    }
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [replacement] = assign.values.as_slice() else {
        return None;
    };
    if !matches!(target, super::super::common::AstLValue::Name(name) if binding.id.matches_name_ref(name))
        || binding_mentions_in_expr(call_value).contains(&binding.id)
        || binding_mentions_in_expr(replacement).contains(&binding.id)
    {
        return None;
    }

    let call = into_call_kind(call_value.clone()).ok()?;

    Some((
        call,
        AstLocalDecl {
            bindings: local_decl.bindings.clone(),
            values: vec![replacement.clone()],
        },
    ))
}

fn trailing_do_block_is_scope_neutral(block: &AstBlock) -> bool {
    !block.stmts.iter().any(|stmt| match stmt {
        AstStmt::GlobalDecl(_) => true,
        AstStmt::LocalDecl(local_decl) => {
            local_decl
                .bindings
                .iter()
                .any(|binding| binding.attr == AstLocalAttr::Close)
                || local_decl
                    .values
                    .iter()
                    .any(|value| matches!(value, AstExpr::FunctionExpr(_)))
        }
        AstStmt::LocalFunctionDecl(_) => true,
        _ => false,
    })
}

fn can_elide_single_stmt_do_block(stmt: &AstStmt) -> bool {
    matches!(
        stmt,
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
    )
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

fn collect_live_mechanical_bindings(
    block: &AstBlock,
    binding_flow: &BlockBindingFlow,
) -> BTreeSet<AstBindingRef> {
    let mut live_bindings = BTreeSet::new();
    for stmt in &block.stmts {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            continue;
        };
        for binding in &local_decl.bindings {
            if matches!(
                binding.id,
                AstBindingRef::Temp(_) | AstBindingRef::SyntheticLocal(_)
            ) && binding_flow.keeps_decl_alive(binding.id)
            {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::common::{
        AstAssign, AstCallExpr, AstGlobalName, AstLValue, AstLocalBinding, AstNameRef,
    };
    use crate::hir::LocalId;

    fn recovered_binding() -> AstLocalBinding {
        AstLocalBinding {
            id: AstBindingRef::Local(LocalId(0)),
            attr: AstLocalAttr::None,
            origin: AstLocalOrigin::Recovered,
        }
    }

    fn call_value() -> AstExpr {
        AstExpr::Call(Box::new(AstCallExpr {
            callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                text: "factory".to_owned(),
            })),
            args: vec![],
            method_name: None,
        }))
    }

    #[test]
    fn splits_recovered_call_result_before_direct_overwrite() {
        let binding = recovered_binding();
        let declaration = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![binding.clone()],
            values: vec![call_value()],
        }));
        let overwrite = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(binding.id.to_name_ref())],
            values: vec![AstExpr::Integer(9)],
        }));

        let (call, rewritten) = split_overwritten_call_result(&declaration, &overwrite)
            .expect("a recovered call result with a direct overwrite is safe to split");
        assert!(matches!(call, AstCallKind::Call(_)));
        assert_eq!(rewritten.bindings, vec![binding]);
        assert_eq!(rewritten.values, vec![AstExpr::Integer(9)]);
    }

    #[test]
    fn keeps_debug_and_self_referencing_call_results() {
        let mut debug_binding = recovered_binding();
        debug_binding.origin = AstLocalOrigin::DebugHinted;
        let debug_decl = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![debug_binding.clone()],
            values: vec![call_value()],
        }));
        let debug_write = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(debug_binding.id.to_name_ref())],
            values: vec![AstExpr::Integer(9)],
        }));
        assert!(split_overwritten_call_result(&debug_decl, &debug_write).is_none());

        let binding = recovered_binding();
        let self_call = AstExpr::Call(Box::new(AstCallExpr {
            callee: AstExpr::Var(binding.id.to_name_ref()),
            args: vec![],
            method_name: None,
        }));
        let declaration = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![binding.clone()],
            values: vec![self_call],
        }));
        let overwrite = AstStmt::Assign(Box::new(AstAssign {
            targets: vec![AstLValue::Name(binding.id.to_name_ref())],
            values: vec![AstExpr::Integer(9)],
        }));
        assert!(split_overwritten_call_result(&declaration, &overwrite).is_none());
    }
}
