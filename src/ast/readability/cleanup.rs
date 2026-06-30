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
//! - 函数尾部的 `return` 会在没有返回值时被去掉

use std::collections::{BTreeMap, BTreeSet};

use super::super::common::{AstBindingRef, AstBlock, AstModule, AstStmt};
use super::ReadabilityContext;
use super::binding_flow::{BindingUseIndex, binding_mentions_in_stmt};
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
        )
    }
}

fn cleanup_block(block: &mut AstBlock, allow_trailing_empty_return_elision: bool) -> bool {
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
                flattened_stmts.push(nested.stmts[0].clone());
                changed = true;
            }
            other => flattened_stmts.push(other),
        }
    }
    block.stmts = flattened_stmts;

    // 尾部 do-end 展开：当 do-end 是块的最后一条语句时，其内部 local 的作用域
    // 在父块结束处同样终止，do-end 仅是多余的缩进壳。
    // 典型来源：guard-flip 把 `if cond then BODY else return end` 拉平成
    // `if not cond then return end; do BODY end`，其中 BODY 含 local 声明。
    // 例外：含 GlobalDecl（如 `global<const> *`）的 do-end 有实际作用域语义，保留。
    while let Some(AstStmt::DoBlock(nested)) = block.stmts.last()
        && !nested
            .stmts
            .iter()
            .any(|s| matches!(s, AstStmt::GlobalDecl(_)))
    {
        let Some(AstStmt::DoBlock(nested)) = block.stmts.pop() else {
            unreachable!();
        };
        block.stmts.extend(nested.stmts);
        changed = true;
    }

    let binding_flow = BlockBindingFlow::new(block);
    let discardable_unused_locals = collect_discardable_unused_locals(block, &binding_flow);
    let original_len = block.stmts.len();
    block.stmts.retain(|stmt| {
        !matches!(
            stmt,
            AstStmt::LocalDecl(local_decl)
                if local_decl.bindings.len() == 1
                    && local_decl.values.len() == 1
                    && discardable_unused_locals.contains(&local_decl.bindings[0].id)
        )
    });
    changed |= block.stmts.len() != original_len;

    let binding_flow = BlockBindingFlow::new(block);
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
    fn new(block: &AstBlock) -> Self {
        let mut mention_counts = BTreeMap::<AstBindingRef, usize>::new();
        for stmt in &block.stmts {
            for binding in binding_mentions_in_stmt(stmt) {
                *mention_counts.entry(binding).or_default() += 1;
            }
        }
        Self {
            mention_counts,
            use_index: BindingUseIndex::for_stmts(&block.stmts),
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

fn collect_discardable_unused_locals(
    block: &AstBlock,
    binding_flow: &BlockBindingFlow,
) -> std::collections::BTreeSet<AstBindingRef> {
    let mut bindings = std::collections::BTreeSet::new();
    for stmt in &block.stmts {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            continue;
        };
        let [binding] = local_decl.bindings.as_slice() else {
            continue;
        };
        let [value] = local_decl.values.as_slice() else {
            continue;
        };
        if !matches!(binding.origin, crate::ast::AstLocalOrigin::Recovered) {
            continue;
        }
        if binding_flow.keeps_decl_alive(binding.id) {
            continue;
        }
        if is_discard_safe_expr(value) {
            bindings.insert(binding.id);
        }
    }
    bindings
}
