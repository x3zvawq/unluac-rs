//! 为超大函数里的短生命周期 local 补充有限词法作用域。
//!
//! 本 pass 依赖 Deferred 阶段已经稳定的语句相邻关系和 binding mention，不补 HIR 事实，
//! 也不为减少 local 做可能改变调用、global lookup 或比较顺序的跨语句内联。它沿词法树
//! 携带外层 local 预算，把短生命周期、无属性的声明分批放入 `do ... end`；带属性 local
//! 与 label/goto 边界保持原状。例如同一函数内 240 个顺序临时声明会变成若干个最多 64
//! 个 local 的 `do` 块，而闭包捕获或后续仍读取的 binding 会把作用域延长到最后 mention。

use std::collections::BTreeMap;

use super::super::common::{
    AstBindingRef, AstBlock, AstFunctionExpr, AstLocalAttr, AstLocalBinding, AstModule, AstStmt,
};
use super::binding_flow::binding_mentions_in_stmt;
use super::{ReadabilityContext, walk};
use walk::{BlockKind, ScopedAstRewritePass};

const DIRECT_LOCAL_LIMIT: usize = 180;
const SCOPE_LOCAL_TARGET: usize = 64;

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    walk::rewrite_module_scoped(module, &0, &mut LocalScopeLimitPass)
}

struct LocalScopeLimitPass;

impl ScopedAstRewritePass for LocalScopeLimitPass {
    type Scope = usize;

    fn enter_function(
        &mut self,
        function: &mut AstFunctionExpr,
        _outer_scope: &Self::Scope,
    ) -> Self::Scope {
        function.params.len() + usize::from(function.named_vararg.is_some())
    }

    fn enter_block(
        &mut self,
        block: &mut AstBlock,
        _kind: BlockKind,
        outer_locals: &Self::Scope,
    ) -> (bool, Self::Scope) {
        let changed = scope_locals(block, DIRECT_LOCAL_LIMIT.saturating_sub(*outer_locals));
        let direct_locals = block.stmts.iter().map(direct_local_count).sum::<usize>();
        (changed, outer_locals.saturating_add(direct_locals))
    }
}

fn scope_locals(block: &mut AstBlock, available_locals: usize) -> bool {
    let direct_local_count = block.stmts.iter().map(direct_local_count).sum::<usize>();
    if direct_local_count <= available_locals {
        return false;
    }

    let last_mentions = last_binding_mentions(&block.stmts);
    let scopeable_prefix = scopeable_local_prefix(&block.stmts);
    let lifetime_limit = SCOPE_LOCAL_TARGET.min(available_locals.max(1));
    let short_lived = block
        .stmts
        .iter()
        .enumerate()
        .map(|(index, stmt)| {
            scopeable_bindings(stmt).is_some_and(|bindings| {
                bindings.ids().all(|binding| {
                    let last = last_mentions.get(&binding).copied().unwrap_or(index);
                    scopeable_prefix[last + 1] - scopeable_prefix[index] <= lifetime_limit
                })
            })
        })
        .collect::<Vec<_>>();
    let persistent_locals = direct_local_count
        - block
            .stmts
            .iter()
            .enumerate()
            .filter(|(index, _)| short_lived[*index])
            .map(|(_, stmt)| scopeable_bindings(stmt).map_or(0, ScopeableBindings::len))
            .sum::<usize>();
    let scope_target =
        SCOPE_LOCAL_TARGET.min(available_locals.saturating_sub(persistent_locals).max(1));
    let ranges = scope_ranges(&block.stmts, &last_mentions, &short_lived, scope_target);
    if ranges.is_empty() {
        return false;
    }

    let old_stmts = std::mem::take(&mut block.stmts);
    let mut old_stmts = old_stmts.into_iter();
    let mut scoped_stmts = Vec::with_capacity(direct_local_count + ranges.len());
    let mut cursor = 0usize;
    for (start, end) in ranges {
        scoped_stmts.extend(old_stmts.by_ref().take(start - cursor));
        let stmts = old_stmts.by_ref().take(end - start).collect();
        scoped_stmts.push(AstStmt::DoBlock(Box::new(AstBlock { stmts })));
        cursor = end;
    }
    scoped_stmts.extend(old_stmts);
    block.stmts = scoped_stmts;
    true
}

fn direct_local_count(stmt: &AstStmt) -> usize {
    match stmt {
        AstStmt::LocalDecl(decl) => decl.bindings.len(),
        AstStmt::LocalFunctionDecl(_) => 1,
        _ => 0,
    }
}

#[derive(Clone, Copy)]
struct ScopeableBindings<'a> {
    locals: &'a [AstLocalBinding],
    local_function: Option<AstBindingRef>,
}

impl<'a> ScopeableBindings<'a> {
    fn ids(self) -> impl Iterator<Item = AstBindingRef> + 'a {
        self.locals
            .iter()
            .map(|binding| binding.id)
            .chain(self.local_function)
    }

    fn len(self) -> usize {
        self.locals.len() + usize::from(self.local_function.is_some())
    }
}

fn scopeable_bindings(stmt: &AstStmt) -> Option<ScopeableBindings<'_>> {
    match stmt {
        AstStmt::LocalDecl(decl)
            if !decl.bindings.is_empty()
                && decl
                    .bindings
                    .iter()
                    .all(|binding| binding.attr == AstLocalAttr::None) =>
        {
            Some(ScopeableBindings {
                locals: &decl.bindings,
                local_function: None,
            })
        }
        AstStmt::LocalFunctionDecl(decl) => Some(ScopeableBindings {
            locals: &[],
            local_function: Some(decl.name),
        }),
        _ => None,
    }
}

fn last_binding_mentions(stmts: &[AstStmt]) -> BTreeMap<AstBindingRef, usize> {
    let mut last_mentions = BTreeMap::new();
    for (index, stmt) in stmts.iter().enumerate() {
        for binding in binding_mentions_in_stmt(stmt) {
            last_mentions.insert(binding, index);
        }
    }
    last_mentions
}

fn scopeable_local_prefix(stmts: &[AstStmt]) -> Vec<usize> {
    let mut prefix = Vec::with_capacity(stmts.len() + 1);
    prefix.push(0);
    for stmt in stmts {
        prefix.push(
            prefix.last().copied().unwrap_or_default()
                + scopeable_bindings(stmt).map_or(0, ScopeableBindings::len),
        );
    }
    prefix
}

fn scope_ranges(
    stmts: &[AstStmt],
    last_mentions: &BTreeMap<AstBindingRef, usize>,
    short_lived: &[bool],
    scope_target: usize,
) -> Vec<(usize, usize)> {
    let mut ranges = Vec::new();
    let mut index = 0usize;
    while index < stmts.len() {
        let Some(bindings) = scopeable_bindings(&stmts[index]).filter(|_| short_lived[index])
        else {
            index += 1;
            continue;
        };

        let start = index;
        let mut required_end = bindings
            .ids()
            .filter_map(|binding| last_mentions.get(&binding).copied())
            .max()
            .unwrap_or(index);
        let mut scoped_locals = 0usize;
        let mut safe_end = None;
        while index < stmts.len() && !is_scope_barrier(&stmts[index]) {
            if let Some(bindings) = scopeable_bindings(&stmts[index]) {
                if !short_lived[index] {
                    break;
                }
                if scoped_locals + bindings.len() > scope_target && safe_end.is_some() {
                    break;
                }
                scoped_locals += bindings.len();
                required_end = required_end.max(
                    bindings
                        .ids()
                        .filter_map(|binding| last_mentions.get(&binding).copied())
                        .max()
                        .unwrap_or(index),
                );
            }
            if index >= required_end {
                safe_end = Some((index + 1, scoped_locals));
                if scoped_locals >= scope_target {
                    break;
                }
            }
            index += 1;
        }

        if let Some((end, safe_local_count)) = safe_end
            && safe_local_count <= scope_target
        {
            ranges.push((start, end));
            index = end;
        } else {
            index = start + 1;
        }
    }
    ranges
}

fn is_scope_barrier(stmt: &AstStmt) -> bool {
    matches!(stmt, AstStmt::Goto(_) | AstStmt::Label(_))
        || (direct_local_count(stmt) != 0 && scopeable_bindings(stmt).is_none())
}
