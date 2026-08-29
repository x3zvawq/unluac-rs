//! 为超大函数里的短生命周期 local 补充有限词法作用域。
//!
//! 本 pass 依赖 Deferred 阶段已经稳定的语句相邻关系和 binding mention，不补 HIR 事实，
//! 也不为减少 local 做可能改变调用、global lookup 或比较顺序的跨语句内联。它沿词法树
//! 携带外层 local 预算，把短生命周期、无属性的声明分批放入 `do ... end`；带属性 local
//! 与 label/goto 边界保持原状。例如同一函数内 240 个顺序临时声明会变成若干个最多 64
//! 个 local 的 `do` 块，而闭包捕获或后续仍读取的 binding 会把作用域延长到最后 mention。
//! repeat body 中被 until 条件读取的 local 必须留在正文直属作用域，不能包进 `do`。

use std::collections::BTreeMap;

use super::super::common::{
    AstBindingRef, AstBlock, AstExpr, AstFunctionExpr, AstLocalAttr, AstLocalBinding,
    AstLocalOrigin, AstModule, AstStmt,
};
use super::binding_flow::{binding_mentions_in_expr, binding_mentions_in_stmt};
use super::{ReadabilityContext, walk};
use walk::{BlockKind, ScopedAstRewritePass};

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
        enter_block_with_trailing_condition(block, None, *outer_locals)
    }

    fn enter_repeat_body(
        &mut self,
        block: &mut AstBlock,
        condition: &AstExpr,
        outer_locals: &Self::Scope,
    ) -> (bool, Self::Scope) {
        enter_block_with_trailing_condition(block, Some(condition), *outer_locals)
    }
}

fn enter_block_with_trailing_condition(
    block: &mut AstBlock,
    trailing_condition: Option<&AstExpr>,
    outer_locals: usize,
) -> (bool, usize) {
    let changed = scope_locals(
        block,
        crate::SOURCE_LOCAL_LIMIT.saturating_sub(outer_locals),
        trailing_condition,
    );
    let direct_locals = block.stmts.iter().map(direct_local_count).sum::<usize>();
    (changed, outer_locals.saturating_add(direct_locals))
}

fn scope_locals(
    block: &mut AstBlock,
    available_locals: usize,
    trailing_condition: Option<&AstExpr>,
) -> bool {
    let direct_local_count = block.stmts.iter().map(direct_local_count).sum::<usize>();
    if available_locals == 0 {
        // 分析停用[LayerBoundary]：外层/参数已耗尽全部源码 local 预算时，内层 `do` 不能降低同时活跃的外层数量；需由 HIR home compaction 减少 persistent locals。
        return false;
    }
    if direct_local_count <= available_locals {
        return false;
    }

    let last_mentions = last_binding_mentions(&block.stmts);
    let trailing_mentions = trailing_condition
        .map(binding_mentions_in_expr)
        .unwrap_or_default();
    let scopeable_prefix = scopeable_local_prefix(&block.stmts);
    let lifetime_limit = SCOPE_LOCAL_TARGET.min(available_locals.max(1));
    let short_lived = block
        .stmts
        .iter()
        .enumerate()
        .map(|(index, stmt)| {
            scopeable_bindings(stmt).is_some_and(|bindings| {
                bindings.ids().all(|binding| {
                    // 候选拒绝[SemanticBarrier:Scope]：repeat 的 `until binding` 在 body 直属作用域读取，包进内层 `do` 会使条件失去该 local。
                    !trailing_mentions.contains(&binding) && {
                        let last = last_mentions.get(&binding).copied().unwrap_or(index);
                        // 候选拒绝[ProofIncomplete]：生命周期跨过超过 64 个 scopeable local 的 binding 暂不分组；需按区间图/峰值活跃数规划重叠作用域，而非固定窗口。
                        scopeable_prefix[last + 1] - scopeable_prefix[index] <= lifetime_limit
                    }
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
        // 候选拒绝[ProofIncomplete]：函数已超 local 预算但当前连续区间算法找不到安全范围；需报告不可缩减的 persistent 集合并由前层压缩身份。
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
                && decl.bindings.iter().all(|binding| {
                    binding.attr == AstLocalAttr::None
                        && binding.origin == AstLocalOrigin::Recovered
                }) =>
        {
            Some(ScopeableBindings {
                locals: &decl.bindings,
                local_function: None,
            })
        }
        AstStmt::LocalFunctionDecl(decl) if decl.origin == AstLocalOrigin::Recovered => {
            Some(ScopeableBindings {
                locals: &[],
                local_function: Some(decl.name),
            })
        }
        AstStmt::LocalDecl(_) | AstStmt::LocalFunctionDecl(_) => {
            // 候选拒绝[SemanticBarrier:Lifetime]：PhysicalRoot 与 `<close>` 若提前离开原 block，会改变 GC root/关闭时点。
            // 候选拒绝[SemanticBarrier:DebugScope]：DebugHinted local 的原词法可见期可被 debug API 观察。
            // 候选拒绝[PolicyBoundary]：`<const>` 声明身份不由 local-budget pass 重排。
            None
        }
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
                    // 候选拒绝[ProofIncomplete]：当前区间只容纳全部 short-lived 的连续声明；遇到长生命周期声明即停止，缺少交错区间分配证明。
                    break;
                }
                if scoped_locals + bindings.len() > scope_target && safe_end.is_some() {
                    // 候选拒绝[PolicyBoundary]：单个生成作用域最多承载 64 个 local，控制缩进块密度并为外层活跃 binding 留余量。
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
            // 候选拒绝[ProofIncomplete]：候选起点到 barrier/扫描终点前没有同时闭合且不超预算的安全区间；需更精确的活跃区间切分。
            index = start + 1;
        }
    }
    ranges
}

fn is_scope_barrier(stmt: &AstStmt) -> bool {
    // 候选拒绝[SemanticBarrier:Scope]：新增 `do` 若跨 label/goto 会改变 label 可见性或制造跳入 local 作用域；候选拒绝[SemanticBarrier:Lifetime]：也不能跨 `<close>` 资源边界。
    matches!(stmt, AstStmt::Goto(_) | AstStmt::Label(_))
        || (direct_local_count(stmt) != 0 && scopeable_bindings(stmt).is_none())
}
