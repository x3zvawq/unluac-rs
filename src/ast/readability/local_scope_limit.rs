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

    fn scope_for_stmt_children(
        &mut self,
        stmt: &AstStmt,
        outer_locals: &Self::Scope,
    ) -> Self::Scope {
        // for 控制变量只在 loop body 内可见；控制表达式里即使出现嵌套函数，
        // enter_function 也会重置预算，因此统一给 statement children 加上它们是精确的。
        match stmt {
            AstStmt::NumericFor(_) => outer_locals.saturating_add(1),
            AstStmt::GenericFor(generic_for) => {
                outer_locals.saturating_add(generic_for.bindings.len())
            }
            _ => *outer_locals,
        }
    }

    fn scope_after_stmt(&mut self, stmt: &AstStmt, outer_locals: &Self::Scope) -> Self::Scope {
        // Lua local 从声明语句结束后才进入当前 block 的后续词法作用域。
        outer_locals.saturating_add(direct_local_count(stmt))
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
    // 当前 block 的声明不能在入口一次性加入：它们只应通过 scope_after_stmt
    // 按源码位置影响后续 sibling 及其子 block。
    (changed, outer_locals)
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
    if direct_local_pressure(&block.stmts) <= available_locals {
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
                        let last = last_mentions
                            .get(&binding)
                            .copied()
                            .expect("scopeable declaration must mention its binding");
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
        // 候选拒绝[ProofIncomplete]：block 峰值已超 local 预算但当前连续区间算法找不到安全范围；需报告不可缩减的 persistent 集合并由前层压缩身份。
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

fn direct_local_pressure(stmts: &[AstStmt]) -> usize {
    let mut active = 0usize;
    let mut peak = 0usize;
    for stmt in stmts {
        let loop_bindings = match stmt {
            AstStmt::NumericFor(_) => 1,
            AstStmt::GenericFor(generic_for) => generic_for.bindings.len(),
            _ => 0,
        };
        peak = peak.max(active.saturating_add(loop_bindings));
        active = active.saturating_add(direct_local_count(stmt));
        peak = peak.max(active);
    }
    peak
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
            .map(|binding| {
                last_mentions
                    .get(&binding)
                    .copied()
                    .expect("scopeable declaration must mention its binding")
            })
            .max()
            .expect("scopeable declaration must contain a binding");
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
                        .map(|binding| {
                            last_mentions
                                .get(&binding)
                                .copied()
                                .expect("scopeable declaration must mention its binding")
                        })
                        .max()
                        .expect("scopeable declaration must contain a binding"),
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
    if matches!(stmt, AstStmt::Goto(_) | AstStmt::Label(_)) {
        // 候选拒绝[ProofIncomplete]：区间规划尚未携带 goto/label 的相对 owner 与入边；只有外部跳入新 `do` 的形状是 Scope 反例，同区间或跳出形状仍待精确放行。
        return true;
    }
    // 属性/debug/root 声明的具体拒绝理由由 scopeable_bindings 在同一候选点分类。
    direct_local_count(stmt) != 0 && scopeable_bindings(stmt).is_none()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::common::{AstGenericFor, AstLocalDecl};
    use crate::hir::LocalId;

    fn recovered_local(index: usize) -> AstStmt {
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: AstBindingRef::Local(LocalId(index)),
                attr: AstLocalAttr::None,
                origin: AstLocalOrigin::Recovered,
            }],
            values: vec![AstExpr::Integer(index as i64)],
        }))
    }

    #[test]
    fn scopes_preceding_locals_before_generic_for_binder_peak() {
        let mut block = AstBlock {
            stmts: (0..crate::SOURCE_LOCAL_LIMIT - 1)
                .map(recovered_local)
                .chain(std::iter::once(AstStmt::GenericFor(Box::new(
                    AstGenericFor {
                        bindings: vec![
                            AstBindingRef::Local(LocalId(1_000)),
                            AstBindingRef::Local(LocalId(1_001)),
                        ],
                        iterator: vec![AstExpr::Nil],
                        body: AstBlock::default(),
                    },
                ))))
                .collect(),
        };

        assert!(scope_locals(&mut block, crate::SOURCE_LOCAL_LIMIT, None));
        assert!(matches!(block.stmts.first(), Some(AstStmt::DoBlock(_))));
    }
}
