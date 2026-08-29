//! 这个子模块负责把一串 seed local 运行合并成更自然的 global decl 形状。
//!
//! 它依赖 binding-flow/binding-tree 已确认这些 local 只是过渡壳，不会越权去推断缺失的
//! global 名称来源。接受候选必须是同序精确双射，且只删除无 provenance/lifetime 约束的
//! Recovered seed。
//! 例如：连续的 `local g = _ENV.g` seed 运行，会在这里尝试折成一条更紧凑的 global 声明。

use super::super::binding_flow::BindingUseIndex;
use super::super::binding_ref::binding_from_name_ref;
use crate::ast::common::{
    AstBindingRef, AstBlock, AstExpr, AstGlobalBinding, AstGlobalDecl, AstLocalAttr,
    AstLocalBinding, AstLocalOrigin, AstStmt,
};

pub(super) fn merge_seed_global_runs(block: &mut AstBlock) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let use_index = BindingUseIndex::for_stmts(&old_stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut index = 0usize;
    let mut changed = false;

    while index < old_stmts.len() {
        if let Some((stmt, consumed)) = try_merge_seed_global_run(&old_stmts, &use_index, index) {
            new_stmts.push(stmt);
            index += consumed;
            changed = true;
            continue;
        }
        new_stmts.push(old_stmts[index].clone());
        index += 1;
    }

    block.stmts = new_stmts;
    changed
}

fn try_merge_seed_global_run(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    start: usize,
) -> Option<(AstStmt, usize)> {
    let mut seeds = Vec::<(AstLocalBinding, AstExpr)>::new();
    let mut index = start;
    while let Some(stmt) = stmts.get(index) {
        let AstStmt::LocalDecl(local_decl) = stmt else {
            break;
        };
        if local_decl.bindings.len() != 1
            || local_decl.values.len() != 1
            || local_decl.bindings[0].attr != AstLocalAttr::None
        {
            break;
        }
        seeds.push((local_decl.bindings[0].clone(), local_decl.values[0].clone()));
        index += 1;
    }
    if seeds.is_empty() {
        return None;
    }

    let mut globals = Vec::<(AstBindingRef, AstGlobalBinding)>::new();
    let mut attr = None;
    while let Some(stmt) = stmts.get(index) {
        let AstStmt::GlobalDecl(global_decl) = stmt else {
            break;
        };
        if global_decl.bindings.len() != 1 || global_decl.values.len() != 1 {
            break;
        }
        let AstExpr::Var(name) = &global_decl.values[0] else {
            break;
        };
        let Some(binding) = binding_from_name_ref(name) else {
            break;
        };
        let current_attr = global_decl.bindings[0].attr;
        if attr.is_none() {
            attr = Some(current_attr);
        }
        if attr != Some(current_attr) {
            break;
        }
        globals.push((binding, global_decl.bindings[0].clone()));
        index += 1;
    }
    if globals.is_empty() {
        return None;
    }

    if seeds.len() != globals.len() {
        // 候选拒绝[SemanticBarrier:Identity]：seed/global 不是精确双射时，合并会删除未交接 seed 的 initializer，或丢掉没有来源的 global 写入；regress335 的 captured_seed 会因此失去闭包 owner。
        return None;
    }

    let mut merged_bindings = Vec::with_capacity(globals.len());
    let mut merged_values = Vec::with_capacity(globals.len());
    for ((seed, value), (global_source, global_binding)) in seeds.iter().zip(&globals) {
        if seed.id != *global_source {
            // 候选拒绝[SemanticBarrier:EvalOrder]：seed 与 global handoff 次序不一致时，合成多声明会把 initializer/global 写入重排；regress335 通过 `_ENV.__newindex` 区分 `y,x` 与 `x,y`。
            return None;
        }
        match seed.origin {
            AstLocalOrigin::Recovered => {}
            AstLocalOrigin::DebugHinted => {
                // 候选拒绝[PolicyBoundary]：DebugHinted seed 是显式源码 local 身份；regress335 通过 debug.getlocal 观察该名字，声明合并不得抹掉它。
                return None;
            }
            AstLocalOrigin::PhysicalRoot => {
                // 候选拒绝[SemanticBarrier:Lifetime]：global 随后被覆盖时，PhysicalRoot seed 仍须把旧值保活到原 block 末端；regress335 用弱表/GC 观察提前消失。
                return None;
            }
        }
        if use_index.count_uses_in_suffix(start, seed.id) != 1 {
            // 候选拒绝[SemanticBarrier:Capture]：唯一允许的 seed use 是对应 global handoff；initializer capture 或 run 后 use 都依赖被删 local，regress335 的闭包 seed 会变成未绑定引用。
            return None;
        }
        merged_bindings.push(global_binding.clone());
        merged_values.push(value.clone());
    }

    if merged_bindings.len() > 1 {
        // 候选拒绝[SemanticBarrier:EvalOrder]：Lua 5.5 的多目标 global 声明按目标
        // 逆序写入；合并顺序 singleton handoff 会反转 `_ENV.__newindex` 可观察顺序。
        return None;
    }

    Some((
        AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
            bindings: merged_bindings,
            values: merged_values,
        })),
        index - start,
    ))
}
