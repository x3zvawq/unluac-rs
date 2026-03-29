//! 这个子模块负责把一串 seed local 运行合并成更自然的 global decl 形状。
//!
//! 它依赖 binding-flow/binding-tree 已确认这些 local 只是过渡壳，不会越权去推断缺失的
//! global 名称来源。
//! 例如：连续的 `local g = _ENV.g` seed 运行，会在这里尝试折成一条更紧凑的 global 声明。

use std::collections::BTreeSet;

use super::super::binding_flow::count_binding_uses_in_stmts;
use super::super::binding_tree::binding_from_name_ref;
use crate::ast::common::{
    AstBindingRef, AstBlock, AstExpr, AstGlobalBinding, AstGlobalDecl, AstLocalAttr, AstStmt,
};

pub(super) fn merge_seed_global_runs(block: &mut AstBlock) -> bool {
    let old_stmts = std::mem::take(&mut block.stmts);
    let mut new_stmts = Vec::with_capacity(old_stmts.len());
    let mut index = 0usize;
    let mut changed = false;

    while index < old_stmts.len() {
        if let Some((stmt, consumed)) = try_merge_seed_global_run(&old_stmts, index) {
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

fn try_merge_seed_global_run(stmts: &[AstStmt], start: usize) -> Option<(AstStmt, usize)> {
    let mut seeds = Vec::<(AstBindingRef, AstExpr)>::new();
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
        seeds.push((local_decl.bindings[0].id, local_decl.values[0].clone()));
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

    let after_run = &stmts[index..];
    let mut merged_bindings = Vec::new();
    let mut merged_values = Vec::new();
    let mut matched = BTreeSet::new();
    for (binding, value) in &seeds {
        if count_binding_uses_in_stmts(after_run, *binding) != 0 {
            return None;
        }
        let Some((_, global_binding)) = globals.iter().find(|(candidate, _)| candidate == binding)
        else {
            continue;
        };
        if !matched.insert(*binding) {
            return None;
        }
        merged_bindings.push(global_binding.clone());
        merged_values.push(value.clone());
    }
    if merged_bindings.len() != globals.len() {
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
