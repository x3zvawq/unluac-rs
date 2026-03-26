//! 这个文件负责把候选名字落成最终 NameMap。
//!
//! strategy 只负责给出“像什么”，这里才负责：
//! - 模块级 function-shape 去重
//! - 函数内冲突消解
//! - 参数对外层当前可见绑定的避让

use std::collections::BTreeSet;

use crate::hir::HirProto;

use super::NamingError;
use super::common::{
    CandidateHint, FunctionHints, FunctionNameMap, FunctionNamingEvidence, ModuleNameAllocator,
    NameInfo, NameSource, NamingMode, NamingOptions,
};
use super::lexical::FunctionLexicalContext;
use super::strategy::{
    choose_local_candidate, choose_param_candidate, choose_synthetic_local_candidate,
    choose_upvalue_candidate, resolve_outer_visible_names,
};
use super::support::{alphabetical_name, is_lua_keyword, lua_keywords};

impl ModuleNameAllocator {
    pub(super) fn reserve_function_shape_name(
        &mut self,
        candidate: CandidateHint,
        used_in_function: &BTreeSet<String>,
        mode: NamingMode,
    ) -> CandidateHint {
        if mode == NamingMode::DebugLike || candidate.source != NameSource::FunctionShape {
            return candidate;
        }

        // `fn` 这类函数形状名如果每个函数都从头开始，会在阅读时迅速失去区分度。
        // 这里单独做模块级递增，只影响函数形状名，不去污染其它局部命名规则。
        let base = candidate.text;
        let mut next_suffix = self
            .next_function_shape_suffix
            .get(&base)
            .copied()
            .unwrap_or(1);

        loop {
            let text = if next_suffix == 1 {
                base.clone()
            } else {
                format!("{base}{next_suffix}")
            };
            if !self.function_shape_names.contains(&text)
                && !used_in_function.contains(&text)
                && !is_lua_keyword(&text)
            {
                self.function_shape_names.insert(text.clone());
                self.next_function_shape_suffix
                    .insert(base, next_suffix.saturating_add(1));
                return CandidateHint {
                    text,
                    source: candidate.source,
                };
            }
            next_suffix = next_suffix.saturating_add(1);
        }
    }
}

/// 为单个函数分配最终名字。
pub(super) fn assign_names_for_function(
    proto: &HirProto,
    evidence: &FunctionNamingEvidence,
    hints: &FunctionHints,
    options: NamingOptions,
    lexical: &FunctionLexicalContext,
    assigned_functions: &[FunctionNameMap],
    module_names: &mut ModuleNameAllocator,
) -> Result<FunctionNameMap, NamingError> {
    let mut used = lua_keywords();
    let outer_visible_names = resolve_outer_visible_names(proto.id, lexical, assigned_functions)?;

    let params = proto
        .params
        .iter()
        .enumerate()
        .map(|(index, param)| {
            allocate_param_name(
                module_names.reserve_function_shape_name(
                    choose_param_candidate(proto, *param, index, evidence, hints, options),
                    &used,
                    options.mode,
                ),
                index,
                options,
                &mut used,
                &outer_visible_names,
            )
        })
        .collect::<Vec<_>>();

    let locals = proto
        .locals
        .iter()
        .enumerate()
        .map(|(index, local)| {
            allocate_name(
                module_names.reserve_function_shape_name(
                    choose_local_candidate(proto, *local, index, evidence, hints, options),
                    &used,
                    options.mode,
                ),
                &mut used,
            )
        })
        .collect::<Vec<_>>();

    let mut upvalues = Vec::with_capacity(proto.upvalues.len());
    for (index, _upvalue) in proto.upvalues.iter().enumerate() {
        let candidate =
            choose_upvalue_candidate(proto, index, evidence, options, assigned_functions)?;
        upvalues.push(allocate_name(
            module_names.reserve_function_shape_name(candidate, &used, options.mode),
            &mut used,
        ));
    }

    let synthetic_locals = hints
        .synthetic_locals
        .iter()
        .copied()
        .enumerate()
        .map(|(synthetic_order, local)| {
            let info = allocate_name(
                module_names.reserve_function_shape_name(
                    choose_synthetic_local_candidate(
                        proto,
                        local,
                        synthetic_order,
                        evidence,
                        hints,
                        options,
                    ),
                    &used,
                    options.mode,
                ),
                &mut used,
            );
            (local, info)
        })
        .collect();

    Ok(FunctionNameMap {
        params,
        locals,
        synthetic_locals,
        upvalues,
    })
}

fn allocate_param_name(
    candidate: CandidateHint,
    index: usize,
    options: NamingOptions,
    used: &mut BTreeSet<String>,
    outer_visible_names: &BTreeSet<String>,
) -> NameInfo {
    if options.mode == NamingMode::DebugLike || candidate.source != NameSource::Simple {
        return allocate_name(candidate, used);
    }
    if !outer_visible_names.contains(&candidate.text) {
        return allocate_name(candidate, used);
    }

    let replacement = next_available_simple_param_name(index, used, outer_visible_names);
    allocate_name(
        CandidateHint {
            text: replacement,
            source: candidate.source,
        },
        used,
    )
}

fn next_available_simple_param_name(
    mut index: usize,
    used: &BTreeSet<String>,
    outer_visible_names: &BTreeSet<String>,
) -> String {
    loop {
        let candidate = alphabetical_name(index).unwrap_or_else(|| format!("arg{}", index + 1));
        if !used.contains(&candidate)
            && !outer_visible_names.contains(&candidate)
            && !is_lua_keyword(&candidate)
        {
            return candidate;
        }
        index = index.saturating_add(1);
    }
}

fn allocate_name(candidate: CandidateHint, used: &mut BTreeSet<String>) -> NameInfo {
    let base = candidate.text;
    if !used.contains(&base) && !is_lua_keyword(&base) {
        used.insert(base.clone());
        return NameInfo {
            text: base,
            source: candidate.source,
            renamed: false,
        };
    }

    let mut suffix = 2usize;
    loop {
        let renamed = format!("{base}{suffix}");
        if !used.contains(&renamed) && !is_lua_keyword(&renamed) {
            used.insert(renamed.clone());
            return NameInfo {
                text: renamed,
                source: candidate.source,
                renamed: true,
            };
        }
        suffix = suffix.saturating_add(1);
    }
}
