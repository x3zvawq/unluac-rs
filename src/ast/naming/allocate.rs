//! 这个文件负责把候选名字落成最终 NameMap。
//!
//! strategy 只负责给出“像什么”，这里才负责：
//! - 模块级 function-shape 去重
//! - 函数内冲突消解
//! - 参数对外层当前可见绑定的避让

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::ast::{AstProtoMeta, LocalId, ProtoId};
use crate::decompile::DecompileDialect;

use super::NamingError;
use super::ast_facts::{AstNamingFacts, FunctionAstNamingFacts};
use super::common::{
    CandidateHint, ClosureCaptureEvidence, FunctionHints, FunctionNameMap, ModuleNameAllocator,
    NameInfo, NameSource, NamingMode, NamingOptions,
};
use super::strategy::{
    choose_local_candidate, choose_param_candidate, choose_synthetic_local_candidate,
    choose_upvalue_candidate,
};
use super::support::{alphabetical_name, is_lua_keyword_for_dialect};
use super::visibility::VisibleNames;

impl ModuleNameAllocator {
    fn reserve_function_shape_name(
        &mut self,
        candidate: CandidateHint,
        names: &FunctionNameAllocator<'_>,
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
            if !self.function_shape_names.contains(&text) && !names.is_used(&text) {
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

pub(super) struct FunctionAssignContext<'a> {
    pub proto: &'a AstProtoMeta,
    pub debug_like_function_index: usize,
    pub capture_evidence: Option<&'a ClosureCaptureEvidence<'a>>,
    pub hints: &'a FunctionHints,
    pub ast_facts: &'a FunctionAstNamingFacts,
    pub module_ast_facts: &'a AstNamingFacts<'a>,
    pub target_dialect: Option<DecompileDialect>,
    pub options: NamingOptions,
    pub visible_names: &'a VisibleNames,
    pub definition_position: usize,
    pub assigned_functions: &'a [FunctionNameMap],
    pub module_names: &'a mut ModuleNameAllocator,
}

struct FunctionNameAllocator<'a> {
    ast_facts: &'a AstNamingFacts<'a>,
    function: ProtoId,
    target_dialect: Option<DecompileDialect>,
    mode: NamingMode,
    visible_names: &'a VisibleNames,
    definition_position: usize,
    /// 贯穿整个函数作用域的全局占用名（参数、upvalue、环境局部或 DebugLike 模式）。
    used: BTreeSet<String>,
    /// 按词法区间记录的局部占用名，严格不相交块之间可安全复用 `i`、`k`、`v` 或同名 debug 局部。
    scoped_used: BTreeMap<String, Vec<Range<usize>>>,
    next_suffix_by_base: BTreeMap<String, usize>,
}

impl<'a> FunctionNameAllocator<'a> {
    fn new(
        ast_facts: &'a AstNamingFacts<'a>,
        function: ProtoId,
        target_dialect: Option<DecompileDialect>,
        mode: NamingMode,
        visible_names: &'a VisibleNames,
        definition_position: usize,
    ) -> Self {
        Self {
            ast_facts,
            function,
            target_dialect,
            mode,
            visible_names,
            definition_position,
            used: BTreeSet::new(),
            scoped_used: BTreeMap::new(),
            next_suffix_by_base: BTreeMap::new(),
        }
    }

    fn is_used(&self, name: &str) -> bool {
        self.is_used_in(name, None)
    }

    fn is_used_in(&self, name: &str, scope: Option<&Range<usize>>) -> bool {
        if is_lua_keyword_for_dialect(self.target_dialect, name)
            || self.used.contains(name)
            || self.ast_facts.reserves_global_name(self.function, name)
        {
            return true;
        }
        let Some(ranges) = self.scoped_used.get(name) else {
            return false;
        };
        if self.mode == NamingMode::DebugLike {
            return !ranges.is_empty();
        }
        match scope {
            Some(iv) => ranges.iter().any(|r| r.start < iv.end && iv.start < r.end),
            None => !ranges.is_empty(),
        }
    }

    fn record_name(&mut self, name: String, scope: Option<Range<usize>>) {
        if self.mode != NamingMode::DebugLike
            && let Some(iv) = scope
        {
            self.scoped_used.entry(name).or_default().push(iv);
        } else {
            self.used.insert(name);
        }
    }

    fn is_outer_visible(&self, name: &str) -> bool {
        self.visible_names.contains(name, self.definition_position)
    }

    fn allocate(&mut self, candidate: CandidateHint) -> NameInfo {
        self.allocate_scoped(candidate, false, None, false)
    }

    fn allocate_scoped(
        &mut self,
        candidate: CandidateHint,
        forbid_env: bool,
        scope: Option<Range<usize>>,
        is_unreferenced_discard: bool,
    ) -> NameInfo {
        if matches!(
            candidate.source,
            NameSource::LegacyArg | NameSource::LexicalEnvironment
        ) {
            self.used.insert(candidate.text.clone());
            return NameInfo {
                text: candidate.text,
                source: candidate.source,
                renamed: false,
            };
        }
        if (candidate.source == NameSource::Discard || is_unreferenced_discard)
            && candidate.text == "_"
            && !self.is_used_in(&candidate.text, scope.as_ref())
        {
            return NameInfo {
                text: candidate.text,
                source: candidate.source,
                renamed: false,
            };
        }

        let base = candidate.text;
        if !self.is_used_in(&base, scope.as_ref()) && !(forbid_env && base == "_ENV") {
            self.record_name(base.clone(), scope);
            return NameInfo {
                text: base,
                source: candidate.source,
                renamed: false,
            };
        }

        let mut suffix = if scope.is_some() && self.mode != NamingMode::DebugLike {
            2
        } else {
            self.next_suffix_by_base.get(&base).copied().unwrap_or(2)
        };
        loop {
            let renamed = format!("{base}{suffix}");
            suffix = suffix.saturating_add(1);
            if !self.is_used_in(&renamed, scope.as_ref()) && !(forbid_env && renamed == "_ENV") {
                if scope.is_none() || self.mode == NamingMode::DebugLike {
                    self.next_suffix_by_base.insert(base, suffix);
                }
                self.record_name(renamed.clone(), scope);
                return NameInfo {
                    text: renamed,
                    source: candidate.source,
                    renamed: true,
                };
            }
        }
    }
}

/// 为单个函数分配最终名字。
pub(super) fn assign_names_for_function(
    context: FunctionAssignContext<'_>,
) -> Result<FunctionNameMap, NamingError> {
    let FunctionAssignContext {
        proto,
        debug_like_function_index,
        capture_evidence,
        hints,
        ast_facts,
        module_ast_facts,
        target_dialect,
        options,
        visible_names,
        definition_position,
        assigned_functions,
        module_names,
    } = context;
    let mut names = FunctionNameAllocator::new(
        module_ast_facts,
        proto.id,
        target_dialect,
        options.mode,
        visible_names,
        definition_position,
    );
    let upvalue_candidates = proto
        .upvalues
        .iter()
        .enumerate()
        .map(|(index, _upvalue)| {
            choose_upvalue_candidate(
                proto,
                debug_like_function_index,
                index,
                capture_evidence,
                options,
                assigned_functions,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;

    // capture provenance 给出的 upvalue 名字，本质上就是父词法作用域里已经稳定存在的
    // 同一个绑定名。这里必须优先保留它们，再让当前函数里的 params/locals 绕开；
    // 如果反过来先给 locals 分配，再把 upvalue 重命名成 `value4` 之类，生成源码会把
    // 自由变量改成一个父作用域里根本不存在的名字，直接破坏运行语义。
    for candidate in &upvalue_candidates {
        if candidate.source == NameSource::CaptureProvenance {
            names.used.insert(candidate.text.clone());
        }
    }

    // 语义角色先占名，普通参数/local 的 debug 或推测名称必须避让。
    if proto.lexical_environment_local.is_some() {
        if upvalue_candidates.iter().any(|candidate| {
            candidate.source == NameSource::CaptureProvenance && candidate.text == "_ENV"
        }) {
            return Err(NamingError::InvalidLexicalEnvironment {
                function: proto.id.index(),
                reason: "local environment would shadow a captured _ENV binding",
            });
        }
        names.used.insert("_ENV".to_owned());
    }
    let params = proto
        .params
        .iter()
        .enumerate()
        .map(|(index, param)| {
            allocate_param_name(
                module_names.reserve_function_shape_name(
                    choose_param_candidate(
                        proto,
                        debug_like_function_index,
                        *param,
                        index,
                        hints,
                        ast_facts,
                        options,
                    ),
                    &names,
                    options.mode,
                ),
                index,
                options,
                ast_facts.forbids_env_params.contains(param),
                &mut names,
            )
        })
        .collect::<Vec<_>>();

    // 按“活动显式 debug/语义名 → 活动启发式/通用名 → 未发射死 LocalId”三档顺序分配，
    // 防止匿名启发式猜测（如 `value`）或死 LocalId 抢占真实源码 debug 局部变量的原名。
    let local_candidates: Vec<(bool, CandidateHint)> = (0..proto.local_count)
        .map(|index| {
            let local = LocalId(index);
            let is_live = ast_facts
                .debug_like_binding_order
                .contains_key(&crate::ast::AstBindingRef::Local(local));
            let candidate = choose_local_candidate(
                proto,
                debug_like_function_index,
                local,
                hints,
                ast_facts,
                options,
            );
            (is_live, candidate)
        })
        .collect();
    let mut local_slots: Vec<Option<NameInfo>> = vec![None; proto.local_count];
    for tier in 0..3u8 {
        for (index, (is_live, candidate)) in local_candidates.iter().enumerate() {
            let is_explicit = matches!(
                candidate.source,
                NameSource::LegacyArg | NameSource::LexicalEnvironment | NameSource::Debug
            );
            let item_tier = if *is_live && is_explicit {
                0
            } else if *is_live {
                1
            } else {
                2
            };
            if item_tier != tier {
                continue;
            }
            let binding_ref = crate::ast::AstBindingRef::Local(LocalId(index));
            let forbid_env = ast_facts.forbids_env_bindings.contains(&binding_ref);
            let scope = ast_facts.binding_scope_intervals.get(&binding_ref).cloned();
            let is_unreferenced_discard = candidate.text == "_"
                && !ast_facts.mentioned_bindings.contains(&binding_ref);
            local_slots[index] = Some(names.allocate_scoped(
                module_names.reserve_function_shape_name(candidate.clone(), &names, options.mode),
                forbid_env,
                scope,
                is_unreferenced_discard,
            ));
        }
    }
    let locals = local_slots
        .into_iter()
        .map(|slot| slot.expect("every local assigned"))
        .collect::<Vec<_>>();

    let mut upvalues = Vec::with_capacity(proto.upvalues.len());
    for candidate in upvalue_candidates {
        let candidate = module_names.reserve_function_shape_name(candidate, &names, options.mode);
        if candidate.source == NameSource::CaptureProvenance {
            upvalues.push(NameInfo {
                text: candidate.text,
                source: candidate.source,
                renamed: false,
            });
            continue;
        }

        upvalues.push(names.allocate(candidate));
    }

    let synthetic_locals = hints
        .synthetic_locals
        .iter()
        .copied()
        .enumerate()
        .map(|(synthetic_order, local)| {
            let binding_ref = crate::ast::AstBindingRef::SyntheticLocal(local);
            let forbid_env = ast_facts.forbids_env_bindings.contains(&binding_ref);
            let scope = ast_facts.binding_scope_intervals.get(&binding_ref).cloned();
            let cand = module_names.reserve_function_shape_name(
                choose_synthetic_local_candidate(
                    proto,
                    debug_like_function_index,
                    local,
                    synthetic_order,
                    hints,
                    ast_facts,
                    options,
                ),
                &names,
                options.mode,
            );
            let is_unreferenced_discard =
                cand.text == "_" && !ast_facts.mentioned_bindings.contains(&binding_ref);
            let info = names.allocate_scoped(cand, forbid_env, scope, is_unreferenced_discard);
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
    forbid_env: bool,
    names: &mut FunctionNameAllocator<'_>,
) -> NameInfo {
    if options.mode == NamingMode::DebugLike || candidate.source != NameSource::Simple {
        return names.allocate_scoped(candidate, forbid_env, None, false);
    }
    if !names.is_outer_visible(&candidate.text) {
        return names.allocate_scoped(candidate, forbid_env, None, false);
    }

    let replacement = next_available_simple_param_name(index, names);
    names.allocate_scoped(
        CandidateHint {
            text: replacement,
            source: candidate.source,
        },
        forbid_env,
        None,
        false,
    )
}

fn next_available_simple_param_name(mut index: usize, names: &FunctionNameAllocator<'_>) -> String {
    loop {
        let candidate = alphabetical_name(index).unwrap_or_else(|| format!("arg{}", index + 1));
        if !names.is_used(&candidate) && !names.is_outer_visible(&candidate) {
            return candidate;
        }
        index = index.saturating_add(1);
    }
}
