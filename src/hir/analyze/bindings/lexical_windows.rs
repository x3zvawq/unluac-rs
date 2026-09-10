//! 把已证明的词法生命周期统一为 exclusive low 区间，供 plan body 原子物化。
//!
//! Close 区间来自捕获 cell 的真实 cleanup；debug 窗口来自共同结束的源码 binding：
//! `local object = {}; local function use(x) end; use(object); debug-end` 恢复为一个 `do`。
//! 窗口的新对象必须属于这些 binding，或有末端前必定覆盖/被调用排除的 scratch home；捕获 cell、
//! open 值和跨窗口内部 SSA 使用仍拒绝。已在外层建立的源码身份可在窗口内更新；
//! 末次调用后的纯尾部也只能更新这些外层身份。debug end 恢复槽复用边界，不表示 VM 已清空旧槽。
//! 这里消费 Structure 的 debug 边界与 SSA/root 事实，不从 HIR 语句或 AST 形状猜作用域。
//! callee 与其它 scratch 消费同一逐槽退休证书；调用帧保活不等于 caller 槽被清空。
//! 普通 if/else 与完整循环可处于窗口内部；共享图区间查询证明唯一入口、出口，
//! 冻结 plan 则保证两端仍在实际发射的指令前缀，不能切入已被表达式或循环语法吸收的位置。

use std::ops::Range;

use super::*;
use crate::hir::emission::HirEmissionFacts;
use crate::structure::{CleanupDisposition, DebugBindingFact, GraphFacts, RootObservation};
use crate::transformer::ResultPack;

pub(super) fn collect_lexical_scopes(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph: &GraphFacts,
    structure: &ReadyStructureFacts,
    emission: &HirEmissionFacts<'_>,
    mut scopes: Vec<Range<usize>>,
) -> Vec<Range<usize>> {
    let debug_bindings = structure.debug_bindings();
    // 同一结束点的 local 共同拥有窗口；producer 可以分属 if 前缀和合流后的基本块。
    let mut cohorts = BTreeMap::<_, Vec<&DebugBindingFact>>::new();
    for fact in debug_bindings.accepted() {
        if let (SsaValue::Def(def), Some(end)) = (fact.value, fact.end_instr)
            && proto.debug_locals[fact.scope].is_source()
        {
            let origin = dataflow.def_instr(def).index();
            if origin < end.index() {
                cohorts.entry(end.index()).or_default().push(fact);
            }
        }
    }
    if cohorts.is_empty() {
        return retain_non_crossing(scopes);
    }
    let mut scanned = 0;
    let mut last_observation = None;
    scopes.extend(cohorts.into_iter().filter_map(|(end, facts)| {
        // cohorts 已按结束点排序，共用一次观察前缀扫描，避免每个窗口回扫纯尾部。
        for index in scanned..end {
            if dataflow.effect_summaries[index].may_observe_gc_roots()
                || matches!(proto.instrs[index], LowInstr::Close(_) | LowInstr::Tbc(_))
            {
                last_observation = Some(index);
            }
        }
        scanned = end;
        debug_binding_window(
            proto,
            cfg,
            dataflow,
            graph,
            structure,
            emission,
            (end, &facts, last_observation),
        )
    }));
    retain_non_crossing(scopes)
}

fn debug_binding_window(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph: &GraphFacts,
    structure: &ReadyStructureFacts,
    emission: &HirEmissionFacts<'_>,
    cohort: (usize, &[&DebugBindingFact], Option<usize>),
) -> Option<Range<usize>> {
    let (end, facts, last_observation) = cohort;
    let debug_bindings = structure.debug_bindings();
    let dispatch = last_observation?;
    let LowInstr::Call(call) = proto.instrs.get(dispatch)? else {
        // 候选拒绝[ProofIncomplete]：debug end 前缺少当前分析能证明的 callee 观察边界。
        return None;
    };
    let mut owners = BTreeMap::new();
    let mut origin = end;
    for fact in facts {
        let SsaValue::Def(def) = fact.value else {
            unreachable!("cohort contains only definition bindings");
        };
        // 候选拒绝[ProofIncomplete]：canonical 身份若来自其他槽，或同槽存在多个 owner，
        // 不能把 source scope 直接当作该固定定义的生命周期。
        if dataflow.def_reg(def) != fact.reg || owners.insert(fact.reg, def).is_some() {
            return None;
        }
        origin = origin.min(dataflow.def_instr(def).index());
    }
    let (&floor, _) = owners.first_key_value()?;
    let (&ceiling, _) = owners.last_key_value()?;
    // 候选拒绝[ProofIncomplete]：非空结果或更宽 caller 前缀仍需额外结果根、外来 binding 证明。
    let final_observation = dataflow.effect_summaries.get(dispatch)?.root_observation;
    if !matches!(call.results, ResultPack::Ignore)
        || cfg.instr_to_block[dispatch] != cfg.instr_to_block[end - 1]
        || !matches!(final_observation,
            RootObservation::Call { caller_end } if caller_end.index() == ceiling.index() + 1)
    {
        return None;
    }
    let entry = cfg.instr_to_block[origin];
    let exit = cfg.instr_to_block[end - 1];
    let start = lexical_scope_evaluation_start(dataflow, cfg, entry, floor, origin)?;
    let window = start..end;

    if !emission.regular_prefix(entry)?.contains(&start)
        || !emission.regular_prefix(exit)?.contains(&(end - 1))
        || emission.scope_owner(entry) != emission.scope_owner(exit)
    {
        return None;
    }
    if entry != exit
        && (!graph.closed_instruction_window(cfg, window.clone())
            || !window_emission_is_local(cfg, emission, &window)
            || owners
                .values()
                .any(|&def| !graph.dominates(dataflow.def_block(def), exit)))
    {
        return None;
    }
    // 调用排除上界与必经覆盖写共同证明末端退休；高槽不需要再重建 for 的动态值类型。
    let home_retires = |reg: Reg, at: usize, block: BlockRef| {
        final_observation.excludes_home_from_caller(reg)
            || owners.get(&reg).is_some_and(|owner| {
                dataflow.def_instr(*owner).index() > at
                    && graph.post_dominates(dataflow.def_block(*owner), block)
            })
    };
    let local_phis = dataflow.closed_phis_in_instruction_window(cfg, window.clone(), floor)?;
    for &id in &local_phis {
        let phi = dataflow.phi_candidate(id)?;
        if dataflow.reg_is_reference_captured(phi.reg)
            || !home_retires(
                phi.reg,
                cfg.blocks[phi.block.index()].instrs.start.index(),
                phi.block,
            )
        {
            return None;
        }
    }
    let mut retained_defs = BTreeSet::<DefId>::new();
    for index in window.clone() {
        let instr = &proto.instrs[index];
        let effect = &dataflow.instr_effects[index];
        // for 控制只消费冻结协议的指令身份；其隐式 closing 仍由原生语法在原位置执行。
        // 额外 Close 只接纳不涉及捕获 cell/显式 TBC 的已归属词法边界。
        if (instr.is_control_terminator()
            && !matches!(instr, LowInstr::Branch(_) | LowInstr::Jump(_))
            && !emission.for_instr(InstrRef(index)))
            || matches!(instr, LowInstr::Tbc(_))
            || matches!(instr, LowInstr::Close(close) if close.from < floor
                || dataflow.reference_captured_regs().any(|reg| reg >= close.from)
                || structure.plan().cleanup_tbc_origins(InstrRef(index)).is_some_and(|origins| !origins.is_empty())
                || !matches!(structure.plan().cleanup_disposition(InstrRef(index)),
                    Some(CleanupDisposition::LexicalScope(_))))
            || effect.open_use.is_some()
            || effect.open_must_def.is_some()
            || effect.fixed_uses_from(floor).iter().any(|&reg| {
                match dataflow.use_value(InstrRef(index), reg) {
                    SsaValue::Def(def) => !window.contains(&dataflow.def_instr(def).index()),
                    SsaValue::Phi(phi) => !local_phis.contains(&phi),
                    SsaValue::Entry(_) => true,
                }
            })
        {
            return None;
        }
        for &def in &dataflow.instr_defs[index] {
            let reg = dataflow.def_reg(def);
            if reg < floor {
                // 已在窗口外建立的源码 binding 可以在 do 内更新；它仍引用同一
                // 外层身份。未证明的 scratch/声明不能借此逃出窗口或延长存活期。
                let outer = proto.lowering_map.pc_map()[index].iter().all(|pc| {
                    proto
                        .debug_locals
                        .source_at(reg, *pc)
                        .and_then(|(scope, _)| debug_bindings.for_scope(scope))
                        .is_some_and(|fact| {
                            fact.end_instr
                                .is_none_or(|scope_end| scope_end.index() >= end)
                                && match fact.value {
                                    SsaValue::Entry(_) => fact.start_pc == 0,
                                    SsaValue::Def(owner) => {
                                        dataflow.def_instr(owner).index() < start
                                            && graph.dominates(dataflow.def_block(owner), entry)
                                    }
                                    SsaValue::Phi(_) => false,
                                }
                        })
                });
                if !outer || proto.lowering_map.pc_map()[index].is_empty() {
                    return None;
                }
                continue;
            }
            // caller 排除只能证明 dispatch 前的 scratch；纯尾部不得再建立窗口内根。
            if index > dispatch {
                return None;
            }
            let owner = owners.get(&reg);
            let is_owner = owner == Some(&def);
            // 候选拒绝[ProofIncomplete]：禁止声明后的 owner 槽复写、未结束的异期 binding、
            // 捕获 cell 和逃逸 def/phi；窗口不能吞掉其他生命周期或延续其值身份。
            if (owner.is_some_and(|owner| dataflow.def_instr(*owner).index() <= index) && !is_owner)
                || dataflow.reg_is_reference_captured(reg)
                || (!is_owner
                    && debug_bindings
                        .for_value(SsaValue::Def(def))
                        .is_some_and(|binding| {
                            binding.reg != reg
                                || binding.end_instr.is_none_or(|binding_end| {
                                    binding_end.index() > end
                                        || (!final_observation.excludes_home_from_caller(reg)
                                            && owner.is_none_or(|owner| {
                                                binding_end.index()
                                                    > dataflow.def_instr(*owner).index()
                                            }))
                                })
                        }))
                || dataflow.def_uses[def.index()]
                    .iter()
                    .any(|site| !window.contains(&site.instr.index()))
                || dataflow.def_phi_uses[def.index()]
                    .iter()
                    .any(|&phi| !dataflow.phi_is_truly_dead(phi) && !local_phis.contains(&phi))
            {
                return None;
            }
            let retained = if is_owner {
                true
            } else {
                match instr {
                    LowInstr::LoadNil(_)
                    | LowInstr::LoadBool(_)
                    | LowInstr::LoadConst(_)
                    | LowInstr::LoadInteger(_)
                    | LowInstr::LoadNumber(_) => true,
                    LowInstr::Move(mov) if mov.src < floor => {
                        // 引用捕获的外层槽可能被调用回写；其副本仍按独立 scratch 证明退休。
                        !dataflow.reg_is_reference_captured(mov.src)
                    }
                    LowInstr::Move(mov) => match dataflow.use_value(InstrRef(index), mov.src) {
                        SsaValue::Def(source) => retained_defs.contains(&source),
                        SsaValue::Phi(_) => false,
                        SsaValue::Entry(_) => return None,
                    },
                    _ => false,
                }
            };
            // 独立 scratch 的证书只授权当前 home 在 END 退休，不能使其后续 MOVE 免于逐槽证明。
            if retained {
                retained_defs.insert(def);
            } else if !home_retires(reg, index, dataflow.def_block(def)) {
                return None;
            }
        }
    }
    // Call 的 caller_end 就是 callee 槽；其 Def/Phi 已通过窗口闭包和逐槽退休证明。
    // 调用中的 callee/self 仍由活动帧保活；只封闭词法窗口，不在 debug end 生成 CLEAR。
    Some(window)
}

/// 图边界已经证明；这里只限制窗口内的发射域和会被新词法块截断的值。
fn window_emission_is_local(
    cfg: &Cfg,
    emission: &HirEmissionFacts<'_>,
    window: &Range<usize>,
) -> bool {
    for run in cfg.instr_to_block[window.clone()].chunk_by(|a, b| a == b) {
        let block = run[0];
        if !emission.ordinary_block(block) {
            return false;
        }
    }
    true
}

pub(super) fn retain_non_crossing(mut scopes: Vec<Range<usize>>) -> Vec<Range<usize>> {
    scopes.sort_unstable_by(|a, b| a.start.cmp(&b.start).then_with(|| b.end.cmp(&a.end)));
    scopes.dedup();
    let mut retained = vec![true; scopes.len()];
    let mut all_ends = BTreeSet::new();
    let mut pending = BTreeMap::<usize, Vec<usize>>::new();
    let mut group_start = 0;
    while group_start < scopes.len() {
        let start = scopes[group_start].start;
        let group_end =
            group_start + scopes[group_start..].partition_point(|scope| scope.start == start);
        for index in group_start..group_end {
            let end = scopes[index].end;
            // 同起点区间彼此嵌套；先完成整组查询再插入。已拒绝的区间仍能证明
            // 后续 crossing，但每个待拒绝区间只从 pending 移除一次，合计 O(C log C)。
            // 候选拒绝[ProofIncomplete]：交叉的恢复边界尚无统一词法 owner，不能任意延长或缩短任一窗口。
            if all_ends.range(start + 1..end).next().is_some() {
                retained[index] = false;
            }
            // 候选拒绝[ProofIncomplete]：同一 crossing 的较早区间也没有可独立提交的嵌套边界。
            while let Some((&crossed_end, _)) = pending.range(start + 1..end).next() {
                for crossed in pending
                    .remove(&crossed_end)
                    .expect("queried scope end exists")
                {
                    retained[crossed] = false;
                }
            }
        }
        for index in group_start..group_end {
            let end = scopes[index].end;
            all_ends.insert(end);
            if retained[index] {
                pending.entry(end).or_default().push(index);
            }
        }
        group_start = group_end;
    }
    scopes
        .into_iter()
        .zip(retained)
        .filter_map(|(scope, retained)| retained.then_some(scope))
        .collect()
}
