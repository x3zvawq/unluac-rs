//! 将已证明的词法生命周期投影为 low 指令区间，供 plan body 原子物化。
//!
//! 消费 Structure 的 cleanup/debug 边界、SSA/root 与冻结发射域，验证唯一入口、
//! 出口及值是否逃出窗口，不从 HIR 或 AST 外形猜作用域。
//! 例如 local object={}; use(object); debug-end 可恢复为 do 块；debug end
//! 只表示源码槽复用边界，不证明 VM 已清空旧根。

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
        if let Some(end) = fact.end_instr
            && proto.debug_locals[fact.scope].is_source()
            && let Some(origin) = binding_origin(fact.value, dataflow, cfg)
            && origin < end.index()
        {
            cohorts.entry(end.index()).or_default().push(fact);
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

fn binding_origin(value: SsaValue, dataflow: &DataflowFacts, cfg: &Cfg) -> Option<usize> {
    match value {
        SsaValue::Def(def) => Some(dataflow.def_instr(def).index()),
        SsaValue::Phi(phi) => Some(
            cfg.blocks[dataflow.phi_candidate(phi)?.block.index()]
                .instrs
                .start
                .index(),
        ),
        SsaValue::Entry(_) => None,
    }
}

/// 原声明的必经写下界：Phi 本身没有写，只有全部入口都由同槽真实 Def 形成时，
/// 才可在合流块必经的前提下使用最早输入写。嵌套 Phi/Entry 不冒充物理覆盖。
fn binding_overwrite_floor(value: SsaValue, dataflow: &DataflowFacts) -> Option<usize> {
    match value {
        SsaValue::Def(def) => Some(dataflow.def_instr(def).index()),
        SsaValue::Phi(id) => {
            let phi = dataflow.phi_candidate(id)?;
            let mut earliest = None;
            for incoming in &phi.incoming {
                let SsaValue::Def(def) = incoming.value else {
                    return None;
                };
                if dataflow.def_reg(def) != phi.reg {
                    return None;
                }
                let at = dataflow.def_instr(def).index();
                earliest = Some(earliest.map_or(at, |old: usize| old.min(at)));
            }
            earliest
        }
        SsaValue::Entry(_) => None,
    }
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
    // 空区间证明最后一个声明初始化后立即离域；必须恢复这个词法末端，
    // 否则保留名称会把 local 延长到后继求值，并抬高其 CALL/临时槽。
    // 非空区间仍需原有调用退休证明，不能单凭 debug end 推断旧根已死亡。
    let immediate_end = facts.iter().any(|fact| fact.start_pc == fact.end_pc);
    let dispatch = if immediate_end {
        end - 1
    } else {
        last_observation?
    };
    let mut owners = BTreeMap::new();
    let mut overwrite_floors = BTreeMap::new();
    let mut origin = end;
    for fact in facts {
        let reg = match fact.value {
            SsaValue::Def(def) => dataflow.def_reg(def),
            SsaValue::Phi(phi) => dataflow.phi_candidate(phi)?.reg,
            SsaValue::Entry(_) => return None,
        };
        // 候选拒绝[ProofIncomplete]：canonical 身份若来自其他槽，或同槽存在多个 owner，
        // 不能把 source scope 直接当作该固定定义的生命周期。
        if reg != fact.reg || owners.insert(fact.reg, *fact).is_some() {
            return None;
        }
        origin = origin.min(binding_origin(fact.value, dataflow, cfg)?);
        if let Some(at) = binding_overwrite_floor(fact.value, dataflow) {
            overwrite_floors.insert(fact.reg, (at, fact.declaration_block?));
        }
    }
    let (&floor, _) = owners.first_key_value()?;
    let (&ceiling, _) = owners.last_key_value()?;
    // 候选拒绝[ProofIncomplete]：非空结果或更宽 caller 前缀仍需额外结果根、外来 binding 证明。
    let final_observation = dataflow.effect_summaries.get(dispatch)?.root_observation;
    if !immediate_end
        && (!matches!(proto.instrs.get(dispatch), Some(LowInstr::Call(call)) if matches!(call.results, ResultPack::Ignore))
            || cfg.instr_to_block[dispatch] != cfg.instr_to_block[end - 1]
            || !matches!(final_observation,
            RootObservation::Call { caller_end } if caller_end.index() == ceiling.index() + 1))
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
            || owners.values().any(|fact| {
                fact.declaration_block
                    .is_none_or(|block| !graph.dominates(block, exit))
            }))
    {
        return None;
    }
    // 空区间末端只关闭原声明及其高槽求值临时量，不清空物理残值；普通窗口
    // 仍由调用排除上界与必经覆盖写证明退休，不重建 for 的动态值类型。
    let home_retires = |reg: Reg, at: usize, block: BlockRef| {
        (immediate_end && reg > ceiling)
            || final_observation.excludes_home_from_caller(reg)
            || overwrite_floors
                .get(&reg)
                .is_some_and(|&(first_write, merge)| {
                    first_write > at && graph.post_dominates(merge, block)
                })
    };
    let local_phis = dataflow.closed_phis_in_instruction_window(cfg, window.clone(), floor)?;
    // 已接受的 Phi 声明拥有同槽输入形成的值。每个邻接边只遍历一次，闭包仍须完整
    // 位于该窗口；不能把其它槽的 COPY 源根或窗口外的 Entry 一起认作声明身份。
    let mut owned_phis = BTreeSet::new();
    let mut owned_defs = BTreeSet::new();
    let mut pending = owners
        .values()
        .filter_map(|fact| match fact.value {
            SsaValue::Phi(phi) => Some(phi),
            _ => None,
        })
        .collect::<Vec<_>>();
    while let Some(id) = pending.pop() {
        if !owned_phis.insert(id) {
            continue;
        }
        if !local_phis.contains(&id) {
            return None;
        }
        let phi = dataflow.phi_candidate(id)?;
        for incoming in &phi.incoming {
            match incoming.value {
                SsaValue::Def(def) if dataflow.def_reg(def) == phi.reg => {
                    owned_defs.insert(def);
                }
                SsaValue::Phi(source) if dataflow.phi_candidate(source)?.reg == phi.reg => {
                    pending.push(source);
                }
                _ => return None,
            }
        }
    }
    for &id in &local_phis {
        let phi = dataflow.phi_candidate(id)?;
        if dataflow.reg_is_reference_captured(phi.reg)
            || (!owned_phis.contains(&id)
                && !home_retires(
                    phi.reg,
                    cfg.blocks[phi.block.index()].instrs.start.index(),
                    phi.block,
                ))
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
            let is_owner = owner.is_some_and(|fact| fact.value == SsaValue::Def(def))
                || owned_defs.contains(&def);
            let source_write = owner.is_some_and(|fact| {
                let pcs = &proto.lowering_map.pc_map()[index];
                !pcs.is_empty()
                    && pcs.iter().all(|pc| {
                        proto
                            .debug_locals
                            .source_at(reg, *pc)
                            .is_some_and(|(scope, _)| scope == fact.scope)
                    })
            });
            // 候选拒绝[ProofIncomplete]：禁止未归属源码身份的 owner 槽复写、未结束的异期 binding、
            // 捕获 cell 和逃逸 def/phi；窗口不能吞掉其他生命周期或延续其值身份。
            if (owner.is_some_and(|owner| {
                binding_origin(owner.value, dataflow, cfg).is_none_or(|at| at <= index)
            }) && !is_owner
                && !source_write)
                || dataflow.reg_is_reference_captured(reg)
                || (!is_owner
                    && !source_write
                    && debug_bindings
                        .for_value(SsaValue::Def(def))
                        .is_some_and(|binding| {
                            binding.reg != reg
                                || binding.end_instr.is_none_or(|binding_end| {
                                    binding_end.index() > end
                                        || (!final_observation.excludes_home_from_caller(reg)
                                            && owner.is_none_or(|owner| {
                                                binding_origin(owner.value, dataflow, cfg)
                                                    .is_none_or(|at| binding_end.index() > at)
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
            let retained = if is_owner || source_write {
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
                        SsaValue::Phi(phi) => owned_phis.contains(&phi),
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
    // Def/Phi 已通过窗口闭包和逐槽归属证明；只封闭词法窗口，不在 debug end
    // 生成 CLEAR。调用中的 callee/self 仍由活动帧保活。
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
