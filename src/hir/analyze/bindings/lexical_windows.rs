//! 把已证明的词法生命周期统一为 exclusive low 区间，供 regular-range owner 原子物化。
//!
//! Close 区间来自捕获 cell 的真实 cleanup；debug 区间只接受封闭的 closure 求值窗口：
//! `closure rN; move rN -> rN+1; call ignored; debug-end` 可恢复一个中间 `do`。
//! debug end 不证明任意 scratch root 死亡，因此窗口新增的对象只能是这个 closure
//! 及其 Move 别名，其他定义只能是常量；捕获 cell、open 值和跨窗口 SSA 使用仍拒绝。
//! 这里消费 Structure 的 debug 边界与 SSA/root 事实，不从 HIR 语句或 AST 形状猜作用域。

use std::ops::Range;

use super::*;
use crate::structure::{DebugBindingFact, DebugBindingFacts, RootObservation};
use crate::transformer::ResultPack;

pub(super) fn collect_lexical_scopes(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    structure: &ReadyStructureFacts,
    mut scopes: Vec<Range<usize>>,
) -> Vec<Range<usize>> {
    let debug_bindings = structure.debug_bindings();
    scopes.extend(
        debug_bindings
            .accepted()
            .iter()
            .filter_map(|fact| debug_closure_window(proto, cfg, dataflow, debug_bindings, fact)),
    );
    retain_non_crossing(scopes)
}

fn debug_closure_window(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    debug_bindings: &DebugBindingFacts,
    fact: &DebugBindingFact,
) -> Option<Range<usize>> {
    if !proto.debug_locals.get(fact.scope)?.is_source() {
        return None;
    }
    let SsaValue::Def(binding) = fact.value else {
        return None;
    };
    let origin = dataflow.def_instr(binding).index();
    let end = fact.end_instr?.index();
    if origin >= end || !matches!(proto.instrs.get(origin)?, LowInstr::Closure(_)) {
        return None;
    }
    let block = *cfg.instr_to_block.get(origin)?;
    // 候选拒绝[ProofIncomplete]：尚无跨基本块的完整窗口入口、出口及 root 边界证明。
    if cfg.instr_to_block.get(end - 1) != Some(&block) {
        return None;
    }
    let LowInstr::Call(call) = proto.instrs.get(end - 1)? else {
        // 候选拒绝[ProofIncomplete]：debug end 前缺少当前分析能证明的 callee 观察边界。
        return None;
    };
    // 候选拒绝[ProofIncomplete]：非空结果或更宽 caller 前缀需要额外结果根、其他 binding 的生命周期证明。
    if !matches!(call.results, ResultPack::Ignore)
        || !matches!(dataflow.effect_summaries.get(end - 1)?.root_observation,
            RootObservation::Call { caller_end } if caller_end.index() == fact.reg.index() + 1)
    {
        return None;
    }
    // 候选拒绝[ProofIncomplete]：初始化依赖若不能闭合到同块固定槽窗口，尚不能确定完整声明起点。
    let start = lexical_scope_evaluation_start(dataflow, cfg, block, fact.reg, origin)?;
    let window = start..end;
    // true 是唯一新 closure 的别名；false 是不引入独立对象根的 VM 常量。
    // 常量字符串本来就由 proto 持有，不能把其他寄存器对象冒充为常量。
    let mut values = BTreeMap::<DefId, bool>::new();
    for index in window.clone() {
        let instr = &proto.instrs[index];
        let effect = &dataflow.instr_effects[index];
        // 候选拒绝[ProofIncomplete]：尚未合并控制/cleanup owner、open 包或外来高槽值的窗口生命周期事实。
        if instr.is_control_terminator()
            || matches!(instr, LowInstr::Close(_) | LowInstr::Tbc(_))
            || effect.open_use.is_some()
            || effect.open_must_def.is_some()
            || effect.fixed_uses().iter().any(|&reg| {
                reg.index() >= fact.reg.index()
                    && !matches!(dataflow.use_value(InstrRef(index), reg),
                        SsaValue::Def(def) if values.contains_key(&def))
            })
        {
            return None;
        }
        let defs = &dataflow.instr_defs[index];
        if defs.is_empty() {
            continue;
        }
        let is_closure = match instr {
            LowInstr::Closure(_) if index == origin => true,
            LowInstr::LoadNil(_)
            | LowInstr::LoadBool(_)
            | LowInstr::LoadConst(_)
            | LowInstr::LoadInteger(_)
            | LowInstr::LoadNumber(_) => false,
            LowInstr::Move(mov) => {
                let SsaValue::Def(source) = dataflow.use_value(InstrRef(index), mov.src) else {
                    // 候选拒绝[ProofIncomplete]：Entry/Phi 输入尚无属于该 closure 或常量的 provenance。
                    return None;
                };
                // 候选拒绝[ProofIncomplete]：外来 Move 值不在已证明的单对象根集合内。
                *values.get(&source)?
            }
            // 候选拒绝[ProofIncomplete]：其他 producer 尚无“不引入独立可收集根”的值事实。
            _ => return None,
        };
        for &def in defs {
            let reg = dataflow.def_reg(def);
            // 候选拒绝[ProofIncomplete]：外层写、额外 debug binding、捕获 cell 或逃逸 def/phi 需独立 owner 证明，当前单 binding 窗口未覆盖。
            if reg.index() < fact.reg.index()
                || (reg == fact.reg && def != binding)
                || dataflow.reg_is_reference_captured(reg)
                || (def != binding && debug_bindings.for_value(SsaValue::Def(def)).is_some())
                || dataflow.def_uses[def.index()]
                    .iter()
                    .any(|site| !window.contains(&site.instr.index()))
                || dataflow.def_phi_uses[def.index()]
                    .iter()
                    .any(|&phi| !dataflow.phi_is_truly_dead(phi))
            {
                return None;
            }
            values.insert(def, is_closure);
        }
    }
    let SsaValue::Def(callee) = dataflow.use_value(InstrRef(end - 1), call.callee) else {
        // 候选拒绝[ProofIncomplete]：末尾 callee 的 Entry/Phi 来源尚不能与目标 closure 配对。
        return None;
    };
    // 候选拒绝[ProofIncomplete]：无真实 callee 别名配对时，Call 的 caller 边界不足以证明该对象窗口。
    (values.get(&callee) == Some(&true)).then_some(window)
}

fn retain_non_crossing(mut scopes: Vec<Range<usize>>) -> Vec<Range<usize>> {
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
