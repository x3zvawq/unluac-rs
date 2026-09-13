//! 将 Dataflow 的调用边界与 canonical 参数 def 配对，冻结 caller 槽交接事实。
//! 同时保留调用结果的同槽覆盖与所有固定定义的精确 dispatch 终点，使 HIR 不必重扫低层后缀。
//!
//! CALL 参数位于 caller prefix 之外，callee 可覆盖这些槽；它们不是跨调用继续存在的
//! 独立 caller root。例如 t = {}; f(t) 的参数槽可交给 f，而 local owner; f(owner) 中
//! owner 的原始低槽不随参数 MOVE 一并交出。这里只发布同 basic block 的 direct def，
//! phi、跨 block use 和按引用捕获槽不产生证明；调用结果最后读取后的覆盖可以位于各直接
//! successor，由 Dataflow 发布完整 frontier。实际 producer 删除由 HIR 求值顺序 owner 审查。
//! 调用布局独立于 callee 值身份；完整帧另需 canonical Def/phi 保留同一 home，
//! 如 `assert(check()==12)` 的 Boolean 合流不创建新 callee。参数区的捕获状态独立
//! 保存，不能因某个参数没有 direct Def 而丢失布局，也不把布局当作一般根退休许可。

use super::*;
use crate::hir::common::HirCallArgumentRoot;
use crate::transformer::ValuePack;

/// 同一原始 CALL 索引下共享参数根与完整调用布局，避免后层按方言重解槽距。
#[derive(Debug, Clone)]
pub(super) struct NativeCallFacts {
    pub(super) argument_roots: Vec<HirCallArgumentRoot>,
    pub(super) argument_values: Vec<Option<TempId>>,
    pub(super) layout: NativeCallLayout,
    pub(super) callee: Option<TempId>,
    pub(super) assignment_copies: Option<[TempId; 2]>,
    pub(super) boolean_prewrites: Vec<BooleanArgumentPrewrite>,
    pub(super) fastcall_argument_copies: Vec<FastCallArgumentCopy>,
}

/// FASTCALL 的非 direct 参数在慢路径才复制到 CALL 参数区；快速路径读取原低槽。
/// 这里只保存原 COPY 身份及两端槽，不发布普通 CALL 的根交接许可。
#[derive(Debug, Clone, Copy)]
pub(in crate::hir) struct FastCallArgumentCopy {
    pub(in crate::hir) argument: usize,
    pub(in crate::hir) producer: TempId,
    pub(in crate::hir) source: Option<TempId>,
    pub(in crate::hir) home: HomeSlotKey,
    pub(in crate::hir) source_home: HomeSlotKey,
}

/// ValueDecision 的入口 Boolean 写与结果 phi 属于同一参数槽；仅完整值帧可重发这次写。
#[derive(Debug, Clone, Copy)]
pub(in crate::hir) struct BooleanArgumentPrewrite {
    pub(in crate::hir) argument: usize,
    pub(in crate::hir) initial: TempId,
    pub(in crate::hir) result: TempId,
    pub(in crate::hir) home: HomeSlotKey,
}

/// 原参数/结果的物理布局不依赖 callee 是否能归一成单个 canonical Def。
/// `(flag and f or g)({ ... })` 的函数身份是 phi，构造器仍属于原调用参数区。
#[derive(Debug, Clone, Copy)]
pub(in crate::hir) struct NativeCallLayout {
    pub(in crate::hir) home: HomeSlotKey,
    pub(in crate::hir) args: ValuePack,
    pub(in crate::hir) results: Option<ResultPack>,
    /// 原调用时整个参数区没有打开的引用捕获；不依赖参数值是否是 canonical Def。
    pub(in crate::hir) arguments_unaliased: bool,
    pub(in crate::hir) fastcall: Option<crate::transformer::FastCallProtocol>,
}

/// callee 的原 Def 身份、CALL 槽和包宽度；完整树化保持调用前后原隐式槽而非签发提前释放。
#[derive(Debug, Clone, Copy)]
pub(in crate::hir) struct NativeCallFrame {
    pub(in crate::hir) callee: TempId,
    pub(in crate::hir) home: HomeSlotKey,
    pub(in crate::hir) args: ValuePack,
    /// None 仅表示原 TAILCALL 的 frame 转移，不是未知结果宽度。
    pub(in crate::hir) results: Option<ResultPack>,
    pub(in crate::hir) arguments_unaliased: bool,
}

pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
    plan: &StructurePlan,
) -> BTreeMap<InstrRef, NativeCallFacts> {
    let prewrites = boolean_prewrites(proto, dataflow, plan, fixed_temps, phi_temps);
    let mut calls = BTreeMap::new();
    for (index, instr) in proto.instrs.iter().enumerate() {
        let (callee, args, results, fastcall) = match instr {
            LowInstr::Call(call) => (
                call.callee,
                call.args,
                Some(call.results),
                match call.kind {
                    crate::transformer::CallKind::FastCall(protocol) => Some(protocol),
                    _ => None,
                },
            ),
            LowInstr::TailCall(call) => (call.callee, call.args, None, None),
            _ => continue,
        };
        let args_start = match args {
            ValuePack::Fixed(args) => args.start,
            ValuePack::Open(start) => start,
        };
        let call_ref = InstrRef(index);
        let mut roots = Vec::new();
        // OPEN 参数的固定前缀已经由 Dataflow 的 SSA use map 证明；不能用可能
        // liveness uses 猜测长度，也不在 HIR 重解 open-top 协议。
        for (reg, value) in dataflow.use_values_at(call_ref).iter() {
            if fastcall.is_some() {
                break;
            }
            // TAILCALL 的布局仍可证明，但 frame-exit 不签发普通 CALL 的参数根交接。
            let RootObservation::Call { caller_end } =
                dataflow.effect_summaries[index].root_observation
            else {
                break;
            };
            if reg.index() < args_start.index() {
                continue;
            }
            let argument = reg.index() - args_start.index();
            if reg.index() <= caller_end.index()
                || epochs.reference_capture_may_be_open(reg, call_ref)
            {
                continue;
            }
            let SsaValue::Def(def) = value else {
                continue;
            };
            let producer = TempId(def.index());
            if fixed_temps[def.index()] != producer
                || dataflow.def_reg(def) != reg
                || dataflow.def_block(def) != cfg.instr_to_block[index]
                || dataflow.def_instr(def).index() >= index
                || !dataflow.def_phi_uses[def.index()].is_empty()
                || dataflow.def_uses[def.index()].iter().any(|use_| {
                    use_.instr.index() <= dataflow.def_instr(def).index()
                        || use_.instr.index() > index
                })
            {
                continue;
            }
            roots.push(HirCallArgumentRoot { producer, argument });
        }
        let layout = NativeCallLayout {
            home: HomeSlotKey::new(callee.index(), epochs.epoch_at(callee, call_ref)),
            args,
            results,
            arguments_unaliased: {
                let end = match args {
                    ValuePack::Fixed(pack) => pack.start.index() + pack.len,
                    ValuePack::Open(_) => usize::from(proto.frame.max_stack_size),
                };
                (args_start.index()..end)
                    .all(|slot| !epochs.reference_capture_may_be_open(Reg(slot), call_ref))
            },
            fastcall,
        };
        let callee = match dataflow.use_values_at(call_ref).get(callee) {
            Some(SsaValue::Def(def))
                if fixed_temps[def.index()] == TempId(def.index())
                    && dataflow.def_reg(def) == callee
                    && dataflow.def_instr(def).index() < index
                    && !epochs.reference_capture_may_be_open(callee, call_ref) =>
            {
                Some(TempId(def.index()))
            }
            Some(SsaValue::Phi(phi))
                if dataflow.phi_candidates[phi.index()].reg == callee
                    && phi_temps.get(phi.index())
                        == Some(&TempId(dataflow.defs.len() + phi.index()))
                    && !epochs.reference_capture_may_be_open(callee, call_ref) =>
            {
                Some(phi_temps[phi.index()])
            }
            _ => None,
        };
        calls.insert(
            call_ref,
            NativeCallFacts {
                argument_roots: roots,
                argument_values: match args {
                    ValuePack::Fixed(pack) => (0..pack.len)
                        .map(|offset| {
                            canonical_value_temp(
                                dataflow.use_value(call_ref, Reg(pack.start.index() + offset)),
                                dataflow.defs.len(),
                                fixed_temps,
                                phi_temps,
                            )
                        })
                        .collect(),
                    ValuePack::Open(_) => Vec::new(),
                },
                layout,
                callee,
                assignment_copies: assignment_copies(proto, cfg, dataflow, fixed_temps, call_ref),
                fastcall_argument_copies: fastcall_argument_copies(
                    proto,
                    cfg,
                    dataflow,
                    epochs,
                    fixed_temps,
                    phi_temps,
                    call_ref,
                ),
                boolean_prewrites: dataflow
                    .use_values_at(call_ref)
                    .iter()
                    .filter_map(|(reg, value)| {
                        if reg.index() < args_start.index() {
                            return None;
                        }
                        let SsaValue::Phi(phi) = value else {
                            return None;
                        };
                        let &(initial, result) = prewrites.get(&phi)?;
                        Some(BooleanArgumentPrewrite {
                            argument: reg.index() - args_start.index(),
                            initial,
                            result,
                            home: HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, call_ref)),
                        })
                    })
                    .collect(),
            },
        );
    }
    calls
}

/// 原协议已区分快路径直读与 fallback 准备；非 direct 槽只有真实 MOVE 才有两路对应。
/// 源槽必须低于整个 CALL 区，并在 MOVE 到 CALL 间保留同一 SSA 值和捕获 epoch。
fn fastcall_argument_copies(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
    site: InstrRef,
) -> Vec<FastCallArgumentCopy> {
    let LowInstr::Call(call) = &proto.instrs[site.index()] else {
        return Vec::new();
    };
    let (crate::transformer::CallKind::FastCall(protocol), ValuePack::Fixed(args)) =
        (call.kind, call.args)
    else {
        return Vec::new();
    };
    (0..args.len)
        .filter_map(|argument| {
            if protocol.fixed_is_direct(argument) {
                return None;
            }
            let target = Reg(args.start.index() + argument);
            let SsaValue::Def(def) = dataflow.use_value(site, target) else {
                return None;
            };
            let producer = TempId(def.index());
            let write = dataflow.def_instr(def);
            let LowInstr::Move(copy) = &proto.instrs[write.index()] else {
                return None;
            };
            if fixed_temps[def.index()] != producer
                || dataflow.def_reg(def) != target
                || copy.dst != target
                || copy.src.index() >= call.callee.index()
                || write.index() >= site.index()
                || cfg.instr_to_block[write.index()] != cfg.instr_to_block[site.index()]
                || dataflow
                    .first_must_write_in_range(copy.src, write.index() + 1..site.index())
                    .is_some()
                || epochs.epoch_at(copy.src, write) != epochs.epoch_at(copy.src, site)
                || epochs.epoch_at(target, write) != epochs.epoch_at(target, site)
                || epochs.reference_capture_may_be_open(copy.src, write)
                || epochs.reference_capture_may_be_open(copy.src, site)
                || epochs.reference_capture_may_be_open(target, write)
                || epochs.reference_capture_may_be_open(target, site)
            {
                return None;
            }
            let source = canonical_value_temp(
                dataflow.use_value(write, copy.src),
                dataflow.defs.len(),
                fixed_temps,
                phi_temps,
            );
            Some(FastCallArgumentCopy {
                argument,
                producer,
                source,
                home: HomeSlotKey::new(target.index(), epochs.epoch_at(target, site)),
                source_home: HomeSlotKey::new(copy.src.index(), epochs.epoch_at(copy.src, site)),
            })
        })
        .collect()
}

/// 低槽初始化、callee COPY、单结果 CALL、写回组成同一源码赋值帧。
/// 保留两端 canonical 定义，使 `local x = f; x = x()` 的低槽不会在完整帧恢复前消失。
/// 此处只识别协议，不允许删除写入；实际槽序和剩余读取仍由完整事务核对。
fn assignment_copies(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
    site: InstrRef,
) -> Option<[TempId; 2]> {
    let index = site.index();
    let LowInstr::Call(call) = proto.instrs.get(index)? else {
        return None;
    };
    let LowInstr::Move(result) = proto.instrs.get(index + 1)? else {
        return None;
    };
    let SsaValue::Def(callee_def) = dataflow.use_value(site, call.callee) else {
        return None;
    };
    let callee_site = dataflow.def_instr(callee_def);
    let LowInstr::Move(callee) = proto.instrs.get(callee_site.index())? else {
        return None;
    };
    let SsaValue::Def(initial_def) = dataflow.use_value(callee_site, callee.src) else {
        return None;
    };
    let initial_site = dataflow.def_instr(initial_def);
    if result.src != call.callee
        || callee.dst != call.callee
        || result.dst != callee.src
        || dataflow.def_reg(initial_def) != callee.src
        || result.dst.index() >= call.callee.index()
        || !matches!(call.results, ResultPack::Fixed(pack) if pack.start == call.callee && pack.len == 1)
        || initial_site.index() >= callee_site.index()
        || callee_site.index() >= index
        || cfg.instr_to_block[initial_site.index()] != cfg.instr_to_block[index]
        || cfg.instr_to_block[callee_site.index()] != cfg.instr_to_block[index]
        || cfg.instr_to_block[index] != cfg.instr_to_block[index + 1]
    {
        return None;
    }
    let result = dataflow.instr_def_for_reg(InstrRef(index + 1), result.dst)?;
    // 只保留原低槽值与写回身份，初值可以来自 GETTABLE 的真实 Def（598）；并不将其
    // 求值移入高槽 CALL。两个端点的删除仍由完整帧 owner 核对原顺序、槽及后缀读取。
    let temps = [TempId(initial_def.index()), TempId(result.index())];
    (fixed_temps[initial_def.index()] == temps[0] && fixed_temps[result.index()] == temps[1])
        .then_some(temps)
}

/// 只消费已选中的值决策：各叶为原 Boolean 写，入口 false 与最终 phi 共享 result_reg。
/// 后层不能从 `a and b` 文本猜测这次预写；无入口预写的普通比较没有此项责任。
fn boolean_prewrites(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> BTreeMap<PhiId, (TempId, TempId)> {
    plan.value_decisions()
        .filter_map(|(_, decision)| {
            let header = decision.header()?;
            let mut initial = None;
            for leaf in &decision.leaves {
                let SsaValue::Def(def) = leaf.value else {
                    return None;
                };
                let LowInstr::LoadBool(value) = proto.instrs[dataflow.def_instr(def).index()]
                else {
                    return None;
                };
                if value.dst != decision.result_reg {
                    return None;
                }
                if dataflow.def_block(def) == header {
                    if value.value || leaf.latest_local_def != Some(def) {
                        return None;
                    }
                    if initial.is_some_and(|old| old != fixed_temps[def.index()]) {
                        return None;
                    }
                    initial = Some(fixed_temps[def.index()]);
                }
            }
            Some((
                decision.result_phi,
                (initial?, phi_temps[decision.result_phi.index()]),
            ))
        })
        .collect()
}

/// 同一共享 Dataflow 事实给出 call result 的独立 root 后缀终点；HIR 不从后缀文本猜 MOVE。
pub(super) fn collect_unobserved_result_ends(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    fixed_temps: &[TempId],
) -> BTreeMap<TempId, Vec<TempId>> {
    dataflow
        .defs
        .iter()
        .filter_map(|def| {
            let producer = TempId(def.id.index());
            if fixed_temps[def.id.index()] != producer
                || dataflow.reg_is_reference_captured(def.reg)
                || !matches!(proto.instrs[def.instr.index()], LowInstr::Call(_))
            {
                return None;
            }
            let ends = dataflow.unobserved_root_overwrite_frontier_after_last_use(def.id, cfg)?;
            let endpoints = ends
                .into_iter()
                .map(|end| {
                    let endpoint = TempId(end.index());
                    (fixed_temps[end.index()] == endpoint).then_some(endpoint)
                })
                .collect::<Option<Vec<_>>>()?;
            Some((producer, endpoints))
        })
        .collect()
}

/// 将 direct def 的 caller home 终点投影到精确调用；此前允许存在 GGET 等观察。
/// 终点属于物理槽而非 producer 的表达式种类；例如 LuaJIT 的 frame gap 也会结束 lookup 根。
/// 每个候选只加入、退休一次；CALL 按寄存器边界切走后缀，不逐调用重扫全部 definition。
pub(super) fn collect_frame_root_ends(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
) -> BTreeMap<InstrRef, Vec<TempId>> {
    let mut calls = BTreeMap::new();
    for &block in &cfg.block_order {
        let mut active = BTreeMap::<Reg, (TempId, usize)>::new();
        let range = cfg.blocks[block.index()].instrs;
        for index in range.start.index()..range.end() {
            let instr_ref = InstrRef(index);
            let instr = &proto.instrs[index];
            let observation = dataflow.effect_summaries[index].root_observation;
            let effect = &dataflow.instr_effects[index];
            if let RootObservation::Call { caller_end } = observation {
                let ended = active.split_off(&caller_end);
                // FASTCALL 可能在当前 frame 执行 builtin；只能使证书失效，不能签发终点。
                if matches!(instr, LowInstr::Call(call)
                    if !matches!(call.kind, crate::transformer::CallKind::FastCall(_)))
                {
                    let roots = ended
                        .into_iter()
                        .filter_map(|(reg, (temp, last_use))| {
                            (last_use < index
                                && !effect.uses_fixed(reg)
                                && effect.open_use.is_none_or(|start| reg < start))
                            .then_some(temp)
                        })
                        .collect::<Vec<_>>();
                    if !roots.is_empty() {
                        calls.insert(instr_ref, roots);
                    }
                }
            }
            match instr {
                LowInstr::Closure(closure) => {
                    for capture in &closure.captures {
                        if let CaptureSource::ByReference(reg) = capture.source {
                            active.remove(&reg);
                        }
                    }
                }
                LowInstr::Close(close) => {
                    active.split_off(&close.from);
                }
                LowInstr::GenericForCall(_) => {
                    // 迭代 dispatch 只发布有效前缀下界，不能证明高槽未经潜在覆盖。
                    if let RootObservation::PrefixLowerBound { end } = observation {
                        active.split_off(&Reg(end));
                    }
                }
                _ => {}
            }
            for reg in effect.fixed_must_defs() {
                active.remove(reg);
            }
            if let Some(start) = effect.open_must_def {
                active.split_off(&start);
            }
            for &def in &dataflow.instr_defs[index] {
                let producer = TempId(def.index());
                let reg = dataflow.def_reg(def);
                if fixed_temps[def.index()] != producer
                    || !dataflow.def_phi_uses[def.index()].is_empty()
                    || epochs.reference_capture_may_be_open(reg, instr_ref)
                {
                    continue;
                }
                // 当前 dispatch 的 callee/参数读取也必须排除；空 use 的固定多返回值仍有 home。
                let last_use =
                    dataflow.def_uses[def.index()]
                        .iter()
                        .try_fold(index, |last, use_| {
                            (use_.instr.index() > index
                                && cfg.instr_to_block[use_.instr.index()] == block)
                                .then_some(last.max(use_.instr.index()))
                        });
                if let Some(last_use) = last_use {
                    active.insert(reg, (producer, last_use));
                }
            }
        }
    }
    calls
}
