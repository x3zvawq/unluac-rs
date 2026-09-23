//! 冻结 CALL 的 caller 槽交接、结果覆盖与 dispatch 终点事实。
//!
//! 消费 Dataflow 调用边界、canonical Def 与完整覆盖 frontier，分别保留布局、
//! 值版本及捕获状态；实际 producer 删除仍由 HIR 求值顺序 owner 证明。
//! 例如 f(owner) 的参数槽可交给 callee，owner 的原低槽不随参数 COPY 交出。
//! 同值的 callee/receiver 准备与结果写回仍是不同物理事件。

use super::*;
use crate::hir::common::HirCallArgumentRoot;
use crate::transformer::ValuePack;

/// 同一原始 CALL 索引下共享参数根与完整调用布局，避免后层按方言重解槽距。
#[derive(Debug, Clone)]
pub(super) struct NativeCallFacts {
    pub(super) argument_roots: Vec<HirCallArgumentRoot>,
    pub(super) argument_values: Vec<Option<TempId>>,
    pub(super) argument_preparations: BTreeMap<usize, operand_preparations::OperandPreparation>,
    pub(super) argument_copies: BTreeMap<usize, NativeArgumentCopy>,
    pub(super) fixed_results: Option<Vec<TempId>>,
    pub(super) vararg_tail_home: Option<HomeSlotKey>,
    pub(super) layout: NativeCallLayout,
    pub(super) callee: Option<TempId>,
    pub(super) assignment_copies: Option<[TempId; 3]>,
    pub(super) scalar_assignment: Option<NativeScalarAssignment>,
    pub(super) result_writebacks: Option<Vec<NativeResultWriteback>>,
    pub(super) boolean_prewrites: Vec<BooleanArgumentPrewrite>,
    pub(super) fastcall_argument_copies: Vec<FastCallArgumentCopy>,
    pub(super) fastcall_callee_before_copies: bool,
}

/// 普通 CALL 参数的最后一次 MOVE；两端 Def 与时点独立于已合并的展示 Local。
#[derive(Debug, Clone, Copy)]
pub(in crate::hir) struct NativeArgumentCopy {
    pub(in crate::hir) source: TempId,
    pub(in crate::hir) target: TempId,
    pub(in crate::hir) source_home: HomeSlotKey,
    pub(in crate::hir) target_home: HomeSlotKey,
    pub(in crate::hir) instruction: InstrRef,
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

/// 原入口 Boolean 写与结果 phi 属于同一参数槽；仅完整值帧可重发这次写。
#[derive(Debug, Clone, Copy)]
pub(in crate::hir) struct BooleanArgumentPrewrite {
    pub(in crate::hir) argument: usize,
    pub(in crate::hir) initial: TempId,
    pub(in crate::hir) initial_value: bool,
    pub(in crate::hir) result: TempId,
    pub(in crate::hir) home: HomeSlotKey,
    /// 槽仅有值捕获时，其它值版本的快照不能观察这次 Boolean 写回。
    pub(in crate::hir) reference_uncaptured: bool,
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
    /// 固定结果写入时没有打开的引用 cell；旧值的 ByValue 快照不观察新结果。
    pub(in crate::hir) fixed_results_unaliased: bool,
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

/// 固定单结果 CALL 后先向低槽写惰性常量，再将结果 COPY 到另一低槽。
/// 例如 `a,b=f(),9`；三个 canonical Def 保留原写序，不能以最终槽号猜出赋值协议。
#[derive(Debug, Clone, Copy)]
pub(in crate::hir) struct NativeScalarAssignment {
    pub(in crate::hir) result: TempId,
    pub(in crate::hir) scalar: TempId,
    pub(in crate::hir) writeback: TempId,
    pub(in crate::hir) scalar_home: HomeSlotKey,
    pub(in crate::hir) target_home: HomeSlotKey,
    pub(in crate::hir) value: CopyRootScalarValue,
}

/// 固定结果 CALL 后连续的原 MOVE，按执行顺序保留结果位置、写入 Def 和目标 cell。
/// 这是原指令事实；HIR 的并行 Phi 转移不能自行重建其写序。
#[derive(Debug, Clone, Copy)]
pub(in crate::hir) struct NativeResultWriteback {
    pub(in crate::hir) result_index: usize,
    pub(in crate::hir) writeback: TempId,
    /// COPY 覆盖的原定义，供声明 owner 连接初始化；不以相同槽号猜 binding。
    pub(in crate::hir) previous: Option<TempId>,
    pub(in crate::hir) target_home: HomeSlotKey,
}

pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
    prewrites: &BTreeMap<PhiId, (TempId, TempId, bool)>,
) -> BTreeMap<InstrRef, NativeCallFacts> {
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
            fixed_results_unaliased: matches!(results, Some(ResultPack::Fixed(pack))
                if (pack.start.index()..pack.start.index() + pack.len)
                    .all(|slot| !epochs.reference_capture_may_be_open(Reg(slot), call_ref))),
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
        let fastcall_argument_copies = fastcall_argument_copies(
            proto,
            cfg,
            dataflow,
            epochs,
            fixed_temps,
            phi_temps,
            call_ref,
        );
        // 固定前缀加 VARARG 的 fallback 可先查找 callee，再 COPY 低槽参数。
        // 保存原 Def 顺序；消费者不能把普通 FASTCALL 的 lookup-after-copy 顺序硬套进来。
        let fastcall_callee_before_copies = !fastcall_argument_copies.is_empty()
            && callee.is_some_and(|callee| {
                callee.index() < dataflow.defs.len()
                    && fastcall_argument_copies.iter().all(|copy| {
                        dataflow.def_instr(crate::structure::DefId(callee.index()))
                            < dataflow.def_instr(crate::structure::DefId(copy.producer.index()))
                    })
            });
        calls.insert(
            call_ref,
            NativeCallFacts {
                argument_roots: roots,
                argument_copies: dataflow
                    .use_values_at(call_ref)
                    .iter()
                    .filter(|(reg, _)| reg.index() >= args_start.index())
                    .filter_map(|(reg, value)| {
                        let SsaValue::Def(target) = value else {
                            return None;
                        };
                        let instruction = dataflow.def_instr(target);
                        let LowInstr::Move(copy) = &proto.instrs[instruction.index()] else {
                            return None;
                        };
                        let SsaValue::Def(source) = dataflow.use_value(instruction, copy.src)
                        else {
                            return None;
                        };
                        if copy.dst != reg
                            || fixed_temps[target.index()] != TempId(target.index())
                            || fixed_temps[source.index()] != TempId(source.index())
                            || cfg.instr_to_block[instruction.index()]
                                != cfg.instr_to_block[call_ref.index()]
                            || epochs.reference_capture_may_be_open(copy.src, instruction)
                            || epochs.reference_capture_may_be_open(copy.dst, instruction)
                        {
                            return None;
                        }
                        Some((
                            reg.index() - args_start.index(),
                            NativeArgumentCopy {
                                source: TempId(source.index()),
                                target: TempId(target.index()),
                                source_home: HomeSlotKey::new(
                                    copy.src.index(),
                                    epochs.epoch_at(copy.src, instruction),
                                ),
                                target_home: HomeSlotKey::new(
                                    copy.dst.index(),
                                    epochs.epoch_at(copy.dst, instruction),
                                ),
                                instruction,
                            },
                        ))
                    })
                    .collect(),
                argument_preparations: dataflow
                    .use_values_at(call_ref)
                    .iter()
                    .filter(|(reg, _)| reg.index() >= args_start.index())
                    .filter_map(|(reg, _)| {
                        Some((
                            reg.index() - args_start.index(),
                            operand_preparations::collect(
                                proto,
                                cfg,
                                dataflow,
                                epochs,
                                fixed_temps,
                                call_ref,
                                reg,
                            )?,
                        ))
                    })
                    .collect(),
                fixed_results: match layout.results {
                    Some(ResultPack::Fixed(pack))
                        if dataflow.instr_defs[index].len() == pack.len =>
                    {
                        dataflow.instr_defs[index]
                            .iter()
                            .enumerate()
                            .map(|(offset, def)| {
                                let temp = TempId(def.index());
                                (dataflow.def_reg(*def).index() == pack.start.index() + offset
                                    && fixed_temps[def.index()] == temp)
                                    .then_some(temp)
                            })
                            .collect()
                    }
                    _ => None,
                },
                vararg_tail_home: match args {
                    ValuePack::Open(_) => {
                        let sources = &dataflow.open_use_sources[index];
                        if !sources.has_entry() && sources.defs().len() == 1 {
                            let def = &dataflow.open_defs[sources.defs().first().unwrap().index()];
                            // 原开放包必须直接来自同块的最后一条 VARARG，不能把 CALL
                            // 返回包或跨路径 pack phi 当作源码中的直接省略号。
                            (def.block == cfg.instr_to_block[index]
                                && def.instr.index() + 1 == index
                                && matches!(proto.instrs[def.instr.index()], LowInstr::VarArg(_)))
                            .then_some(HomeSlotKey::new(
                                def.start_reg.index(),
                                epochs.epoch_at(def.start_reg, call_ref),
                            ))
                        } else {
                            None
                        }
                    }
                    ValuePack::Fixed(_) => None,
                },
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
                    // Open SSA use map 只包含已证明的连续固定前缀；动态尾没有逐槽 Def。
                    // TAILCALL 同样需要这些值版本，不能因不签发参数根交接而丢弃布局事实。
                    ValuePack::Open(start) => dataflow
                        .use_values_at(call_ref)
                        .iter()
                        .filter(|(reg, _)| reg.index() >= start.index())
                        .map(|(_, value)| {
                            canonical_value_temp(value, dataflow.defs.len(), fixed_temps, phi_temps)
                        })
                        .collect(),
                },
                layout,
                callee,
                assignment_copies: assignment_copies(proto, cfg, dataflow, fixed_temps, call_ref),
                scalar_assignment: scalar_assignment(
                    proto,
                    cfg,
                    dataflow,
                    epochs,
                    fixed_temps,
                    call_ref,
                ),
                result_writebacks: result_writebacks(proto, cfg, dataflow, epochs, call_ref),
                fastcall_argument_copies,
                fastcall_callee_before_copies,
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
                        let &(initial, result, initial_value) = prewrites.get(&phi)?;
                        Some(BooleanArgumentPrewrite {
                            argument: reg.index() - args_start.index(),
                            initial,
                            initial_value,
                            result,
                            home: HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, call_ref)),
                            reference_uncaptured: !dataflow.reg_is_reference_captured(reg),
                        })
                    })
                    .collect(),
            },
        );
    }
    calls
}

fn result_writebacks(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    site: InstrRef,
) -> Option<Vec<NativeResultWriteback>> {
    let LowInstr::Call(call) = &proto.instrs[site.index()] else {
        return None;
    };
    let ResultPack::Fixed(pack) = call.results else {
        return None;
    };
    if pack.len < 2 || pack.start != call.callee {
        return None;
    }
    let mut writes = Vec::with_capacity(pack.len);
    let mut sources = BTreeSet::new();
    let mut targets = BTreeSet::new();
    for offset in 0..pack.len {
        let copy_site = InstrRef(site.index() + offset + 1);
        let LowInstr::Move(copy) = proto.instrs.get(copy_site.index())? else {
            return None;
        };
        let result_index = copy.src.index().checked_sub(pack.start.index())?;
        if result_index >= pack.len
            || copy.dst.index() >= pack.start.index()
            || cfg.instr_to_block[copy_site.index()] != cfg.instr_to_block[site.index()]
            || !sources.insert(copy.src)
            || !targets.insert(copy.dst)
            || epochs.reference_capture_may_be_open(copy.dst, copy_site)
        {
            return None;
        }
        let result = dataflow.instr_def_for_reg(site, copy.src)?;
        if dataflow.use_value(copy_site, copy.src) != SsaValue::Def(result) {
            return None;
        }
        let writeback = dataflow.instr_def_for_reg(copy_site, copy.dst)?;
        writes.push(NativeResultWriteback {
            result_index,
            writeback: TempId(writeback.index()),
            previous: match dataflow.def_overwritten_value(writeback) {
                Some(SsaValue::Def(def)) => Some(TempId(def.index())),
                _ => None,
            },
            target_home: HomeSlotKey::new(copy.dst.index(), epochs.epoch_at(copy.dst, copy_site)),
        });
    }
    Some(writes)
}

/// 原协议已区分快路径直读与 fallback 准备；非 direct 槽只有真实 MOVE 才有两路对应。
/// 源槽必须低于整个 CALL 区，并在 MOVE 到 CALL 间保持位置与捕获 epoch。
/// 开放 cell 的读取只有槽身份，不发布 canonical 值快照；完整帧仍在原 fallback
/// 时点重发 COPY，不能据此把它移动到 direct 参数的可观察求值之前。
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
    let crate::transformer::CallKind::FastCall(protocol) = call.kind else {
        return Vec::new();
    };
    let args = match call.args {
        ValuePack::Fixed(args) => args,
        ValuePack::Open(start) => crate::transformer::RegRange {
            start,
            len: dataflow
                .use_values_at(site)
                .iter()
                .filter(|(reg, _)| reg.index() >= start.index())
                .count(),
        },
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
                || epochs.reference_capture_may_be_open(target, write)
                || epochs.reference_capture_may_be_open(target, site)
            {
                return None;
            }
            let source = if epochs.reference_capture_may_be_open(copy.src, write)
                || epochs.reference_capture_may_be_open(copy.src, site)
            {
                None
            } else {
                canonical_value_temp(
                    dataflow.use_value(write, copy.src),
                    dataflow.defs.len(),
                    fixed_temps,
                    phi_temps,
                )
            };
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

/// 每个 CALL 只检查两个相邻指令，不按候选重扫后缀。只接受无求值的标量写，
/// 任一分支边界、额外结果读取或非 canonical 定义都不产生完整赋值事实。
fn scalar_assignment(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    site: InstrRef,
) -> Option<NativeScalarAssignment> {
    let index = site.index();
    let LowInstr::Call(call) = proto.instrs.get(index)? else {
        return None;
    };
    let scalar_site = InstrRef(index + 1);
    let copy_site = InstrRef(index + 2);
    let scalar_instr = proto.instrs.get(scalar_site.index())?;
    let scalar_reg = match scalar_instr {
        LowInstr::LoadNil(load) if load.dst.len == 1 => load.dst.start,
        LowInstr::LoadBool(load) => load.dst,
        LowInstr::LoadInteger(load) => load.dst,
        LowInstr::LoadNumber(load) => load.dst,
        _ => return None,
    };
    let value = direct_scalar_overwrite_value(scalar_instr, scalar_reg)?;
    let LowInstr::Move(copy) = proto.instrs.get(copy_site.index())? else {
        return None;
    };
    if !matches!(call.results, ResultPack::Fixed(pack)
        if pack.start == call.callee && pack.len == 1)
        || copy.src != call.callee
        || copy.dst == scalar_reg
        || copy.dst.index() >= call.callee.index()
        || scalar_reg.index() >= call.callee.index()
        || cfg.instr_to_block[index] != cfg.instr_to_block[scalar_site.index()]
        || cfg.instr_to_block[index] != cfg.instr_to_block[copy_site.index()]
        || epochs.reference_capture_may_be_open(scalar_reg, scalar_site)
        || epochs.reference_capture_may_be_open(copy.dst, copy_site)
    {
        return None;
    }
    let result = dataflow.instr_def_for_reg(site, call.callee)?;
    let scalar = dataflow.instr_def_for_reg(scalar_site, scalar_reg)?;
    let writeback = dataflow.instr_def_for_reg(copy_site, copy.dst)?;
    if dataflow.use_value(copy_site, copy.src) != SsaValue::Def(result)
        || !dataflow.def_phi_uses[result.index()].is_empty()
        || !matches!(dataflow.def_uses[result.index()].as_slice(), [use_] if use_.instr == copy_site)
        || [result, scalar, writeback]
            .iter()
            .any(|def| fixed_temps[def.index()] != TempId(def.index()))
    {
        return None;
    }
    Some(NativeScalarAssignment {
        result: TempId(result.index()),
        scalar: TempId(scalar.index()),
        writeback: TempId(writeback.index()),
        scalar_home: HomeSlotKey::new(scalar_reg.index(), epochs.epoch_at(scalar_reg, scalar_site)),
        target_home: HomeSlotKey::new(copy.dst.index(), epochs.epoch_at(copy.dst, copy_site)),
        value,
    })
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
) -> Option<[TempId; 3]> {
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
    let (copy_site, callee) = match proto.instrs.get(callee_site.index())? {
        LowInstr::Move(copy) => (callee_site, copy),
        LowInstr::GetTable(access) if call.kind == crate::transformer::CallKind::Method => {
            let crate::transformer::AccessBase::Reg(receiver) = access.base else {
                return None;
            };
            let SsaValue::Def(receiver_def) = dataflow.use_value(callee_site, receiver) else {
                return None;
            };
            let copy_site = dataflow.def_instr(receiver_def);
            let LowInstr::Move(copy) = proto.instrs.get(copy_site.index())? else {
                return None;
            };
            if copy.dst != receiver || copy_site.index() >= callee_site.index() {
                return None;
            }
            (copy_site, copy)
        }
        _ => return None,
    };
    let SsaValue::Def(initial_def) = dataflow.use_value(copy_site, callee.src) else {
        return None;
    };
    let initial_site = dataflow.def_instr(initial_def);
    if result.src != call.callee
        || (call.kind != crate::transformer::CallKind::Method && callee.dst != call.callee)
        || result.dst != callee.src
        || dataflow.def_reg(initial_def) != callee.src
        || result.dst.index() >= call.callee.index()
        || !matches!(call.results, ResultPack::Fixed(pack) if pack.start == call.callee && pack.len == 1)
        || initial_site.index() >= copy_site.index()
        || callee_site.index() >= index
        || cfg.instr_to_block[initial_site.index()] != cfg.instr_to_block[index]
        || cfg.instr_to_block[callee_site.index()] != cfg.instr_to_block[index]
        || cfg.instr_to_block[copy_site.index()] != cfg.instr_to_block[index]
        || cfg.instr_to_block[index] != cfg.instr_to_block[index + 1]
    {
        return None;
    }
    let result = dataflow.instr_def_for_reg(InstrRef(index + 1), result.dst)?;
    // 初值、准备 COPY 与结果写回分别保留真实 Def；初值可以来自 GETTABLE，不能将其
    // 求值移入高槽 CALL。三者的删除由完整帧 owner 核对原顺序、槽及后缀读取。
    let preparation = dataflow.instr_def_for_reg(copy_site, callee.dst)?;
    let defs = [initial_def, preparation, result];
    defs.iter()
        .all(|def| fixed_temps[def.index()] == TempId(def.index()))
        .then(|| defs.map(|def| TempId(def.index())))
}

/// 冻结入口 Boolean 与同槽结果 phi；已选值决策直接提供配对，未树化的前向合流
/// 则由原 Def 支配关系证明。此事实不授权折叠控制树，后层仍须重发整个参数帧。
pub(super) fn boolean_prewrites(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    graph: &GraphFacts,
    plan: &StructurePlan,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> BTreeMap<PhiId, (TempId, TempId, bool)> {
    let mut prewrites = plan
        .value_decisions()
        .filter_map(|(_, decision)| {
            let header = decision.header()?;
            let mut initial = None;
            for leaf in &decision.leaves {
                let SsaValue::Def(def) = leaf.value else {
                    return None;
                };
                if dataflow.def_reg(def) != decision.result_reg {
                    return None;
                }
                if dataflow.def_block(def) == header {
                    let LowInstr::LoadBool(value) = proto.instrs[dataflow.def_instr(def).index()]
                    else {
                        return None;
                    };
                    if fixed_temps[def.index()] != TempId(def.index()) {
                        return None;
                    }
                    if initial.is_some_and(|old| old != (fixed_temps[def.index()], value.value)) {
                        return None;
                    }
                    initial = Some((fixed_temps[def.index()], value.value));
                }
                // `predicate and/or table.field` 的末叶保留任意字段值；它仍与入口 Boolean
                // 共用结果槽。预写身份不要求所有叶都是 Boolean，后层仍完整重发每个叶。
            }
            if phi_temps[decision.result_phi.index()]
                != TempId(fixed_temps.len() + decision.result_phi.index())
            {
                return None;
            }
            let (initial, initial_value) = initial?;
            Some((
                decision.result_phi,
                (
                    initial,
                    phi_temps[decision.result_phi.index()],
                    initial_value,
                ),
            ))
        })
        .collect::<BTreeMap<_, _>>();
    for (_, decision) in plan.value_decisions() {
        for operand in &decision.operands {
            let phi = &dataflow.phi_candidates[operand.phi.index()];
            let header = decision.nodes[operand.entry.index()].block;
            let initial = operand.leaves.values().find_map(|value| {
                let SsaValue::Def(def) = *value else {
                    return None;
                };
                if dataflow.def_block(def) != header || dataflow.def_reg(def) != phi.reg {
                    return None;
                }
                let LowInstr::LoadBool(load) = proto.instrs[dataflow.def_instr(def).index()] else {
                    return None;
                };
                (fixed_temps[def.index()] == TempId(def.index()))
                    .then_some((fixed_temps[def.index()], load.value))
            });
            // 操作数与外层结果各自占原槽；入口预写即使来自同一 header，也不能
            // 只把最外层预写登记为 CALL 参数而遗失内部值树的覆盖事件。
            if let Some((initial, value)) = initial
                && phi_temps[phi.id.index()] == TempId(fixed_temps.len() + phi.id.index())
            {
                prewrites.insert(phi.id, (initial, phi_temps[phi.id.index()], value));
            }
        }
    }
    for phi in plan.phis() {
        if prewrites.contains_key(&phi.phi)
            || dataflow.phi_candidates[phi.phi.index()]
                .incoming
                .iter()
                .any(|incoming| {
                    incoming
                        .pred
                        .is_some_and(|pred| graph.dominates(phi.block, pred))
                })
            || phi.has_unresolved()
            || phi_temps[phi.phi.index()] != TempId(fixed_temps.len() + phi.phi.index())
        {
            continue;
        }
        // 展开调用可能让准备区跨越多个基本块；最早的 Boolean Def 仍须支配
        // 每个分支结果和合流点。循环体内的前向合流同样成立，但回边 phi
        // 会跨迭代携带值，不能领取当前准备区的初始化证明。
        let Some(defs) = phi
            .incomings
            .iter()
            .map(|incoming| {
                let SsaValue::Def(def) = incoming.value else {
                    return None;
                };
                (fixed_temps[def.index()] == TempId(def.index())
                    && dataflow.def_reg(def) == phi.reg)
                    .then_some(def)
            })
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        let Some(&initial) = defs.iter().min_by_key(|&&def| dataflow.def_instr(def)) else {
            continue;
        };
        let initial_block = dataflow.def_block(initial);
        let LowInstr::LoadBool(value) = proto.instrs[dataflow.def_instr(initial).index()] else {
            continue;
        };
        if !graph.dominates(initial_block, phi.block)
            || defs
                .iter()
                .any(|&def| !graph.dominates(initial_block, dataflow.def_block(def)))
        {
            continue;
        }
        prewrites.insert(
            phi.phi,
            (
                fixed_temps[initial.index()],
                phi_temps[phi.phi.index()],
                value.value,
            ),
        );
    }
    prewrites
}

/// 合流后的首条 MOVE 是显式结果写回；其它语句或跨块 COPY 不属于这份事实。
pub(super) fn value_result_copies(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    plan: &StructurePlan,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> BTreeMap<TempId, ImmediateMoveWrite> {
    plan.phis()
        .filter_map(|phi| {
            let result = canonical_value_temp(
                SsaValue::Phi(phi.phi),
                fixed_temps.len(),
                fixed_temps,
                phi_temps,
            )?;
            let instr = cfg.blocks[phi.block.index()].instrs.start;
            let LowInstr::Move(copy) = proto.instrs[instr.index()] else {
                return None;
            };
            if copy.src != phi.reg || dataflow.use_value(instr, copy.src) != SsaValue::Phi(phi.phi)
            {
                return None;
            }
            let [def] = dataflow.instr_defs[instr.index()].as_slice() else {
                return None;
            };
            let target = canonical_value_temp(
                SsaValue::Def(*def),
                fixed_temps.len(),
                fixed_temps,
                phi_temps,
            )?;
            Some((
                result,
                ImmediateMoveWrite {
                    source: Some(result),
                    target,
                    source_home: HomeSlotKey::new(
                        copy.src.index(),
                        epochs.epoch_at(copy.src, instr),
                    ),
                    target_home: HomeSlotKey::new(
                        copy.dst.index(),
                        epochs.epoch_at(copy.dst, instr),
                    ),
                },
            ))
        })
        .collect()
}

/// 值决策入口的 MOVE 与结果 phi 同槽；后层必须连同完整短路值树重发这次准备。
pub(super) fn copy_prewrites(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    fixed_temps: &[TempId],
    phi_temps: &[TempId],
) -> BTreeMap<TempId, TempId> {
    let mut copies = BTreeMap::new();
    let mut record = |header, reg, phi: PhiId, leaves: Vec<SsaValue>| {
        let mut initial = None;
        for leaf in leaves {
            let SsaValue::Def(def) = leaf else { continue };
            if dataflow.def_block(def) != header || dataflow.def_reg(def) != reg {
                continue;
            }
            if !matches!(
                proto.instrs[dataflow.def_instr(def).index()],
                LowInstr::Move(_)
            ) || fixed_temps[def.index()] != TempId(def.index())
                || initial.is_some_and(|old| old != fixed_temps[def.index()])
            {
                return;
            }
            initial = Some(fixed_temps[def.index()]);
        }
        let result = phi_temps[phi.index()];
        if result == TempId(fixed_temps.len() + phi.index())
            && let Some(initial) = initial
        {
            copies.insert(result, initial);
        }
    };
    for (_, decision) in plan.value_decisions() {
        if let Some(header) = decision.header() {
            record(
                header,
                decision.result_reg,
                decision.result_phi,
                decision.leaves.iter().map(|leaf| leaf.value).collect(),
            );
        }
        for operand in &decision.operands {
            record(
                decision.nodes[operand.entry.index()].block,
                dataflow.phi_candidates[operand.phi.index()].reg,
                operand.phi,
                operand.leaves.values().copied().collect(),
            );
        }
    }
    copies
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
