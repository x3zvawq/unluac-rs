//! 语言级数据流摘要：副作用分类、开放多值包配对、捕获事实与 Debug 绑定提示。
//!
//! 只计算直接影响 Lua 语言级语义的事实，彻底剥离物理栈槽/弱表 GC 残值模型。

use std::collections::BTreeMap;

use crate::transformer::{
    GetTableKind, InstrRef, LowInstr, LoweredProto, Reg, ResultPack, ValuePack,
};

use super::cfg::Cfg;
use super::ssa::{SlotKey, SsaForm, collect_debug_slot_hints};

/// 指令副作用分类，用于表达式树化与安全内联判定。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectClass {
    /// 纯值构造，不读取可变状态、不触发元方法（如字面量、NewTable、Closure）。
    Pure,
    /// 读取可变环境/上值/原始表槽，不写入也不触发元方法（受后续写入影响）。
    ReadsState,
    /// 可能写入状态、抛错或触发元方法（Call、表读写、算术/比较/拼接/#、SetUpvalue、Close 等）。
    MayObserveOrWrite,
}

/// 开放多值包生产-消费配对（`CALL`/`VARARG` -> `CALL`/`TAILCALL`/`RETURN`/`SETLIST`）。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OpenPackLink {
    pub producer: InstrRef,
    pub consumer: InstrRef,
    pub start: Reg,
}

/// 单个 proto 的紧凑数据流事实。
#[derive(Debug, Clone)]
pub struct DataflowFacts {
    /// 按指令索引存放副作用级别。
    pub effects: Vec<EffectClass>,
    /// 开放结果包：producer -> consumer。
    pub open_pack_by_producer: BTreeMap<InstrRef, OpenPackLink>,
    /// 开放结果包：consumer -> producer。
    pub open_pack_by_consumer: BTreeMap<InstrRef, OpenPackLink>,
    /// 源码 debug local 名称提示（按 SlotKey 索引）。
    pub debug_slot_hints: BTreeMap<SlotKey, String>,
}

/// 按 Lua 语言语义对单条 LowInstr 分类副作用。
pub fn classify_effect(instr: &LowInstr) -> EffectClass {
    match instr {
        LowInstr::Move(_)
        | LowInstr::LoadNil(_)
        | LowInstr::LoadBool(_)
        | LowInstr::LoadConst(_)
        | LowInstr::LoadInteger(_)
        | LowInstr::LoadNumber(_)
        | LowInstr::NewTable(_)
        | LowInstr::Closure(_)
        | LowInstr::Jump(_) => EffectClass::Pure,

        LowInstr::GetUpvalue(_) => EffectClass::ReadsState,
        LowInstr::GetTable(gt) if gt.kind == GetTableKind::Raw => EffectClass::ReadsState,

        // `not` 在 Lua 中永不触发元方法，纯求真值。
        LowInstr::UnaryOp(u) if u.op == crate::transformer::UnaryOpKind::Not => EffectClass::Pure,

        // 其余运算、表访问、调用、关闭、控制守卫都可能观察副作用或触发元方法。
        LowInstr::UnaryOp(_)
        | LowInstr::BinaryOp(_)
        | LowInstr::Concat(_)
        | LowInstr::SetUpvalue(_)
        | LowInstr::GetTable(_)
        | LowInstr::SetTable(_)
        | LowInstr::ErrNil(_)
        | LowInstr::TypeGuard(_)
        | LowInstr::SetList(_)
        | LowInstr::Call(_)
        | LowInstr::TailCall(_)
        | LowInstr::VarArg(_)
        | LowInstr::Return(_)
        | LowInstr::Close(_)
        | LowInstr::Tbc(_)
        | LowInstr::NumericForInit(_)
        | LowInstr::NumericForLoop(_)
        | LowInstr::GenericForPrep(_)
        | LowInstr::GenericForCall(_)
        | LowInstr::GenericForLoop(_)
        | LowInstr::Branch(_) => EffectClass::MayObserveOrWrite,
    }
}

/// 扫描每个基本块，配对 `ResultPack::Open` 生产者与 `ValuePack::Open` 消费者。
pub(crate) fn compute_open_pack_links(
    proto: &LoweredProto,
    cfg: &Cfg,
) -> (BTreeMap<InstrRef, OpenPackLink>, BTreeMap<InstrRef, OpenPackLink>) {
    let mut open_pack_by_producer = BTreeMap::new();
    let mut open_pack_by_consumer = BTreeMap::new();

    for &block in &cfg.block_order {
        let mut active_open: Option<(InstrRef, Reg)> = None;
        for iref in cfg.blocks[block.index()].instrs.iter() {
            let instr = &proto.instrs[iref.index()];
            let consumes_open = match instr {
                LowInstr::Call(c) => match c.args {
                    ValuePack::Open(r) => Some(r),
                    ValuePack::Fixed(_) => None,
                },
                LowInstr::TailCall(c) => match c.args {
                    ValuePack::Open(r) => Some(r),
                    ValuePack::Fixed(_) => None,
                },
                LowInstr::Return(r) => match r.values {
                    ValuePack::Open(reg) => Some(reg),
                    ValuePack::Fixed(_) => None,
                },
                LowInstr::SetList(s) => match s.values {
                    ValuePack::Open(reg) => Some(reg),
                    ValuePack::Fixed(_) => None,
                },
                _ => None,
            };
            if let Some(consume_start) = consumes_open
                && let Some((producer, prod_start)) = active_open.take()
                && prod_start.index() >= consume_start.index()
            {
                let link = OpenPackLink {
                    producer,
                    consumer: iref,
                    start: prod_start,
                };
                open_pack_by_producer.insert(producer, link);
                open_pack_by_consumer.insert(iref, link);
            }

            let produces_open = match instr {
                LowInstr::Call(c) => match c.results {
                    ResultPack::Open(r) => Some(r),
                    ResultPack::Fixed(_) | ResultPack::Ignore => None,
                },
                LowInstr::VarArg(v) => match v.results {
                    ResultPack::Open(r) => Some(r),
                    ResultPack::Fixed(_) | ResultPack::Ignore => None,
                },
                _ => None,
            };
            if let Some(start) = produces_open {
                active_open = Some((iref, start));
            }
        }
    }

    (open_pack_by_producer, open_pack_by_consumer)
}

/// 构建单个 proto 的数据流摘要。
pub(crate) fn compute_dataflow(
    proto: &LoweredProto,
    cfg: &Cfg,
    ssa: &SsaForm,
    open_pack_by_producer: BTreeMap<InstrRef, OpenPackLink>,
    open_pack_by_consumer: BTreeMap<InstrRef, OpenPackLink>,
) -> DataflowFacts {
    let effects = proto.instrs.iter().map(classify_effect).collect();
    let debug_slot_hints = collect_debug_slot_hints(proto, cfg, ssa);

    DataflowFacts {
        effects,
        open_pack_by_producer,
        open_pack_by_consumer,
        debug_slot_hints,
    }
}
