//! 保留操作输入树化前的一次原上值、字段读取或字面量准备。
//!
//! Dataflow 的 use→Def 将读取绑定到其消费者，而非给同名上值一个全局 home。
//! 例如 GETUPVAL r0 后原位 LEN r0，输入内联为 `#captured` 后仍能证明先写 r0；
//! 后续元方法或 CALL 的物理根义务由完整帧 owner 验证，不由这个入口证书提前退休。
//! 每次只查一个原 use 和其唯一 Def，比较、一元/二元、CONCAT 首项及动态索引
//! 共用相同身份和 epoch 检查。高槽 key 先于低槽 base 时，完整索引 owner 另保留两者顺序。
//! SETTABLE 目标若来自 GETTABLE，证书绑定精确读取来源且仅有这一个 use；
//! 多次使用的表变量不会误作可删除的目标快照，字段树的输入布局仍由帧 owner 逐层核对。

use crate::hir::common::{HirExpr, TempId, UpvalueId};
use crate::parser::RawLiteralConst;
use crate::structure::{Cfg, DataflowFacts, SsaValue};
use crate::transformer::{InstrRef, LowInstr, LoweredProto, Reg, UpvalueOperand};

use super::{HomeSlotKey, SlotEpochFacts};

#[derive(Debug, Clone)]
enum PreparedValue {
    TableRead(InstrRef),
    Upvalue(UpvalueId),
    Integer(i64),
    Number(f64),
    String(crate::LuaString),
}

#[derive(Debug, Clone)]
pub(super) struct OperandPreparation {
    pub(super) temp: TempId,
    pub(super) home: HomeSlotKey,
    pub(super) read: InstrRef,
    value: PreparedValue,
}

/// 原动态索引先在高槽准备 key，再在结果槽准备 base；两次读取属于同一 GETTABLE。
#[derive(Debug, Clone)]
pub(super) struct TablePreparation {
    pub(super) base: OperandPreparation,
    pub(super) key: OperandPreparation,
}

impl OperandPreparation {
    pub(super) fn matches(&self, value: &HirExpr) -> bool {
        match (&self.value, value) {
            (PreparedValue::TableRead(read), HirExpr::TableAccess(access)) => {
                matches!(access.sources, crate::hir::common::HirOperationSources::Single(source)
                    if source.instr == *read)
            }
            (PreparedValue::Upvalue(original), HirExpr::UpvalueRef(current)) => original == current,
            (PreparedValue::Integer(original), HirExpr::Integer(current)) => original == current,
            (PreparedValue::Number(original), HirExpr::Number(current)) => {
                original.to_bits() == current.to_bits()
            }
            (PreparedValue::String(original), HirExpr::String(current)) => original == current,
            _ => false,
        }
    }
}

pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    epochs: &SlotEpochFacts,
    fixed_temps: &[TempId],
    site: InstrRef,
    reg: Reg,
) -> Option<OperandPreparation> {
    let SsaValue::Def(def) = dataflow.use_value(site, reg) else {
        return None;
    };
    let temp = TempId(def.index());
    let uses = &dataflow.def_uses[def.index()];
    if fixed_temps[def.index()] != temp
        || dataflow.def_reg(def) != reg
        || uses.len() != 1
        || uses[0].instr != site
        || !dataflow.def_phi_uses[def.index()].is_empty()
        || dataflow.def_block(def) != cfg.instr_to_block[site.index()]
    {
        return None;
    }
    let read = dataflow.def_instr(def);
    let home = HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, site));
    if epochs.epoch_at(reg, read) != home.epoch
        || epochs.reference_capture_may_be_open(reg, read)
        || epochs.reference_capture_may_be_open(reg, site)
    {
        return None;
    }
    let value = match &proto.instrs[read.index()] {
        LowInstr::GetTable(_) => PreparedValue::TableRead(read),
        LowInstr::GetUpvalue(get) => {
            let (UpvalueOperand::Env(upvalue) | UpvalueOperand::Upvalue(upvalue)) = get.src;
            PreparedValue::Upvalue(UpvalueId(upvalue.index()))
        }
        LowInstr::LoadInteger(load) => PreparedValue::Integer(load.value),
        LowInstr::LoadNumber(load) => PreparedValue::Number(load.value),
        LowInstr::LoadConst(load) => match &proto.constants[load.value.index()] {
            RawLiteralConst::Integer(value) => PreparedValue::Integer(*value),
            RawLiteralConst::Number(value) => PreparedValue::Number(*value),
            RawLiteralConst::String(value) => {
                PreparedValue::String(crate::LuaString::from_raw(value))
            }
            _ => return None,
        },
        _ => return None,
    };
    Some(OperandPreparation {
        temp,
        home,
        read,
        value,
    })
}
