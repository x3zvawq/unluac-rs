//! 保留操作输入树化前的原准备写入身份。
//!
//! 消费 Dataflow 的 use/Def、home 与 epoch，为完整帧 owner 发布来源证书；
//! 证书本身不授权删除 producer 或提前退休物理根。

use crate::hir::common::{HirExpr, TempId, UpvalueId};
use crate::parser::RawLiteralConst;
use crate::structure::{Cfg, DataflowFacts, SsaValue};
use crate::transformer::{InstrRef, LowInstr, LoweredProto, Reg, UpvalueOperand};

use super::{HomeSlotKey, SlotEpochFacts};

#[derive(Debug, Clone)]
enum PreparedValue {
    Call(InstrRef),
    TableRead(InstrRef),
    Unary(InstrRef, crate::hir::common::HirUnaryOpKind),
    Binary(InstrRef),
    Upvalue(UpvalueId),
    Nil,
    NilBatch,
    Boolean(bool),
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

/// 动态索引的 key 准备及可选的 base 准备均绑定到同一 GETTABLE；低槽 base 无须准备。
#[derive(Debug, Clone)]
pub(super) struct TablePreparation {
    pub(super) base: Option<OperandPreparation>,
    pub(super) key: OperandPreparation,
}

impl OperandPreparation {
    pub(super) fn is_nil_batch_member(&self) -> bool {
        matches!(self.value, PreparedValue::NilBatch)
    }

    pub(super) fn matches(&self, value: &HirExpr) -> bool {
        match (&self.value, value) {
            (PreparedValue::Call(read), HirExpr::Call(call)) => {
                call.source_site.is_some_and(|source| source.instr == *read)
            }
            (PreparedValue::TableRead(read), HirExpr::TableAccess(access)) => {
                matches!(access.sources, crate::hir::common::HirOperationSources::Single(source)
                    if source.instr == *read)
            }
            (PreparedValue::TableRead(read), HirExpr::GlobalRef(global)) => {
                // 环境常量键读取归一化成 GlobalRef，仍是原 GETTABLE 的同一次 SSA 准备。
                matches!(global.sources, crate::hir::common::HirOperationSources::Single(source)
                    if source.instr == *read)
            }
            (PreparedValue::Unary(read, op), HirExpr::Unary(unary)) => {
                unary.op == *op
                    && unary
                        .source_site
                        .is_some_and(|source| source.instr == *read)
            }
            (PreparedValue::Binary(read), HirExpr::Binary(binary)) => binary
                .source_site
                .is_some_and(|source| source.instr == *read),
            (PreparedValue::Upvalue(original), HirExpr::UpvalueRef(current)) => original == current,
            (PreparedValue::Nil, HirExpr::Nil) => true,
            (PreparedValue::Boolean(original), HirExpr::Boolean(current)) => original == current,
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
        // SETTABLE 的 RHS、二元运算和比较的右操作数可含分支，先读的快照仍由同一 SSA Def 支配。
        // 这里只保留读取身份；跨分支的实际求值和准备区由完整赋值帧核对。
        || (dataflow.def_block(def) != cfg.instr_to_block[site.index()]
            && !matches!(proto.instrs[site.index()], LowInstr::SetTable(_) | LowInstr::BinaryOp(_) | LowInstr::Branch(_)))
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
        LowInstr::Call(call)
            if call.results
                == crate::transformer::ResultPack::Fixed(crate::transformer::RegRange {
                    start: reg,
                    len: 1,
                }) =>
        {
            PreparedValue::Call(read)
        }
        LowInstr::GetTable(_) => PreparedValue::TableRead(read),
        LowInstr::BinaryOp(_) => PreparedValue::Binary(read),
        LowInstr::UnaryOp(unary) => {
            use crate::hir::common::HirUnaryOpKind;
            use crate::transformer::UnaryOpKind;
            let op = match unary.op {
                UnaryOpKind::Not => HirUnaryOpKind::Not,
                UnaryOpKind::Neg => HirUnaryOpKind::Neg,
                UnaryOpKind::BitNot => HirUnaryOpKind::BitNot,
                UnaryOpKind::Length => HirUnaryOpKind::Length,
            };
            PreparedValue::Unary(read, op)
        }
        LowInstr::GetUpvalue(get) => {
            let (UpvalueOperand::Env(upvalue) | UpvalueOperand::Upvalue(upvalue)) = get.src;
            PreparedValue::Upvalue(UpvalueId(upvalue.index()))
        }
        LowInstr::LoadBool(load) => PreparedValue::Boolean(load.value),
        // 单槽 LOADNIL 可以作为比较准备重发；批量清槽还携带其它写域，不能借此拆开。
        LowInstr::LoadNil(load) if load.dst.start == reg && load.dst.len == 1 => PreparedValue::Nil,
        // 发布批次成员身份，但不让单项 matches(Nil) 接受；只有完整 LOADNIL
        // 事务可消费它，避免其它算术/比较消费者拆掉同指令的剩余写域。
        LowInstr::LoadNil(_) => PreparedValue::NilBatch,
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
