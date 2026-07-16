//! low-IR 指令的稳定单行展示。
//!
//! 这不是 debug stage renderer 的一部分：web/wasm 的 rich result 也需要把
//! `LowInstr` 渲染成便于 UI 展示的短文本。因此这里保持在普通 transformer 模块内，
//! 而完整的 `--dump transformer` 树形输出继续放在 `debug.rs` 并受
//! `decompile-debug` feature 控制。

use super::{
    AccessBase, AccessKey, BinaryOpKind, BranchCond, BranchPredicate, BranchSubject, CallKind,
    CaptureSource, CondOperand, GetTableKind, InstrRef, LowInstr, Reg, RegRange, ResultPack,
    SetTableKind, UnaryOpKind, ValueOperand, ValuePack,
};

pub fn format_low_instr(instr: &LowInstr) -> String {
    match instr {
        LowInstr::Move(instr) => {
            format!(
                "move {} <- {}",
                format_reg(instr.dst),
                format_reg(instr.src)
            )
        }
        LowInstr::LoadNil(instr) => format!("load-nil {}", format_reg_range(instr.dst)),
        LowInstr::LoadBool(instr) => {
            format!("load-bool {} <- {}", format_reg(instr.dst), instr.value)
        }
        LowInstr::LoadConst(instr) => {
            format!(
                "load-const {} <- {}",
                format_reg(instr.dst),
                format_const(instr.value)
            )
        }
        LowInstr::LoadInteger(instr) => {
            format!("load-int {} <- {}", format_reg(instr.dst), instr.value)
        }
        LowInstr::LoadNumber(instr) => {
            format!("load-num {} <- {}", format_reg(instr.dst), instr.value)
        }
        LowInstr::UnaryOp(instr) => format!(
            "{} {} <- {}",
            format_unary_op(instr.op),
            format_reg(instr.dst),
            format_reg(instr.src)
        ),
        LowInstr::BinaryOp(instr) => format!(
            "{} {} <- {}, {}",
            format_binary_op(instr.op),
            format_reg(instr.dst),
            format_value_operand(instr.lhs),
            format_value_operand(instr.rhs)
        ),
        LowInstr::Concat(instr) => format!(
            "concat {} <- {}",
            format_reg(instr.dst),
            format_reg_range(instr.src)
        ),
        LowInstr::GetUpvalue(instr) => format!(
            "get-upvalue {} <- {}",
            format_reg(instr.dst),
            format_upvalue_operand(instr.src)
        ),
        LowInstr::SetUpvalue(instr) => format!(
            "set-upvalue {} <- {}",
            format_upvalue_operand(instr.dst),
            format_value_operand(instr.src)
        ),
        LowInstr::GetTable(instr) => format!(
            "{} {} <- {}[{}]",
            if instr.kind == GetTableKind::Raw {
                "raw-get-table"
            } else {
                "get-table"
            },
            format_reg(instr.dst),
            format_access_base(instr.base),
            format_access_key(instr.key)
        ),
        LowInstr::SetTable(instr) => format!(
            "{} {}[{}] <- {}",
            if instr.kind == SetTableKind::Raw {
                "raw-set-table"
            } else {
                "set-table"
            },
            format_access_base(instr.base),
            format_access_key(instr.key),
            format_value_operand(instr.value)
        ),
        LowInstr::ErrNil(instr) => format!(
            "err-nnil {} name={}",
            format_reg(instr.subject),
            instr.name.map_or_else(|| "?".to_owned(), format_const)
        ),
        LowInstr::TypeGuard(instr) => format!(
            "type-guard {} expected={}",
            format_reg(instr.subject),
            instr.kind.label()
        ),
        LowInstr::NewTable(instr) => format!("new-table {}", format_reg(instr.dst)),
        LowInstr::SetList(instr) => format!(
            "set-list {} values={} start={}",
            format_reg(instr.base),
            format_value_pack(instr.values),
            instr.start_index
        ),
        LowInstr::Call(instr) => format!(
            "call({}) {} args={} results={}",
            format_call_kind(instr.kind),
            format_reg(instr.callee),
            format_value_pack(instr.args),
            format_result_pack(instr.results)
        ),
        LowInstr::TailCall(instr) => format!(
            "tail-call({}) {} args={}",
            format_call_kind(instr.kind),
            format_reg(instr.callee),
            format_value_pack(instr.args)
        ),
        LowInstr::VarArg(instr) => format!("vararg results={}", format_result_pack(instr.results)),
        LowInstr::Return(instr) => format!("return {}", format_value_pack(instr.values)),
        LowInstr::Closure(instr) => format!(
            "closure {} <- {} captures=[{}]",
            format_reg(instr.dst),
            format_proto(instr.proto),
            instr
                .captures
                .iter()
                .map(|capture| format_capture_source(capture.source))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        LowInstr::Close(instr) => format!("close from {}", format_reg(instr.from)),
        LowInstr::Tbc(instr) => format!("tbc {}", format_reg(instr.reg)),
        LowInstr::NumericForInit(instr) => format!(
            "numeric-for-init index={} limit={} step={} binding={} body={} exit={}",
            format_reg(instr.index),
            format_reg(instr.limit),
            format_reg(instr.step),
            format_reg(instr.binding),
            format_instr_ref(instr.body_target),
            format_instr_ref(instr.exit_target)
        ),
        LowInstr::NumericForLoop(instr) => format!(
            "numeric-for-loop index={} limit={} step={} binding={} body={} exit={}",
            format_reg(instr.index),
            format_reg(instr.limit),
            format_reg(instr.step),
            format_reg(instr.binding),
            format_instr_ref(instr.body_target),
            format_instr_ref(instr.exit_target)
        ),
        LowInstr::GenericForPrep(instr) => format!(
            "generic-for-prep iterator={} state={} control={}->{} closing={}->{}",
            format_reg(instr.iterator),
            format_reg(instr.state),
            format_reg(instr.control_source),
            format_reg(instr.control_target),
            format_reg(instr.closing_source),
            format_reg(instr.closing_target)
        ),
        LowInstr::GenericForCall(instr) => format!(
            "generic-for-call iterator={} state={} control={} results={}",
            format_reg(instr.iterator),
            format_reg(instr.state),
            format_reg(instr.control),
            format_result_pack(instr.results)
        ),
        LowInstr::GenericForLoop(instr) => format!(
            "generic-for-loop control={} bindings={} body={} exit={}",
            format_reg(instr.control_target),
            format_reg_range(instr.bindings),
            format_instr_ref(instr.body_target),
            format_instr_ref(instr.exit_target)
        ),
        LowInstr::Jump(instr) => format!("jump {}", format_instr_ref(instr.target)),
        LowInstr::Branch(instr) => format!(
            "branch if {} then {} else {}",
            format_branch_cond(instr.cond),
            format_instr_ref(instr.then_target),
            format_instr_ref(instr.else_target)
        ),
    }
}

fn format_reg(reg: Reg) -> String {
    format!("r{}", reg.index())
}

fn format_reg_range(range: RegRange) -> String {
    match range.len {
        0 => format!("{}..(empty)", format_reg(range.start)),
        1 => format_reg(range.start),
        len => format!(
            "{}..r{}",
            format_reg(range.start),
            range.start.index() + len - 1
        ),
    }
}

fn format_const(const_ref: super::ConstRef) -> String {
    format!("k{}", const_ref.index())
}

fn format_upvalue(upvalue_ref: super::UpvalueRef) -> String {
    format!("u{}", upvalue_ref.index())
}

fn format_upvalue_operand(operand: super::UpvalueOperand) -> String {
    match operand {
        super::UpvalueOperand::Env => "env".to_owned(),
        super::UpvalueOperand::Upvalue(upvalue) => format_upvalue(upvalue),
    }
}

fn format_proto(proto_ref: super::ProtoRef) -> String {
    format!("proto#{}", proto_ref.index())
}

fn format_value_operand(operand: ValueOperand) -> String {
    match operand {
        ValueOperand::Reg(reg) => format_reg(reg),
        ValueOperand::Const(const_ref) => format_const(const_ref),
        ValueOperand::Integer(value) => value.to_string(),
        ValueOperand::Nil => "nil".to_owned(),
        ValueOperand::Boolean(value) => value.to_string(),
    }
}

fn format_access_base(base: AccessBase) -> String {
    match base {
        AccessBase::Reg(reg) => format_reg(reg),
        AccessBase::Env => "env".to_owned(),
        AccessBase::Upvalue(upvalue) => format_upvalue(upvalue),
    }
}

fn format_access_key(key: AccessKey) -> String {
    match key {
        AccessKey::Reg(reg) => format_reg(reg),
        AccessKey::Const(const_ref) => format_const(const_ref),
        AccessKey::Integer(value) => value.to_string(),
    }
}

fn format_value_pack(pack: ValuePack) -> String {
    match pack {
        ValuePack::Fixed(range) => format!("fixed({})", format_reg_range(range)),
        ValuePack::Open(reg) => format!("open({})", format_reg(reg)),
    }
}

fn format_result_pack(pack: ResultPack) -> String {
    match pack {
        ResultPack::Fixed(range) => format!("fixed({})", format_reg_range(range)),
        ResultPack::Open(reg) => format!("open({})", format_reg(reg)),
        ResultPack::Ignore => "ignore".to_owned(),
    }
}

fn format_call_kind(kind: CallKind) -> &'static str {
    match kind {
        CallKind::Normal => "normal",
        CallKind::Method => "method",
    }
}

fn format_capture_source(source: CaptureSource) -> String {
    match source {
        CaptureSource::ByValue(reg) => format!("value({})", format_reg(reg)),
        CaptureSource::ByReference(reg) => format!("ref({})", format_reg(reg)),
        CaptureSource::Upvalue(upvalue) => format!("upvalue({})", format_upvalue(upvalue)),
    }
}

fn format_unary_op(op: UnaryOpKind) -> &'static str {
    match op {
        UnaryOpKind::Not => "not",
        UnaryOpKind::Neg => "neg",
        UnaryOpKind::BitNot => "bit-not",
        UnaryOpKind::Length => "len",
    }
}

fn format_binary_op(op: BinaryOpKind) -> &'static str {
    match op {
        BinaryOpKind::Add => "add",
        BinaryOpKind::Sub => "sub",
        BinaryOpKind::Mul => "mul",
        BinaryOpKind::Div => "div",
        BinaryOpKind::FloorDiv => "floor-div",
        BinaryOpKind::Mod => "mod",
        BinaryOpKind::Pow => "pow",
        BinaryOpKind::BitAnd => "bit-and",
        BinaryOpKind::BitOr => "bit-or",
        BinaryOpKind::BitXor => "bit-xor",
        BinaryOpKind::Shl => "shl",
        BinaryOpKind::Shr => "shr",
    }
}

fn format_branch_cond(cond: BranchCond) -> String {
    let base = match cond.subject {
        BranchSubject::Truthy(operand) => format!("truthy {}", format_cond_operand(operand)),
        BranchSubject::Compare {
            predicate,
            lhs,
            rhs,
        } => format!(
            "{} {}, {}",
            format_branch_predicate(predicate),
            format_cond_operand(lhs),
            format_cond_operand(rhs)
        ),
    };

    if cond.negated {
        format!("not ({base})")
    } else {
        base
    }
}

fn format_branch_predicate(predicate: BranchPredicate) -> &'static str {
    match predicate {
        BranchPredicate::Eq => "eq",
        BranchPredicate::Lt => "lt",
        BranchPredicate::Le => "le",
    }
}

fn format_cond_operand(operand: CondOperand) -> String {
    match operand {
        CondOperand::Reg(reg) => format_reg(reg),
        CondOperand::Const(const_ref) => format_const(const_ref),
        CondOperand::Nil => "nil".to_owned(),
        CondOperand::Boolean(value) => value.to_string(),
        CondOperand::Integer(value) => value.to_string(),
        CondOperand::Number(value) => value.to_f64().to_string(),
    }
}

fn format_instr_ref(instr: InstrRef) -> String {
    format!("@{}", instr.index())
}
