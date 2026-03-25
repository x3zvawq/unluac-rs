//! 这个文件承载 transformer 层对外暴露的调试入口。
//!
//! low-IR 是跨 dialect 共享的稳定契约，因此 dump 视图也应尽量共享实现；
//! dialect-specific 的复杂性应该留在 lowering 阶段，而不是再次渗回观察层。

use std::fmt::Write as _;

use crate::debug::{DebugDetail, DebugFilters};
use crate::parser::DialectVersion;

use super::{
    AccessBase, AccessKey, BinaryOpKind, BranchCond, BranchOperands, BranchPredicate, CallKind,
    CaptureSource, CondOperand, InstrRef, LowInstr, LoweredChunk, LoweredProto, RawInstrRef, Reg,
    RegRange, ResultPack, UnaryOpKind, ValueOperand, ValuePack,
};

#[derive(Debug, Clone, Copy)]
struct ProtoEntry<'a> {
    id: usize,
    parent: Option<usize>,
    depth: usize,
    proto: &'a LoweredProto,
}

/// 输出统一 low-IR 的人类可读调试视图。
pub fn dump_lir(chunk: &LoweredChunk, detail: DebugDetail, filters: &DebugFilters) -> String {
    let mut output = String::new();
    let protos = collect_proto_entries(&chunk.main);
    let visible_protos = visible_proto_ids(&protos, filters);

    let _ = writeln!(output, "===== Dump LIR =====");
    let _ = writeln!(
        output,
        "lir dialect={} detail={} protos={}",
        dialect_label(chunk.header.version),
        detail,
        protos.len()
    );
    if let Some(proto_id) = filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output);

    write_proto_tree_view(&mut output, &protos, &visible_protos, detail);
    let _ = writeln!(output);
    write_lir_listing(&mut output, &protos, &visible_protos);

    output
}

fn collect_proto_entries(root: &LoweredProto) -> Vec<ProtoEntry<'_>> {
    let mut entries = Vec::new();
    collect_proto_entries_inner(root, None, 0, &mut entries);
    entries
}

fn collect_proto_entries_inner<'a>(
    proto: &'a LoweredProto,
    parent: Option<usize>,
    depth: usize,
    entries: &mut Vec<ProtoEntry<'a>>,
) {
    let id = entries.len();
    entries.push(ProtoEntry {
        id,
        parent,
        depth,
        proto,
    });

    for child in &proto.children {
        collect_proto_entries_inner(child, Some(id), depth + 1, entries);
    }
}

fn visible_proto_ids(protos: &[ProtoEntry<'_>], filters: &DebugFilters) -> Vec<usize> {
    match filters.proto {
        Some(id) if protos.iter().any(|entry| entry.id == id) => vec![id],
        Some(_) => Vec::new(),
        None => protos.iter().map(|entry| entry.id).collect(),
    }
}

fn write_proto_tree_view(
    output: &mut String,
    protos: &[ProtoEntry<'_>],
    visible_protos: &[usize],
    detail: DebugDetail,
) {
    let _ = writeln!(output, "proto tree");
    if visible_protos.is_empty() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return;
    }

    for entry in protos {
        if !visible_protos.contains(&entry.id) {
            continue;
        }

        let indent = "  ".repeat(entry.depth + 1);
        let _ = writeln!(
            output,
            "{indent}proto#{} parent={} params={} upvalues={} stack={} instrs={} children={} lines={}..{} source={}",
            entry.id,
            entry
                .parent
                .map_or_else(|| "-".to_owned(), |parent| format!("proto#{parent}")),
            entry.proto.signature.num_params,
            entry.proto.upvalues.common.count,
            entry.proto.frame.max_stack_size,
            entry.proto.instrs.len(),
            entry.proto.children.len(),
            entry.proto.line_range.defined_start,
            entry.proto.line_range.defined_end,
            format_optional_source(entry.proto),
        );

        if matches!(detail, DebugDetail::Verbose) {
            let _ = writeln!(
                output,
                "{indent}  raw_instrs={} consts={} low_instrs={}",
                entry.proto.lowering_map.raw_to_low.len(),
                entry.proto.constants.common.literals.len(),
                entry.proto.instrs.len(),
            );
        }
    }
}

fn write_lir_listing(output: &mut String, protos: &[ProtoEntry<'_>], visible_protos: &[usize]) {
    let _ = writeln!(output, "low-ir listing");
    if visible_protos.is_empty() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return;
    }

    for entry in protos {
        if !visible_protos.contains(&entry.id) {
            continue;
        }

        let _ = writeln!(output, "  proto#{}", entry.id);
        if entry.proto.instrs.is_empty() {
            let _ = writeln!(output, "    <empty>");
            continue;
        }

        for (index, instr) in entry.proto.instrs.iter().enumerate() {
            let pcs = &entry.proto.lowering_map.pc_map[index];
            let raws = &entry.proto.lowering_map.low_to_raw[index];
            let line = entry.proto.lowering_map.line_hints[index]
                .map_or_else(|| "-".to_owned(), |line| line.to_string());

            let _ = writeln!(
                output,
                "    @{index:03} {:<60} origin=pc={} raw={} line={}",
                format_low_instr(instr),
                format_pc_list(pcs),
                format_raw_refs(raws),
                line,
            );
        }
    }
}

fn format_optional_source(proto: &LoweredProto) -> String {
    proto
        .source
        .as_ref()
        .and_then(|source| source.text.as_ref())
        .map_or_else(|| "-".to_owned(), |text| format!("{:?}", text.value))
}

fn dialect_label(version: DialectVersion) -> &'static str {
    match version {
        DialectVersion::Lua51 => "lua5.1",
        DialectVersion::Lua52 => "lua5.2",
    }
}

fn format_low_instr(instr: &LowInstr) -> String {
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
            format_upvalue(instr.src)
        ),
        LowInstr::SetUpvalue(instr) => format!(
            "set-upvalue {} <- {}",
            format_upvalue(instr.dst),
            format_reg(instr.src)
        ),
        LowInstr::GetTable(instr) => format!(
            "get-table {} <- {}[{}]",
            format_reg(instr.dst),
            format_access_base(instr.base),
            format_access_key(instr.key)
        ),
        LowInstr::SetTable(instr) => format!(
            "set-table {}[{}] <- {}",
            format_access_base(instr.base),
            format_access_key(instr.key),
            format_value_operand(instr.value)
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
        LowInstr::GenericForCall(instr) => format!(
            "generic-for-call state={} results={}",
            format_reg_range(instr.state),
            format_result_pack(instr.results)
        ),
        LowInstr::GenericForLoop(instr) => format!(
            "generic-for-loop control={} bindings={} body={} exit={}",
            format_reg(instr.control),
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

fn format_proto(proto_ref: super::ProtoRef) -> String {
    format!("proto#{}", proto_ref.index())
}

fn format_value_operand(operand: ValueOperand) -> String {
    match operand {
        ValueOperand::Reg(reg) => format_reg(reg),
        ValueOperand::Const(const_ref) => format_const(const_ref),
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
        CaptureSource::Reg(reg) => format!("reg({})", format_reg(reg)),
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
    let base = match cond.operands {
        BranchOperands::Unary(operand) => {
            format!(
                "{} {}",
                format_branch_predicate(cond.predicate),
                format_cond_operand(operand)
            )
        }
        BranchOperands::Binary(lhs, rhs) => format!(
            "{} {}, {}",
            format_branch_predicate(cond.predicate),
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
        BranchPredicate::Truthy => "truthy",
        BranchPredicate::Eq => "eq",
        BranchPredicate::Lt => "lt",
        BranchPredicate::Le => "le",
    }
}

fn format_cond_operand(operand: CondOperand) -> String {
    match operand {
        CondOperand::Reg(reg) => format_reg(reg),
        CondOperand::Const(const_ref) => format_const(const_ref),
    }
}

fn format_instr_ref(instr: InstrRef) -> String {
    format!("@{}", instr.index())
}

fn format_raw_refs(raws: &[RawInstrRef]) -> String {
    if raws.is_empty() {
        "-".to_owned()
    } else {
        raws.iter()
            .map(|raw| format!("raw#{}", raw.index()))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn format_pc_list(pcs: &[u32]) -> String {
    if pcs.is_empty() {
        "-".to_owned()
    } else {
        let joined = pcs
            .iter()
            .map(u32::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        format!("[{joined}]")
    }
}
