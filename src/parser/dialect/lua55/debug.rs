//! 这个文件承载 Lua 5.5 parser 产物的轻量调试输出。

use std::fmt::Write as _;

use crate::debug::{DebugDetail, DebugFilters};
use crate::parser::raw::{
    DecodedText, DialectDebugExtra, DialectInstrExtra, DialectProtoExtra, RawChunk, RawInstr,
    RawInstrOpcode, RawInstrOperands, RawProto, RawString,
};

use super::raw::{Lua55DebugExtra, Lua55InstrExtra, Lua55Opcode, Lua55Operands, Lua55ProtoExtra};

pub(crate) fn dump_chunk(chunk: &RawChunk, detail: DebugDetail, filters: &DebugFilters) -> String {
    let mut output = String::new();
    let mut protos = Vec::new();
    collect_protos(&chunk.main, 0, &mut protos);

    let _ = writeln!(output, "===== Dump Parser =====");
    let _ = writeln!(
        output,
        "parser dialect=lua5.5 detail={} protos={}",
        detail,
        protos.len()
    );
    if let Some(proto_id) = filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output);

    for (id, depth, proto) in protos {
        if filters.proto.is_some_and(|proto_id| proto_id != id) {
            continue;
        }

        let indent = "  ".repeat(depth);
        let raw_flag = match proto.extra {
            DialectProtoExtra::Lua55(Lua55ProtoExtra { raw_flag }) => raw_flag,
            _ => unreachable!("lua55 debug should only receive lua55 protos"),
        };
        let _ = writeln!(
            output,
            "{indent}proto#{id} source={} lines={}..{} params={} vararg={} raw_flag=0x{raw_flag:02x} stack={} instrs={} consts={} upvalues={} children={}",
            format_optional_source(proto.common.source.as_ref()),
            proto.common.line_range.defined_start,
            proto.common.line_range.defined_end,
            proto.common.signature.num_params,
            proto.common.signature.is_vararg,
            proto.common.frame.max_stack_size,
            proto.common.instructions.len(),
            proto.common.constants.common.literals.len(),
            proto.common.upvalues.common.count,
            proto.common.children.len(),
        );

        if matches!(detail, DebugDetail::Summary) {
            continue;
        }

        if let DialectDebugExtra::Lua55(Lua55DebugExtra {
            line_deltas,
            abs_line_info,
        }) = &proto.common.debug_info.extra
            && matches!(detail, DebugDetail::Verbose)
        {
            let _ = writeln!(
                output,
                "{indent}  debug line-deltas={} abs-line-info={} locals={} upvalue-names={}",
                line_deltas.len(),
                abs_line_info.len(),
                proto.common.debug_info.common.local_vars.len(),
                proto.common.debug_info.common.upvalue_names.len(),
            );
        }

        let _ = writeln!(output, "{indent}  instructions");
        if proto.common.instructions.is_empty() {
            let _ = writeln!(output, "{indent}    <empty>");
            continue;
        }

        for (index, instr) in proto.common.instructions.iter().enumerate() {
            let (opcode, operands, extra) = decode_lua55(instr);
            let _ = writeln!(
                output,
                "{indent}    @{index:03} pc={} words={} opcode={} operands={} extraarg={}",
                extra.pc,
                extra.word_len,
                opcode.label(),
                operands.label(),
                extra
                    .extra_arg
                    .map_or_else(|| "-".to_owned(), |value| value.to_string()),
            );
        }
    }

    output
}

fn collect_protos<'a>(
    proto: &'a RawProto,
    depth: usize,
    out: &mut Vec<(usize, usize, &'a RawProto)>,
) {
    let id = out.len();
    out.push((id, depth, proto));
    for child in &proto.common.children {
        collect_protos(child, depth + 1, out);
    }
}

fn format_optional_source(source: Option<&RawString>) -> String {
    source.map_or_else(|| "-".to_owned(), format_raw_string)
}

fn format_raw_string(source: &RawString) -> String {
    source
        .text
        .as_ref()
        .map(|DecodedText { value, .. }| format!("{value:?}"))
        .unwrap_or_else(|| format!("<{} bytes>", source.bytes.len()))
}

fn decode_lua55(raw: &RawInstr) -> (Lua55Opcode, &Lua55Operands, Lua55InstrExtra) {
    let RawInstrOpcode::Lua55(opcode) = raw.opcode else {
        unreachable!("lua55 debug should only receive lua55 opcodes");
    };
    let RawInstrOperands::Lua55(ref operands) = raw.operands else {
        unreachable!("lua55 debug should only receive lua55 operands");
    };
    let DialectInstrExtra::Lua55(extra) = raw.extra else {
        unreachable!("lua55 debug should only receive lua55 extras");
    };
    (opcode, operands, extra)
}

trait Lua55OpcodeDebugExt {
    fn label(self) -> &'static str;
}

impl Lua55OpcodeDebugExt for Lua55Opcode {
    fn label(self) -> &'static str {
        match self {
            Self::Move => "MOVE",
            Self::LoadI => "LOADI",
            Self::LoadF => "LOADF",
            Self::LoadK => "LOADK",
            Self::LoadKx => "LOADKX",
            Self::LoadFalse => "LOADFALSE",
            Self::LFalseSkip => "LFALSESKIP",
            Self::LoadTrue => "LOADTRUE",
            Self::LoadNil => "LOADNIL",
            Self::GetUpVal => "GETUPVAL",
            Self::SetUpVal => "SETUPVAL",
            Self::GetTabUp => "GETTABUP",
            Self::GetTable => "GETTABLE",
            Self::GetI => "GETI",
            Self::GetField => "GETFIELD",
            Self::SetTabUp => "SETTABUP",
            Self::SetTable => "SETTABLE",
            Self::SetI => "SETI",
            Self::SetField => "SETFIELD",
            Self::NewTable => "NEWTABLE",
            Self::Self_ => "SELF",
            Self::AddI => "ADDI",
            Self::AddK => "ADDK",
            Self::SubK => "SUBK",
            Self::MulK => "MULK",
            Self::ModK => "MODK",
            Self::PowK => "POWK",
            Self::DivK => "DIVK",
            Self::IdivK => "IDIVK",
            Self::BandK => "BANDK",
            Self::BorK => "BORK",
            Self::BxorK => "BXORK",
            Self::ShlI => "SHLI",
            Self::ShrI => "SHRI",
            Self::Add => "ADD",
            Self::Sub => "SUB",
            Self::Mul => "MUL",
            Self::Mod => "MOD",
            Self::Pow => "POW",
            Self::Div => "DIV",
            Self::Idiv => "IDIV",
            Self::Band => "BAND",
            Self::Bor => "BOR",
            Self::Bxor => "BXOR",
            Self::Shl => "SHL",
            Self::Shr => "SHR",
            Self::MMBin => "MMBIN",
            Self::MMBinI => "MMBINI",
            Self::MMBinK => "MMBINK",
            Self::Unm => "UNM",
            Self::BNot => "BNOT",
            Self::Not => "NOT",
            Self::Len => "LEN",
            Self::Concat => "CONCAT",
            Self::Close => "CLOSE",
            Self::Tbc => "TBC",
            Self::Jmp => "JMP",
            Self::Eq => "EQ",
            Self::Lt => "LT",
            Self::Le => "LE",
            Self::EqK => "EQK",
            Self::EqI => "EQI",
            Self::LtI => "LTI",
            Self::LeI => "LEI",
            Self::GtI => "GTI",
            Self::GeI => "GEI",
            Self::Test => "TEST",
            Self::TestSet => "TESTSET",
            Self::Call => "CALL",
            Self::TailCall => "TAILCALL",
            Self::Return => "RETURN",
            Self::Return0 => "RETURN0",
            Self::Return1 => "RETURN1",
            Self::ForLoop => "FORLOOP",
            Self::ForPrep => "FORPREP",
            Self::TForPrep => "TFORPREP",
            Self::TForCall => "TFORCALL",
            Self::TForLoop => "TFORLOOP",
            Self::SetList => "SETLIST",
            Self::Closure => "CLOSURE",
            Self::VarArg => "VARARG",
            Self::GetVarg => "GETVARG",
            Self::ErrNNil => "ERRNNIL",
            Self::VarArgPrep => "VARARGPREP",
            Self::ExtraArg => "EXTRAARG",
        }
    }
}

trait Lua55OperandsDebugExt {
    fn label(&self) -> String;
}

impl Lua55OperandsDebugExt for Lua55Operands {
    fn label(&self) -> String {
        match self {
            Lua55Operands::None => "-".to_owned(),
            Lua55Operands::A { a } => format!("A={a}"),
            Lua55Operands::Ak { a, k } => format!("A={a} k={}", u8::from(*k)),
            Lua55Operands::AB { a, b } => format!("A={a} B={b}"),
            Lua55Operands::AC { a, c } => format!("A={a} C={c}"),
            Lua55Operands::ABC { a, b, c } => format!("A={a} B={b} C={c}"),
            Lua55Operands::ABk { a, b, k } => format!("A={a} B={b} k={}", u8::from(*k)),
            Lua55Operands::ABCk { a, b, c, k } => {
                format!("A={a} B={b} C={c} k={}", u8::from(*k))
            }
            Lua55Operands::ABx { a, bx } => format!("A={a} Bx={bx}"),
            Lua55Operands::AsBx { a, sbx } => format!("A={a} sBx={sbx}"),
            Lua55Operands::AsJ { sj } => format!("sJ={sj}"),
            Lua55Operands::Ax { ax } => format!("Ax={ax}"),
            Lua55Operands::ABsCk { a, b, sc, k } => {
                format!("A={a} B={b} sC={sc} k={}", u8::from(*k))
            }
            Lua55Operands::AsBCk { a, sb, c, k } => {
                format!("A={a} sB={sb} C={c} k={}", u8::from(*k))
            }
            Lua55Operands::AvBCk { a, vb, vc, k } => {
                format!("A={a} vB={vb} vC={vc} k={}", u8::from(*k))
            }
        }
    }
}
