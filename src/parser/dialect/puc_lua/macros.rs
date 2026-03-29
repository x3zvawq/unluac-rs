/// 用单张 opcode 声明表同时生成：
/// `enum + TryFrom<u8> + operand_kind() + extra_word_policy() + label()`。
///
/// 这样各个 PUC-Lua 版本都能把“opcode 长什么样、是否需要 helper word”
/// 以及“出错时展示什么大写标签”都放回 raw 层声明，parser 只消费事实，
/// 不再维护另一张大 `match` 表。
macro_rules! define_puc_lua_opcodes {
    (
        opcode: $opcode:ident,
        operand_kind: $operand_kind:ident,
        extra_word_policy: $extra_word_policy:ident,
        [$(($name:ident, $label:literal, $kind:ident $(, $policy:ident)?)),+ $(,)?]
    ) => {
        $crate::parser::dialect::opcodes::define_opcode_enum! {
            pub enum $opcode { $( $name ),+ }
        }

        impl $opcode {
            pub const fn operand_kind(self) -> $operand_kind {
                match self {
                    $( Self::$name => $operand_kind::$kind, )+
                }
            }

            pub const fn extra_word_policy(self) -> $extra_word_policy {
                match self {
                    $( Self::$name => define_puc_lua_opcodes!(
                        @policy $extra_word_policy $(, $policy)?
                    ), )+
                }
            }

            pub const fn label(self) -> &'static str {
                match self {
                    $( Self::$name => $label, )+
                }
            }
        }
    };
    (@policy $extra_word_policy:ident, $policy:ident) => {
        $extra_word_policy::$policy
    };
    (@policy $extra_word_policy:ident) => {
        $extra_word_policy::None
    };
}

pub(crate) use define_puc_lua_opcodes;

/// 生成 PUC-Lua parser 侧的 instruction codec 胶水实现。
///
/// 各版本只需要声明：
/// - 使用哪种位域拆解结果
/// - 什么时候需要读取 helper word
/// - 如何把 opcode/operands/extra 包回各自的 raw enum
macro_rules! define_puc_lua_instruction_codec {
    (
        codec: $codec:ident,
        opcode: $opcode:ty,
        fields: $fields:ty,
        extra_word_policy: $extra_word_policy:ty,
        operands: $operands:ty,
        decode_fields: $decode_fields:path,
        extra_arg_opcode: $extra_arg_opcode:path,
        should_read_extra_word: |$policy:ident, $fields_ident:ident| $should_read:expr,
        wrap_opcode: $wrap_opcode:expr,
        wrap_operands: $wrap_operands:expr,
        wrap_extra: |$pc:ident, $word_len:ident, $extra_arg:ident| $wrap_extra:expr
        $(,)?
    ) => {
        struct $codec;

        impl $crate::parser::dialect::puc_lua::PucLuaInstructionCodec for $codec {
            type Opcode = $opcode;
            type Fields = $fields;
            type ExtraWordPolicy = $extra_word_policy;
            type Operands = $operands;

            fn decode_fields(word: u32) -> Self::Fields {
                $decode_fields(word)
            }

            fn opcode_byte(fields: Self::Fields) -> u8 {
                fields.opcode
            }

            fn decode_operands(opcode: Self::Opcode, fields: Self::Fields) -> Self::Operands {
                opcode.decode_operands(fields)
            }

            fn extra_word_policy(opcode: Self::Opcode) -> Self::ExtraWordPolicy {
                opcode.extra_word_policy()
            }

            fn should_read_extra_word(policy: Self::ExtraWordPolicy, fields: Self::Fields) -> bool {
                let $policy = policy;
                let $fields_ident = fields;
                $should_read
            }

            fn opcode_label(opcode: Self::Opcode) -> &'static str {
                opcode.label()
            }

            fn extra_arg_opcode() -> Self::Opcode {
                $extra_arg_opcode
            }

            fn extra_arg_ax(fields: Self::Fields) -> u32 {
                fields.ax
            }

            fn wrap_opcode(opcode: Self::Opcode) -> crate::parser::raw::RawInstrOpcode {
                ($wrap_opcode)(opcode)
            }

            fn wrap_operands(operands: Self::Operands) -> crate::parser::raw::RawInstrOperands {
                ($wrap_operands)(operands)
            }

            fn wrap_extra(
                pc: u32,
                word_len: u8,
                extra_arg: Option<u32>,
            ) -> crate::parser::raw::DialectInstrExtra {
                let $pc = pc;
                let $word_len = word_len;
                let $extra_arg = extra_arg;
                $wrap_extra
            }
        }
    };
}

pub(crate) use define_puc_lua_instruction_codec;
