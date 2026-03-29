//! 这个模块只放跨 dialect 真正共享的 opcode 声明宏。
//!
//! 它故意不碰具体的 operand 字段、helper word 规则、aux word 语义；
//! 那些仍然留给各个 family/dialect 自己定义，避免为了“一个宏包打天下”
//! 把差异揉成越来越难懂的 DSL。

/// 只负责生成 `enum + TryFrom<u8>` 的最小 opcode 骨架。
macro_rules! define_opcode_enum {
    ($vis:vis enum $opcode:ident { $($name:ident),+ $(,)? }) => {
        #[derive(Debug, Clone, Copy, Eq, PartialEq)]
        #[repr(u8)]
        $vis enum $opcode {
            $( $name, )+
        }

        impl ::std::convert::TryFrom<u8> for $opcode {
            type Error = u8;

            fn try_from(value: u8) -> Result<Self, Self::Error> {
                match value {
                    $( x if x == Self::$name as u8 => Ok(Self::$name), )+
                    _ => Err(value),
                }
            }
        }
    };
}

pub(crate) use define_opcode_enum;

/// 为“opcode -> label / operand kind” 这种简单表驱动 dialect 生成骨架。
macro_rules! define_opcode_kind_table {
    (
        opcode: $opcode:ident,
        operand_kind: $operand_kind:ident,
        [$(($name:ident, $label:literal, $kind:ident)),+ $(,)?]
    ) => {
        $crate::parser::dialect::opcodes::define_opcode_enum! {
            pub enum $opcode { $( $name ),+ }
        }

        impl $opcode {
            pub const fn label(self) -> &'static str {
                match self {
                    $( Self::$name => $label, )+
                }
            }

            pub const fn operand_kind(self) -> $operand_kind {
                match self {
                    $( Self::$name => $operand_kind::$kind, )+
                }
            }
        }
    };
}

pub(crate) use define_opcode_kind_table;
