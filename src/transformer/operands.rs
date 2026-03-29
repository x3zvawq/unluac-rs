//! 这个模块承载 transformer 各 dialect lowering 共享的 operand-shape 校验样板。
//!
//! `expect_ab / expect_abx / expect_asbx ...` 这类 helper 的职责始终一样：
//! 只校验 raw operands 是否匹配期望 shape，并在不匹配时统一抛出
//! `TransformError::UnexpectedOperands`。把这层样板收成宏，版本文件就只需要声明
//! “这个 dialect 的哪个 enum variant 对应哪个 shape”，不再重复维护相同的错误路径。

macro_rules! define_operand_expecters {
    (
        opcode = $opcode_ty:ty,
        operands = $operands_ty:ty,
        label = $opcode_label:path,
        $(
            fn $name:ident($expected:literal) -> $result:ty {
                $( $pattern:pat => $value:expr ),+ $(,)?
            }
        )+
    ) => {
        $(
            fn $name(
                raw_pc: u32,
                opcode: $opcode_ty,
                operands: &$operands_ty,
            ) -> Result<$result, crate::transformer::TransformError> {
                match operands {
                    $( $pattern => Ok($value), )+
                    _ => Err(crate::transformer::TransformError::UnexpectedOperands {
                        raw_pc,
                        opcode: $opcode_label(opcode),
                        expected: $expected,
                    }),
                }
            }
        )+
    };
}

pub(crate) use define_operand_expecters;
