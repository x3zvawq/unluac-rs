//! Generate 层错误类型。

use thiserror::Error;

use crate::ast::{AstBindingRef, AstNameRef, DecompileDialect, ProtoId};

/// Generate 可能失败的原因。
#[derive(Debug, Error)]
pub enum GenerateError {
    #[error("proven Luau interpolation lost its fixed argument shape")]
    UnprovenLuauInterpolation,
    #[error("required Luau compound assignment has lost its valid shape")]
    UnprovenCompoundAssignment,
    #[error("generate cannot find naming context for proto#{function}")]
    MissingFunctionNames { function: usize },
    #[error("generate cannot resolve name {name:?} in proto#{function}")]
    MissingName { function: usize, name: AstNameRef },
    #[error("generate cannot resolve binding {binding:?} in proto#{function}")]
    MissingBindingName {
        function: usize,
        binding: AstBindingRef,
    },
    #[error(
        "generate encountered mixed global attributes in a single declaration in proto#{function}"
    )]
    MixedGlobalAttrs { function: usize },
    #[error(
        "target dialect `{dialect}` does not support feature `{feature}` required during generate"
    )]
    UnsupportedFeature {
        dialect: DecompileDialect,
        feature: &'static str,
    },
    #[error("generating a Luau vector constant requires an explicit vector constructor")]
    MissingLuauVectorConstructor,
    #[error("invalid Luau vector constructor identifier `{name}`")]
    InvalidLuauVectorConstructor { name: String },
    #[error("LuaJIT complex literal cannot represent real={real}, imag={imag}")]
    UnrepresentableLuajitComplex { real: f64, imag: f64 },
}

impl GenerateError {
    pub(crate) fn missing_function_names(function: ProtoId) -> Self {
        Self::MissingFunctionNames {
            function: function.index(),
        }
    }
}
