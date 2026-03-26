//! Generate 层错误类型。
//!
//! Generate 是纯输出层，所以这里的错误大多意味着前层契约没有收敛好，
//! 或者当前 AST 已经表达了一个生成器还不能稳定输出的形状。

use thiserror::Error;

use crate::ast::{AstBindingRef, AstDialectVersion, AstNameRef};
use crate::hir::HirProtoRef;

/// Generate 可能失败的原因。
#[derive(Debug, Error)]
pub enum GenerateError {
    #[error("generate cannot find naming context for proto#{function}")]
    MissingFunctionNames { function: usize },
    #[error("generate cannot resolve name {name:?} in proto#{function}")]
    MissingName { function: usize, name: AstNameRef },
    #[error("generate cannot resolve binding {binding:?} in proto#{function}")]
    MissingBindingName {
        function: usize,
        binding: AstBindingRef,
    },
    #[error("generate encountered residual temp name {name:?} in proto#{function}")]
    ResidualTempName { function: usize, name: AstNameRef },
    #[error("generate encountered residual temp binding {binding:?} in proto#{function}")]
    ResidualTempBinding {
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
        dialect: AstDialectVersion,
        feature: &'static str,
    },
}

impl GenerateError {
    pub(crate) fn missing_function_names(function: HirProtoRef) -> Self {
        Self::MissingFunctionNames {
            function: function.index(),
        }
    }
}
