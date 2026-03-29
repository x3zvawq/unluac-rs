//! 这个子模块负责把 AST 中的 name/binding 引用解析成最终文本。
//!
//! 它依赖 Naming 层已经产出的 `NameMap`，只做查表和错误暴露，不会在这里临时发明兜底名。
//! 例如：残留的 `TempRef` 若没被命名收掉，这里会直接报错而不是静默生成假名字。

use crate::ast::{
    AstBindingRef, AstFunctionDecl, AstFunctionName, AstGlobalBinding, AstGlobalBindingTarget,
    AstLocalAttr, AstLocalBinding, AstNameRef,
};
use crate::generate::doc::Doc;
use crate::hir::HirProtoRef;
use crate::naming::NameMap;

use super::super::error::GenerateError;
use super::Emitter;

pub(super) struct NameResolver<'a> {
    names: &'a NameMap,
}

impl<'a> NameResolver<'a> {
    pub(super) const fn new(names: &'a NameMap) -> Self {
        Self { names }
    }

    pub(super) fn resolve_name_ref(
        &self,
        function: HirProtoRef,
        name: &AstNameRef,
    ) -> Result<String, GenerateError> {
        match name {
            AstNameRef::Global(global) => Ok(global.text.clone()),
            AstNameRef::Temp(_) => Err(GenerateError::ResidualTempName {
                function: function.index(),
                name: name.clone(),
            }),
            _ => {
                let function_names = self
                    .names
                    .function(function)
                    .ok_or_else(|| GenerateError::missing_function_names(function))?;
                let text = match name {
                    AstNameRef::Param(id) => function_names
                        .params
                        .get(id.index())
                        .map(|info| info.text.clone()),
                    AstNameRef::Local(id) => function_names
                        .locals
                        .get(id.index())
                        .map(|info| info.text.clone()),
                    AstNameRef::SyntheticLocal(id) => function_names
                        .synthetic_locals
                        .get(id)
                        .map(|info| info.text.clone()),
                    AstNameRef::Upvalue(id) => function_names
                        .upvalues
                        .get(id.index())
                        .map(|info| info.text.clone()),
                    AstNameRef::Global(_) | AstNameRef::Temp(_) => unreachable!(),
                };
                text.ok_or_else(|| GenerateError::MissingName {
                    function: function.index(),
                    name: name.clone(),
                })
            }
        }
    }

    pub(super) fn resolve_binding_ref(
        &self,
        function: HirProtoRef,
        binding: &AstBindingRef,
    ) -> Result<String, GenerateError> {
        match binding {
            AstBindingRef::Temp(_) => Err(GenerateError::ResidualTempBinding {
                function: function.index(),
                binding: *binding,
            }),
            _ => {
                let function_names = self
                    .names
                    .function(function)
                    .ok_or_else(|| GenerateError::missing_function_names(function))?;
                let text = match binding {
                    AstBindingRef::Local(id) => function_names
                        .locals
                        .get(id.index())
                        .map(|info| info.text.clone()),
                    AstBindingRef::SyntheticLocal(id) => function_names
                        .synthetic_locals
                        .get(id)
                        .map(|info| info.text.clone()),
                    AstBindingRef::Temp(_) => unreachable!(),
                };
                text.ok_or_else(|| GenerateError::MissingBindingName {
                    function: function.index(),
                    binding: *binding,
                })
            }
        }
    }
}

impl<'a> Emitter<'a> {
    pub(super) fn emit_local_binding(
        &self,
        binding: &AstLocalBinding,
        function: HirProtoRef,
    ) -> Result<Doc, GenerateError> {
        let name = self.names.resolve_binding_ref(function, &binding.id)?;
        let text = match binding.attr {
            AstLocalAttr::None => name,
            AstLocalAttr::Const => format!("{name} <const>"),
            AstLocalAttr::Close => format!("{name} <close>"),
        };
        Ok(Doc::text(text))
    }

    pub(super) fn emit_global_binding_target(binding: &AstGlobalBinding) -> Doc {
        match &binding.target {
            AstGlobalBindingTarget::Name(name) => Doc::text(name.text.clone()),
            AstGlobalBindingTarget::Wildcard => Doc::text("*"),
        }
    }

    pub(super) fn function_decl_is_global(&self, function_decl: &AstFunctionDecl) -> bool {
        self.target.caps.global_decl
            && matches!(
                &function_decl.target,
                AstFunctionName::Plain(path) | AstFunctionName::Method(path, _)
                    if matches!(path.root, AstNameRef::Global(_))
            )
    }
}
