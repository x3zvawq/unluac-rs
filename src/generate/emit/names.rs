//! 将 AST 中的 name/binding 引用解析成最终文本。

use crate::ast::{
    AstBindingRef, AstFeature, AstGlobalBinding, AstGlobalBindingTarget, AstLocalAttr,
    AstLocalBinding, AstNameRef, NameMap, ProtoId,
};
use crate::generate::doc::Doc;

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
        function: ProtoId,
        name: &AstNameRef,
    ) -> Result<String, GenerateError> {
        match name {
            AstNameRef::Environment => Ok("_ENV".to_owned()),
            AstNameRef::Global(global) => Ok(global.text.clone()),
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
                    AstNameRef::Environment | AstNameRef::Global(_) => unreachable!(),
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
        function: ProtoId,
        binding: &AstBindingRef,
    ) -> Result<String, GenerateError> {
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
        };
        text.ok_or_else(|| GenerateError::MissingBindingName {
            function: function.index(),
            binding: *binding,
        })
    }
}

impl<'a> Emitter<'a> {
    pub(super) fn emit_local_binding(
        &self,
        binding: &AstLocalBinding,
        function: ProtoId,
    ) -> Result<Doc, GenerateError> {
        match binding.attr {
            AstLocalAttr::Const if !self.allows_feature(AstFeature::LocalConst) => {
                return Err(GenerateError::UnsupportedFeature {
                    dialect: self.target.version,
                    feature: "local<const>",
                });
            }
            AstLocalAttr::Close if !self.allows_feature(AstFeature::LocalClose) => {
                return Err(GenerateError::UnsupportedFeature {
                    dialect: self.target.version,
                    feature: "local<close>",
                });
            }
            AstLocalAttr::None | AstLocalAttr::Const | AstLocalAttr::Close => {}
        }
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
}
