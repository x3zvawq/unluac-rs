//! 这些测试直接固定 Generate 的共享契约。
//!
//! 这里优先手工构造 AST / NameMap，是为了验证“只要前层已经给出稳定语法树，
//! Generate 就能正确落文本”，避免被 parser / HIR 的其它噪音干扰。

#[cfg(test)]
mod generate_tests {
    use unluac::ast::{
        AstBlock, AstDialectVersion, AstGlobalAttr, AstGlobalBinding, AstGlobalBindingTarget,
        AstGlobalDecl, AstModule, AstStmt, AstTargetDialect,
    };
    use unluac::generate::{GenerateOptions, generate_chunk};
    use unluac::hir::HirProtoRef;
    use unluac::naming::{FunctionNameMap, NameMap, NamingMode};

    #[test]
    fn generate_should_emit_global_const_wildcard_decl_when_ast_explicitly_contains_it() {
        let module = AstModule {
            entry_function: HirProtoRef(0),
            body: AstBlock {
                stmts: vec![AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
                    bindings: vec![AstGlobalBinding {
                        target: AstGlobalBindingTarget::Wildcard,
                        attr: AstGlobalAttr::Const,
                    }],
                    values: Vec::new(),
                }))],
            },
        };
        let names = NameMap {
            entry_function: HirProtoRef(0),
            mode: NamingMode::Simple,
            functions: vec![FunctionNameMap::default()],
        };

        let generated = generate_chunk(
            &module,
            &names,
            AstTargetDialect::new(AstDialectVersion::Lua55),
            GenerateOptions::default(),
        )
        .expect("generate should accept explicit global<const> * AST");

        assert_eq!(generated.source, "global<const> *\n");
    }
}
