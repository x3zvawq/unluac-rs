//! 收集整个 AST 的方言特性与残余错误，包括嵌套函数体。
//!
//! 共享 visitor 负责子节点覆盖；这里只解释声明属性和控制语法，不从名字或 capture
//! 推断特性。例如子函数中的 `<close>` 声明也会成为整个模块的生成要求。

use std::collections::BTreeSet;

use crate::ast::visit::{self, AstVisitor};
use crate::ast::{AstExpr, AstFeature, AstGlobalAttr, AstLocalAttr, AstModule, AstStmt};

pub(crate) fn collect_ast_features(module: &AstModule) -> (BTreeSet<AstFeature>, bool) {
    let mut collector = FeatureCollector::default();
    visit::visit_block(&module.body, &mut collector);
    (collector.features, collector.has_errors)
}

#[derive(Default)]
struct FeatureCollector {
    features: BTreeSet<AstFeature>,
    has_errors: bool,
}

impl AstVisitor for FeatureCollector {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::LocalDecl(local_decl) => {
                for binding in &local_decl.bindings {
                    match binding.attr {
                        AstLocalAttr::Const => {
                            self.features.insert(AstFeature::LocalConst);
                        }
                        AstLocalAttr::Close => {
                            self.features.insert(AstFeature::LocalClose);
                        }
                        AstLocalAttr::None => {}
                    }
                }
            }
            AstStmt::GlobalDecl(global_decl) => {
                self.features.insert(AstFeature::GlobalDecl);
                if global_decl
                    .bindings
                    .iter()
                    .any(|binding| binding.attr == AstGlobalAttr::Const)
                {
                    self.features.insert(AstFeature::GlobalConst);
                }
            }
            AstStmt::Continue => {
                self.features.insert(AstFeature::ContinueStmt);
            }
            AstStmt::Goto(_) | AstStmt::Label(_) => {
                self.features.insert(AstFeature::GotoLabel);
            }
            AstStmt::Error(_) => self.has_errors = true,
            _ => {}
        }
    }

    fn visit_expr(&mut self, expr: &AstExpr) {
        self.has_errors |= matches!(expr, AstExpr::Error(_));
    }
}
