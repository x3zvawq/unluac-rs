//! AST readability：把合法 AST 收敛成更接近源码的稳定形状。

mod cleanup;
mod function_sugar;

use super::common::{AstModule, AstTargetDialect};

/// 对外的 readability 入口。
pub fn make_readable(module: &AstModule, target: AstTargetDialect) -> AstModule {
    let mut module = module.clone();
    loop {
        let mut changed = false;
        changed |= function_sugar::apply(&mut module, target);
        changed |= cleanup::apply(&mut module);
        if !changed {
            return module;
        }
    }
}
