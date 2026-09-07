//! 收集当前函数源码中的稳定显示编号，不进入 child body 或消费 capture 元数据。
//!
//! 子节点与名字角色由共享 AST visitor 枚举；synthetic 编号排在本函数已出现的 LocalId
//! 之后。例如嵌套函数捕获父级 local 时，capture 不能扩大当前快照的 local 编号范围。

use std::collections::BTreeSet;
use std::ops::ControlFlow;

use crate::ast::visit::{self, AstVisitor, NameAccess};
use crate::ast::{AstBlock, AstFunctionExpr, AstNameRef, AstSyntheticLocalId};

use super::FunctionRenderNames;

pub(super) fn collect_function_render_names(block: &AstBlock) -> FunctionRenderNames {
    let mut collector = RenderNameCollector::default();
    visit::visit_block(block, &mut collector);
    let start_index = collector.max_local.map_or(0, |index| index + 1);
    let synthetic_locals = collector
        .synthetic_locals
        .into_iter()
        .enumerate()
        .map(|(offset, local)| (local, start_index + offset))
        .collect();
    FunctionRenderNames { synthetic_locals }
}

#[derive(Default)]
struct RenderNameCollector {
    max_local: Option<usize>,
    synthetic_locals: BTreeSet<AstSyntheticLocalId>,
}

impl AstVisitor for RenderNameCollector {
    fn visit_name(&mut self, name: &AstNameRef, access: NameAccess) -> ControlFlow<()> {
        if !matches!(access, NameAccess::Capture) {
            match name {
                AstNameRef::Local(local) => {
                    self.max_local = self.max_local.max(Some(local.index()));
                }
                AstNameRef::SyntheticLocal(local) => {
                    self.synthetic_locals.insert(*local);
                }
                _ => {}
            }
        }
        ControlFlow::Continue(())
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}
