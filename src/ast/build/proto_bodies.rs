//! 按 HIR 实际闭包引用后序构造函数体，避免把词法 proto 深度压到 AST lowering 调用栈。
//!
//! HIR visitor 提供当前快照的引用，detached child 只在诊断恢复中参与。函数体和失败结果
//! 都留到原 closure occurrence 消费，捕获元数据仍由该 occurrence 的 lowering 负责。
//! 例如 `return function() return function() end end` 从内到外移动已构造的 body，
//! 不为每层复制整棵子树；同一 proto 的多个实际 occurrence 才需要复制独立 AST。

use crate::hir::visit::{self, HirVisitor};
use crate::hir::{HirExpr, HirModule};

use super::{AstBlock, AstLowerError};

#[derive(Default)]
pub(super) struct ProtoBodies {
    remaining: Vec<usize>,
    bodies: Vec<Option<Result<AstBlock, AstLowerError>>>,
}

impl ProtoBodies {
    pub(super) fn prepare(module: &HirModule) -> (Self, Vec<usize>) {
        let dependencies = module
            .protos
            .iter()
            .map(|proto| {
                let mut references = BodyReferences::default();
                visit::visit_proto(proto, &mut references);
                if proto.failure.is_some() {
                    references.0.extend(
                        proto
                            .detached_children
                            .iter()
                            .map(|(_, child)| child.index()),
                    );
                }
                references.0
            })
            .collect::<Vec<_>>();
        let order = crate::graph::depth_first(
            module.protos.len(),
            module.entry.index(),
            |index| index,
            |index| index < module.protos.len(),
            |index| dependencies[index].iter().copied(),
        )
        .postorder;
        let mut remaining = vec![0; module.protos.len()];
        for &owner in &order {
            for &child in &dependencies[owner] {
                if let Some(uses) = remaining.get_mut(child) {
                    *uses += 1;
                }
            }
        }
        if let Some(uses) = remaining.get_mut(module.entry.index()) {
            *uses += 1;
        }
        let bodies = (0..module.protos.len()).map(|_| None).collect();
        (Self { remaining, bodies }, order)
    }

    pub(super) fn insert(&mut self, proto: usize, body: Result<AstBlock, AstLowerError>) {
        self.bodies[proto] = Some(body);
    }

    pub(super) fn take(&mut self, proto: usize) -> Result<AstBlock, AstLowerError> {
        let remaining = &mut self.remaining[proto];
        let slot = &mut self.bodies[proto];
        *remaining -= 1;
        if *remaining == 0 {
            slot.take()
                .expect("child body is constructed before its owner")
        } else {
            slot.as_ref()
                .expect("child body is constructed before its owner")
                .clone()
        }
    }
}

#[derive(Default)]
struct BodyReferences(Vec<usize>);

impl HirVisitor for BodyReferences {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::Closure(closure) = expr {
            self.0.push(closure.proto.index());
        }
    }
}
