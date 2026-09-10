//! 按 HIR 实际闭包引用后序构造函数体，避免把词法 proto 深度压到 AST lowering 调用栈。
//!
//! HIR visitor 提供当前快照的引用，detached child 只在诊断恢复中参与。函数体和失败结果
//! 都留到原 closure occurrence 消费，捕获元数据仍由该 occurrence 的 lowering 负责。
//! 例如 `return function() return function() end end` 从内到外移动已构造的 body，
//! 不为每层复制整棵子树；同一 proto 的多个实际 occurrence 才需要复制独立 AST。
//! 首次访问可达 proto 时一并冻结 hoist 与命名变参引用，后续消费不再回扫 HIR；
//! 依赖 Vec 保留重复 occurrence 并直接交给 DFS，不为未使用的 proto 构造语法事实。

use crate::hir::{HirModule, TempId};

use super::analysis::ProtoBuildFacts;
use super::{AstBlock, AstLowerError};

#[derive(Default)]
pub(super) struct ProtoBodies {
    entries: Vec<ProtoBody>,
}

#[derive(Default)]
struct ProtoBody {
    remaining: usize,
    facts: ProtoBuildFacts,
    body: Option<Result<AstBlock, AstLowerError>>,
}

impl ProtoBodies {
    pub(super) fn prepare(module: &HirModule) -> (Self, Vec<usize>) {
        let mut entries = (0..module.protos.len())
            .map(|_| ProtoBody::default())
            .collect::<Vec<_>>();
        let order = crate::graph::depth_first(
            module.protos.len(),
            module.entry.index(),
            |index| index,
            |index| index < module.protos.len(),
            |index| {
                let (facts, dependencies) = ProtoBuildFacts::collect(&module.protos[index]);
                entries[index].facts = facts;
                for &child in &dependencies {
                    if let Some(entry) = entries.get_mut(child) {
                        entry.remaining += 1;
                    }
                }
                dependencies
            },
        )
        .postorder;
        if let Some(entry) = entries.get_mut(module.entry.index()) {
            entry.remaining += 1;
        }
        (Self { entries }, order)
    }

    pub(super) fn take_hoisted_temps(&mut self, proto: usize) -> Vec<TempId> {
        std::mem::take(&mut self.entries[proto].facts.hoisted_temps)
    }

    pub(super) fn named_vararg_is_referenced(&self, proto: usize) -> bool {
        self.entries[proto].facts.named_vararg_referenced
    }

    pub(super) fn insert(&mut self, proto: usize, body: Result<AstBlock, AstLowerError>) {
        self.entries[proto].body = Some(body);
    }

    pub(super) fn take(&mut self, proto: usize) -> Result<AstBlock, AstLowerError> {
        let entry = &mut self.entries[proto];
        entry.remaining -= 1;
        if entry.remaining == 0 {
            entry
                .body
                .take()
                .expect("child body is constructed before its owner")
        } else {
            entry
                .body
                .as_ref()
                .expect("child body is constructed before its owner")
                .clone()
        }
    }
}
