//! 按 HIR 实际闭包引用构造 AST 函数体及其构造事实。
//!
//! 保留原 closure occurrence 的捕获与错误归属，诊断恢复另处理 detached child。

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
