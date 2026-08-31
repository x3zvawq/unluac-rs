//! 这个文件负责清理 HIR 里已经没有入边的机械 label。
//!
//! fallback label/goto body 会先给每个可能成为跳转目标的 block 发一个稳定 label。
//! 但经过 close-scope 物化、branch/loop 恢复之后，入口块和大量中间 pad 的 label 往往
//! 已经不再被任何 `goto` 命中。它们继续留在 HIR 里不仅会让源码多出 `::L0::` 这类
//! 噪音，还会挡住后续 locals pass 对顶层 temp 的提升。
//!
//! 它依赖更前面的 HIR 结构恢复和 scope/loop pass 已经稳定了真正需要保留的 goto，
//! 这里只做“没有任何引用”的 label 清扫，不重新判断控制流是否可结构化，也不会替
//! 前层兜底重写 jump 目标。raw TBC/Close 尚未收敛时，label 仍是 close-scopes 的
//! active-set 边界，因此延迟到资源 cleanup 被消费后的下一轮再删除。
//!
//! 例子：
//! - `::L1::` 如果已经没有任何 `goto L1` 且不再承载 pending TBC 边界，这里会把它删掉
//! - fallback body 里为了每个 block 都预发的 label，经过 branch/loop 吸收后只要
//!   失去引用，就会在这里统一清理
//! - 它不会删除仍被 `goto` 命中的 label，也不会主动合并 block 或改写 goto 结构

use std::collections::BTreeSet;

use crate::hir::common::{HirLabel, HirLabelId, HirProto, HirStmt};

use super::visit::{HirVisitor, visit_proto};
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn remove_unused_labels_in_proto(proto: &mut HirProto) -> bool {
    let facts = collect_label_facts(proto);
    let mut pass = DeadLabelPass {
        referenced: &facts.referenced,
        protect_tbc_boundaries: facts.has_to_be_closed && facts.has_close,
    };
    rewrite_proto(proto, &mut pass)
}

struct DeadLabelPass<'a> {
    referenced: &'a BTreeSet<HirLabelId>,
    protect_tbc_boundaries: bool,
}

impl HirRewritePass for DeadLabelPass<'_> {
    fn rewrite_block(&mut self, block: &mut crate::hir::common::HirBlock) -> bool {
        let original_len = block.stmts.len();
        block.stmts.retain(|stmt| {
            !matches!(stmt, HirStmt::Label(label) if label_is_removable(
                label,
                self.referenced,
                self.protect_tbc_boundaries,
            ))
        });
        block.stmts.len() != original_len
    }
}

fn label_is_removable(
    label: &HirLabel,
    referenced: &BTreeSet<HirLabelId>,
    protect_tbc_boundaries: bool,
) -> bool {
    // 候选拒绝[SemanticBarrier:ControlFlow]：仍被 `goto` 命中的 label 是控制流目的地；
    // 删除会生成悬空 goto；最小反例为 `goto L; ::L::`。
    if referenced.contains(&label.id) {
        return false;
    }
    // 候选拒绝[SemanticBarrier:Lifetime]：raw TBC/Close 尚未被 close-scopes 消费时，
    // 空与非空 active-set label 共同记录词法转换；提前删除会扩大 `<close>` 生命周期
    // （regress_328_dead_label_tbc_barrier）。Close 消费后下一轮即可清理这些机械 label。
    !protect_tbc_boundaries
}

fn collect_label_facts(proto: &HirProto) -> LabelFacts {
    let mut collector = LabelFacts::default();
    visit_proto(proto, &mut collector);
    collector
}

#[derive(Default)]
struct LabelFacts {
    referenced: BTreeSet<HirLabelId>,
    has_to_be_closed: bool,
    has_close: bool,
}

impl HirVisitor for LabelFacts {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::Goto(goto_stmt) => {
                self.referenced.insert(goto_stmt.target);
            }
            HirStmt::ToBeClosed(_) => self.has_to_be_closed = true,
            HirStmt::Close(_) => self.has_close = true,
            _ => {}
        }
    }
}
