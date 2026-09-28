//! 收集最终 HIR 快照中 AST 构造所需的语法事实。
//!
//! 消费共享 HIR visitor 与显式绑定、资源及闭包身份，发布 temp 声明、TBC 配对、
//! 闭包依赖和命名变参引用；具体语法错误由原 lowering 位置报告。

use std::collections::BTreeSet;

use crate::hir::visit::{self, HirVisitor};
use crate::hir::{
    HirBlock, HirExpr, HirLValue, HirProto, HirStmt, HirTbcDeclaration, LocalId, TempId,
};

#[derive(Default)]
pub(super) struct ProtoBuildFacts {
    pub(super) hoisted_temps: Vec<TempId>,
    pub(super) named_vararg_referenced: bool,
}

impl ProtoBuildFacts {
    pub(super) fn collect(proto: &HirProto) -> (Self, Vec<usize>) {
        let mut collectors = (
            BodyReferences::default(),
            (
                (
                    ReferencedTempCollector::default(),
                    CloseTempCollector::default(),
                ),
                LocalReferenceCollector {
                    local: proto.vararg_param_local.filter(|_| {
                        proto.signature.has_vararg_param_reg && !proto.signature.legacy_arg_slot
                    }),
                    found: false,
                },
            ),
        );
        visit::visit_proto(proto, &mut collectors);
        let (mut children, ((mut references, close), named_vararg)) = collectors;
        references
            .ordered
            .retain(|temp| !close.temps.contains(temp));
        if proto.failure.is_some() {
            children.0.extend(
                proto
                    .detached_children
                    .iter()
                    .map(|(_, child)| child.index()),
            );
        }
        (
            Self {
                hoisted_temps: references.ordered,
                named_vararg_referenced: named_vararg.found,
            },
            children.0,
        )
    }
}

#[derive(Default)]
struct BodyReferences(Vec<usize>);

impl HirVisitor<'_> for BodyReferences {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::Closure(closure) = expr {
            self.0.push(closure.proto.index());
        }
    }
}

#[derive(Default)]
struct ReferencedTempCollector {
    seen: BTreeSet<TempId>,
    ordered: Vec<TempId>,
}

impl ReferencedTempCollector {
    fn note_temp(&mut self, temp: TempId) {
        if self.seen.insert(temp) {
            self.ordered.push(temp);
        }
    }
}

impl HirVisitor<'_> for ReferencedTempCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::TempRef(temp) = expr {
            self.note_temp(*temp);
        }
    }

    fn visit_lvalue(&mut self, target: &HirLValue) {
        if let HirLValue::Temp(temp) = target {
            self.note_temp(*temp);
        }
    }
}

#[derive(Default)]
struct CloseTempCollector {
    temps: BTreeSet<TempId>,
}

impl HirVisitor<'_> for CloseTempCollector {
    fn visit_block(&mut self, block: &HirBlock) {
        for (index, stmt) in block.stmts.iter().enumerate() {
            let HirStmt::ToBeClosed(to_be_closed) = stmt else {
                continue;
            };
            let HirExpr::TempRef(temp) = &to_be_closed.value else {
                continue;
            };
            self.temps.insert(*temp);
            // TBC 声明 query 证明紧邻的整组 exact assignment 都将合成一条声明。
            // sibling temp 也必须从 hoist 排除，否则会先声明再被该语句重复遮蔽。
            if let Some(HirTbcDeclaration::Temps { assignment, .. }) = index
                .checked_sub(1)
                .and_then(|previous| block.stmts.get(previous))
                .and_then(|previous| to_be_closed.declaration(previous))
            {
                self.temps
                    .extend(assignment.targets.iter().filter_map(|target| match target {
                        HirLValue::Temp(temp) => Some(*temp),
                        _ => None,
                    }));
            }
        }
    }
}

struct LocalReferenceCollector {
    local: Option<LocalId>,
    found: bool,
}

impl HirVisitor<'_> for LocalReferenceCollector {
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |= matches!(expr, HirExpr::LocalRef(local) if Some(*local) == self.local);
    }

    fn visit_lvalue(&mut self, target: &HirLValue) {
        self.found |= matches!(target, HirLValue::Local(local) if Some(*local) == self.local);
    }
}

pub(super) fn block_has_continue(block: &HirBlock) -> bool {
    block.stmts.iter().any(stmt_has_continue)
}

fn stmt_has_continue(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Continue => true,
        HirStmt::If(if_stmt) => {
            block_has_continue(&if_stmt.then_block)
                || if_stmt.else_block.as_ref().is_some_and(block_has_continue)
        }
        HirStmt::Block(block) => block_has_continue(block),
        // 内层 loop 自己会在各自的 AST lowering 里决定是否需要 synthetic continue label。
        // 这里如果继续递归进去，外层 loop 会错误地因为“子循环里出现 continue”
        // 也挂上一层无意义的 `::Lx::` label。
        HirStmt::While(_)
        | HirStmt::Repeat(_)
        | HirStmt::NumericFor(_)
        | HirStmt::GenericFor(_) => false,
        _ => false,
    }
}
