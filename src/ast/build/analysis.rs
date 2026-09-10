//! AST build 所需的当前 HIR 语法事实查询。
//!
//! 遍历子节点和多返回 tail 的责任归 HIR visitor；这里仅收集剩余 temp 的首次出现顺序、
//! `<close>` 声明配对、实际闭包依赖和命名变参的真实引用，避免重新解释 HIR 树结构。
//! 例如 `t = call(); use(t)` 只给 t 分配一次 hoist 声明；相邻 exact assignment/TBC
//! 已能直接语法化为 `<close>` 声明时，整组 sibling temp 都不应再被提前声明。
//! ProtoBodies 在首次访问可达 proto 时请求同一最终 HIR 快照的全部构造事实；遍历完成
//! 才按完整排除集合发布 hoist 列表，避免早遇见的引用遗漏后续 TBC 配对。查询不发出
//! lowering 错误，缺失命名变参身份和 child body 错误仍在原 closure occurrence 处理。
//! continue 查询只回答当前 loop 的语法化需求，嵌套 loop 使用自己的 label owner。

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

impl HirVisitor for BodyReferences {
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

impl HirVisitor for ReferencedTempCollector {
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

impl HirVisitor for CloseTempCollector {
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

impl HirVisitor for LocalReferenceCollector {
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
