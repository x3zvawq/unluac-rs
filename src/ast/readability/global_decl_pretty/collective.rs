//! 这个子模块负责把“缺失 global 声明”收成最小 collective gate。
//!
//! 在 Lua 5.5 里，stripped chunk 常常只能证明“这里必须重新打开某种 global gate 才能
//! 重新编译”，却未必能证明源码是逐名 `global a, b` 还是 collective `global *`。
//! 这里的 owner 只处理这种 AST 级 canonical 选择：
//! - 优先把终端语句尾巴收成最小 `do + global *` / `global<const> *`
//! - 它不会去猜 block 外是否也存在同一批 global
//! - 也不会跨越 label/goto 之类高风险控制流去硬包一层 `do`
//!
//! 例子：
//! - `local ok = ...; local left = math.max(...); return left`
//!   会被收成 `local ok = ...; do global<const> *; local left = ...; return left end`

use std::collections::BTreeSet;

use crate::ast::common::{
    AstBlock, AstExpr, AstFunctionExpr, AstGlobalAttr, AstLValue, AstNameRef, AstStmt,
};

use super::super::visit::{self, AstVisitor};
use super::super::walk::BlockKind;
use super::facts::MissingGlobals;
use super::insert::build_wildcard_global_decl;

pub(super) fn try_wrap_missing_collective_suffix(
    block: &mut AstBlock,
    kind: BlockKind,
    missing: &MissingGlobals,
) -> bool {
    if matches!(kind, BlockKind::ModuleBody) {
        return false;
    }

    let Some((attr, names)) = collective_candidate(missing) else {
        return false;
    };
    let start = block
        .stmts
        .iter()
        .position(|stmt| stmt_mentions_any_missing_global(stmt, &names));
    let Some(start) = start else {
        return false;
    };
    if has_incoming_goto(block, start) {
        // 候选拒绝[SemanticBarrier:ControlFlow]：`goto L; use(missing); ::L::` 若把
        // suffix 改成 `do; global *; use(missing); ::L::; end`，会令原本合法的 goto
        // 跳入新 gate，生成源码无法编译。
        return false;
    }

    let suffix = block.stmts.split_off(start);
    let mut inner_stmts = Vec::with_capacity(suffix.len() + 1);
    inner_stmts.push(build_wildcard_global_decl(attr));
    inner_stmts.extend(suffix);
    block
        .stmts
        .push(AstStmt::DoBlock(Box::new(AstBlock { stmts: inner_stmts })));
    true
}

fn collective_candidate(missing: &MissingGlobals) -> Option<(AstGlobalAttr, BTreeSet<String>)> {
    match (missing.none.is_empty(), missing.const_.is_empty()) {
        (true, false) => Some((
            AstGlobalAttr::Const,
            missing.const_.iter().cloned().collect(),
        )),
        (false, true) => Some((AstGlobalAttr::None, missing.none.iter().cloned().collect())),
        (false, false) => {
            // 候选拒绝[TargetConstraint]：Lua 5.5 的单个 wildcard gate 只能携带一种属性，无法同时表达可写与 const 缺失名；混合形状由逐名声明精确表达。
            None
        }
        (true, true) => None,
    }
}

fn has_incoming_goto(block: &AstBlock, start: usize) -> bool {
    let suffix_labels = block.stmts[start..]
        .iter()
        .filter_map(|stmt| match stmt {
            AstStmt::Label(label) => Some(label.id),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    if suffix_labels.is_empty() {
        return false;
    }

    let mut visitor = IncomingGotoVisitor {
        suffix_labels: &suffix_labels,
        found: false,
    };
    for stmt in &block.stmts[..start] {
        visit::visit_stmt(stmt, &mut visitor);
    }
    visitor.found
}

struct IncomingGotoVisitor<'a> {
    suffix_labels: &'a BTreeSet<crate::ast::common::AstLabelId>,
    found: bool,
}

impl AstVisitor for IncomingGotoVisitor<'_> {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        if let AstStmt::Goto(goto_) = stmt {
            self.found |= self.suffix_labels.contains(&goto_.target);
        }
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}

fn stmt_mentions_any_missing_global(stmt: &AstStmt, names: &BTreeSet<String>) -> bool {
    let mut visitor = MissingGlobalStmtVisitor {
        names,
        found: false,
    };
    visit::visit_stmt(stmt, &mut visitor);
    visitor.found
}

struct MissingGlobalStmtVisitor<'a> {
    names: &'a BTreeSet<String>,
    found: bool,
}

impl AstVisitor for MissingGlobalStmtVisitor<'_> {
    fn visit_expr(&mut self, expr: &AstExpr) {
        if let AstExpr::Var(AstNameRef::Global(global)) = expr
            && self.names.contains(&global.text)
        {
            self.found = true;
        }
    }

    fn visit_lvalue(&mut self, lvalue: &AstLValue) {
        if let AstLValue::Name(AstNameRef::Global(global)) = lvalue
            && self.names.contains(&global.text)
        {
            self.found = true;
        }
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}
