//! 这个子模块负责把“缺失 global 声明”收成最小 collective gate。
//!
//! 在 Lua 5.5 里，已有 AST gate 会约束后缀中的 global 访问；当逐名声明与 collective
//! gate 都能表达该约束时，这里的 owner 只处理 AST 级 canonical 选择，不声称恢复原源码形状：
//! - 优先把终端语句尾巴收成最小 `do + global *` / `global<const> *`
//! - 它不会去猜 block 外是否也存在同一批 global
//! - 也不会跨越 label/goto 之类高风险控制流去硬包一层 `do`
//! - repeat suffix 只有在 until 条件仍能看到所需 binding、且局部根/close 生命周期不变时才包裹
//!
//! 例子：
//! - `local ok = ...; local left = math.max(...); return left`
//!   会被收成 `local ok = ...; do global<const> *; local left = ...; return left end`

use std::{collections::BTreeSet, ops::ControlFlow};

use crate::ast::common::{AstBlock, AstExpr, AstFunctionExpr, AstGlobalAttr, AstNameRef, AstStmt};
use crate::hir::HirRepeatConditionLifetimeFacts;

use self::lifetime::{suffix_has_preserved_lifetime, suffix_shortens_referenced_binding};
use super::facts::MissingGlobals;
use super::insert::build_wildcard_global_decl;
use crate::ast::visit::{self, AstVisitor, NameAccess};

mod lifetime;

pub(super) fn try_wrap_missing_collective_suffix(
    block: &mut AstBlock,
    missing: &MissingGlobals,
    trailing_expr: Option<&AstExpr>,
    repeat_lifetime: Option<&HirRepeatConditionLifetimeFacts>,
) -> bool {
    let names = missing
        .none
        .iter()
        .chain(&missing.const_)
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    if names.is_empty() {
        return false;
    }
    let start = block
        .stmts
        .iter()
        .position(|stmt| stmt_mentions_any_missing_global(stmt, &names));
    let Some(start) = start else {
        return false;
    };
    let Some(attr) = collective_candidate_attr(missing) else {
        return false;
    };
    if trailing_expr
        .is_some_and(|expr| suffix_shortens_referenced_binding(&block.stmts[start..], expr))
    {
        // 候选拒绝[SemanticBarrier:Scope]：`repeat; local value = use(missing); until done(value)`
        // 的 `value` 必须在 until 条件中可见；suffix 包进 `do + global *` 会提前结束其词法作用域；见 regress_424。
        return false;
    }
    if trailing_expr.is_some()
        && repeat_lifetime
            .is_none_or(|lifetime| suffix_has_preserved_lifetime(&block.stmts, start, lifetime))
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：repeat suffix 中的 `<close>`/source identity 必须跨过条件；
        // eventful condition 还能用 weak table + collectgarbage 观察普通 local 的 collectable final value；
        // HIR-origin binding 只有在这个 repeat 的 condition 事实中逐项获证才可提前结束；见 regress_436。
        return false;
    }
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

fn collective_candidate_attr(missing: &MissingGlobals) -> Option<AstGlobalAttr> {
    if missing.requires_named_decl() {
        // `global *` 不能遮蔽外层逐名 `global<const> name`；这类可写
        // 重声明必须由 insert owner 生成精确的 `global name`。
        return None;
    }
    match (missing.none.is_empty(), missing.const_.is_empty()) {
        (true, false) => Some(AstGlobalAttr::Const),
        (false, true) => Some(AstGlobalAttr::None),
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

    block.stmts[..start].iter().any(|stmt| {
        visit::any_stmt_structure(stmt, &mut |stmt| {
            matches!(stmt, AstStmt::Goto(goto_) if suffix_labels.contains(&goto_.target))
        })
    })
}

fn stmt_mentions_any_missing_global(stmt: &AstStmt, names: &BTreeSet<&str>) -> bool {
    let mut visitor = MissingGlobalStmtVisitor {
        names,
        found: false,
    };
    visit::visit_stmt(stmt, &mut visitor);
    visitor.found
}

struct MissingGlobalStmtVisitor<'a, 'names> {
    names: &'a BTreeSet<&'names str>,
    found: bool,
}

impl AstVisitor for MissingGlobalStmtVisitor<'_, '_> {
    fn visit_name(&mut self, name: &AstNameRef, _access: NameAccess) -> ControlFlow<()> {
        // 函数 target 的根引用同样由 visitor 发布；例如 box.f 的 box 在写字段前读取。
        if let AstNameRef::Global(global) = name
            && self.names.contains(global.text.as_str())
        {
            self.found = true;
            return ControlFlow::Break(());
        }
        ControlFlow::Continue(())
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}
