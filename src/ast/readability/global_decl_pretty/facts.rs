//! 这个子模块负责 `global_decl_pretty` pass 的事实收集。
//!
//! 它依赖共享 visitor 的 block pruning 在一次遍历里收集“当前 block 的显式 global、直属
//! 闭包写入、当前 block 的读写观测”，不会把普通子 block 的 gate 提升到父作用域，也不会
//! 在这里直接插入或合并声明。观测还会记录它位于当前 block 首个显式 gate 的前后，避免
//! 把隐式 `global *` 区域误算成受后续声明约束。
//! 例如：块里读到 `print`、写到 `installer` 时，这里会分别记成常量/可写观测；
//! 如果块里显式出现了 `global *`，这里也会把 collective gate 作为正式作用域事实留下来。

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::common::{
    AstBlock, AstExpr, AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstGlobalAttr,
    AstGlobalBindingTarget, AstLValue, AstNameRef, AstStmt,
};

use super::super::visit::{self, AstVisitor};
use super::super::walk::BlockKind;

#[derive(Clone, Default)]
pub(in crate::ast::readability) struct VisibleGlobals {
    names: BTreeMap<String, AstGlobalAttr>,
    collective: Option<AstGlobalAttr>,
}

impl VisibleGlobals {
    pub(super) fn has_explicit_gate(&self) -> bool {
        self.collective.is_some() || !self.names.is_empty()
    }

    fn name_attr(&self, name: &str) -> Option<AstGlobalAttr> {
        self.names.get(name).copied()
    }

    fn collective(&self) -> Option<AstGlobalAttr> {
        self.collective
    }

    pub(in crate::ast::readability) fn after_stmt(&self, stmt: &AstStmt) -> Self {
        let mut visible = self.clone();
        match stmt {
            AstStmt::GlobalDecl(decl) => GlobalFactsCollector::note_global_decl_bindings(
                &decl.bindings,
                &mut visible.names,
                &mut visible.collective,
            ),
            AstStmt::FunctionDecl(function) => {
                if let Some(name) = global_declared_name(function) {
                    visible.names.insert(name.to_owned(), AstGlobalAttr::None);
                }
            }
            _ => {}
        }
        visible
    }
}

pub(super) struct BlockFacts {
    explicit_here: BTreeMap<String, AstGlobalAttr>,
    explicit_collective_here: Option<AstGlobalAttr>,
    nested_written_here: BTreeSet<String>,
    observations: Vec<GlobalObservation>,
    first_explicit_index: Option<usize>,
}

impl BlockFacts {
    pub(super) fn collect(block: &AstBlock) -> Self {
        Self::collect_current_scope(block, None)
    }

    pub(super) fn collect_repeat(block: &AstBlock, condition: &AstExpr) -> Self {
        Self::collect_current_scope(block, Some(condition))
    }

    fn collect_current_scope(block: &AstBlock, trailing_expr: Option<&AstExpr>) -> Self {
        let mut collector = GlobalFactsCollector {
            root_seen: true,
            ..GlobalFactsCollector::default()
        };
        // 当前 block 是事实根；普通子 block 由 scoped walker 单独处理。repeat 的 body
        // 与 condition 属于子级共享作用域，不能把 condition 提升成当前 block 的观测。
        for stmt in &block.stmts {
            if matches!(stmt, AstStmt::Repeat(_)) {
                collector.visit_stmt(stmt);
                collector.leave_stmt(stmt);
            } else {
                visit::visit_stmt(stmt, &mut collector);
            }
        }
        if let Some(expr) = trailing_expr {
            visit::visit_expr(expr, &mut collector);
        }

        Self {
            explicit_here: collector.explicit_here,
            explicit_collective_here: collector.explicit_collective_here,
            nested_written_here: collector.nested_written_here,
            observations: collector.observations,
            first_explicit_index: block.stmts.iter().position(stmt_opens_global_gate),
        }
    }

    pub(super) fn infer_missing(&self, outer_visible: &VisibleGlobals) -> MissingGlobals {
        let mut missing = MissingGlobals::default();
        for observation in &self.observations {
            if !outer_visible.has_explicit_gate() && !observation.after_explicit_here {
                continue;
            }
            let named_attr = observation
                .explicit_name_here
                .or_else(|| outer_visible.name_attr(&observation.name));
            if named_attr.is_some_and(|attr| {
                global_attr_allows(
                    attr,
                    observation.kind,
                    self.nested_written_here.contains(&observation.name),
                )
            }) {
                continue;
            }
            let visible_collective = observation
                .explicit_collective_here
                .or_else(|| outer_visible.collective());
            match visible_collective {
                Some(AstGlobalAttr::None) => continue,
                Some(AstGlobalAttr::Const)
                    if observation.kind == GlobalObservationKind::Read
                        && !self.nested_written_here.contains(&observation.name) =>
                {
                    continue;
                }
                Some(AstGlobalAttr::Const) | None => {}
            }
            if named_attr == Some(AstGlobalAttr::Const)
                || observation.kind == GlobalObservationKind::Write
                || self.nested_written_here.contains(&observation.name)
            {
                missing.note_none(&observation.name, named_attr.is_some());
            } else {
                missing.note_const(&observation.name);
            }
        }
        missing
    }

    pub(super) fn has_explicit_globals(&self) -> bool {
        self.explicit_collective_here.is_some() || !self.explicit_here.is_empty()
    }

    pub(super) fn missing_insert_at(&self, outer_visible: &VisibleGlobals) -> usize {
        if outer_visible.has_explicit_gate() {
            0
        } else {
            self.first_explicit_index.map_or(0, |index| index + 1)
        }
    }
}

#[derive(Default)]
pub(super) struct MissingGlobals {
    pub(super) none: Vec<String>,
    pub(super) const_: Vec<String>,
    seen_none: BTreeSet<String>,
    seen_const: BTreeSet<String>,
    force_named: BTreeSet<String>,
}

impl MissingGlobals {
    pub(super) fn is_empty(&self) -> bool {
        self.none.is_empty() && self.const_.is_empty()
    }

    pub(super) fn requires_named_decl(&self) -> bool {
        !self.force_named.is_empty()
    }

    fn note_none(&mut self, name: &str, force_named: bool) {
        if self.seen_none.insert(name.to_owned()) {
            self.none.push(name.to_owned());
        }
        if force_named {
            self.force_named.insert(name.to_owned());
        }
        self.seen_const.remove(name);
        self.const_.retain(|candidate| candidate != name);
    }

    fn note_const(&mut self, name: &str) {
        if self.seen_none.contains(name) || !self.seen_const.insert(name.to_owned()) {
            return;
        }
        self.const_.push(name.to_owned());
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum GlobalObservationKind {
    Read,
    Write,
}

struct GlobalObservation {
    name: String,
    kind: GlobalObservationKind,
    after_explicit_here: bool,
    explicit_name_here: Option<AstGlobalAttr>,
    explicit_collective_here: Option<AstGlobalAttr>,
}

#[derive(Default)]
struct GlobalFactsCollector {
    explicit_here: BTreeMap<String, AstGlobalAttr>,
    explicit_collective_here: Option<AstGlobalAttr>,
    nested_written_here: BTreeSet<String>,
    observations: Vec<GlobalObservation>,
    function_depth: usize,
    root_seen: bool,
    direct_explicit_active: bool,
    pending_direct_global_decl: bool,
    active_explicit_names: BTreeMap<String, AstGlobalAttr>,
    active_explicit_collective: Option<AstGlobalAttr>,
}

impl GlobalFactsCollector {
    fn note_observation(&mut self, name: &str, kind: GlobalObservationKind) {
        self.observations.push(GlobalObservation {
            name: name.to_owned(),
            kind,
            after_explicit_here: self.direct_explicit_active,
            explicit_name_here: self.active_explicit_names.get(name).copied(),
            explicit_collective_here: self.active_explicit_collective,
        });
    }

    fn note_global_decl_bindings(
        bindings: &[crate::ast::common::AstGlobalBinding],
        names: &mut BTreeMap<String, AstGlobalAttr>,
        collective: &mut Option<AstGlobalAttr>,
    ) {
        for binding in bindings {
            match &binding.target {
                AstGlobalBindingTarget::Name(name) => {
                    names.insert(name.text.clone(), binding.attr);
                }
                AstGlobalBindingTarget::Wildcard => {
                    // 同一词法域里后声明的 wildcard 属性覆盖前声明，而不是取更宽松者：
                    // `global *; global<const> *; x = 1` 在 Lua 5.5 中必须报 const 写入。
                    *collective = Some(binding.attr);
                }
            }
        }
    }
}

impl AstVisitor for GlobalFactsCollector {
    fn visit_block(&mut self, _block: &AstBlock, _kind: BlockKind) -> bool {
        if self.function_depth > 0 {
            return true;
        }
        if self.root_seen {
            return false;
        }
        self.root_seen = true;
        true
    }

    fn visit_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::GlobalDecl(global_decl) => {
                if self.function_depth == 0 {
                    Self::note_global_decl_bindings(
                        &global_decl.bindings,
                        &mut self.explicit_here,
                        &mut self.explicit_collective_here,
                    );
                    self.pending_direct_global_decl = true;
                } else {
                    self.nested_written_here
                        .extend(global_decl.bindings.iter().filter_map(|binding| {
                            match &binding.target {
                                AstGlobalBindingTarget::Name(name) => Some(name.text.clone()),
                                AstGlobalBindingTarget::Wildcard => None,
                            }
                        }));
                }
            }
            AstStmt::FunctionDecl(function_decl) => {
                if let Some(name) = global_declared_name(function_decl) {
                    if self.function_depth == 0 {
                        self.explicit_here
                            .insert(name.to_owned(), AstGlobalAttr::None);
                        self.active_explicit_names
                            .insert(name.to_owned(), AstGlobalAttr::None);
                        self.direct_explicit_active = true;
                    } else {
                        self.nested_written_here.insert(name.to_owned());
                    }
                } else if self.function_depth == 0
                    && let Some(name) = global_function_root_read(function_decl)
                {
                    self.note_observation(name, GlobalObservationKind::Read);
                }
            }
            AstStmt::LocalDecl(_)
            | AstStmt::Assign(_)
            | AstStmt::CallStmt(_)
            | AstStmt::Return(_)
            | AstStmt::If(_)
            | AstStmt::While(_)
            | AstStmt::Repeat(_)
            | AstStmt::NumericFor(_)
            | AstStmt::GenericFor(_)
            | AstStmt::DoBlock(_)
            | AstStmt::LocalFunctionDecl(_)
            | AstStmt::Break
            | AstStmt::Continue
            | AstStmt::Goto(_)
            | AstStmt::Label(_)
            | AstStmt::Error(_) => {}
        }
    }

    fn leave_stmt(&mut self, stmt: &AstStmt) {
        if self.function_depth == 0
            && matches!(stmt, AstStmt::GlobalDecl(_))
            && self.pending_direct_global_decl
        {
            let AstStmt::GlobalDecl(decl) = stmt else {
                unreachable!("global declaration shape checked above");
            };
            Self::note_global_decl_bindings(
                &decl.bindings,
                &mut self.active_explicit_names,
                &mut self.active_explicit_collective,
            );
            self.direct_explicit_active = true;
            self.pending_direct_global_decl = false;
        }
    }

    fn visit_expr(&mut self, expr: &AstExpr) {
        if self.function_depth == 0
            && let AstExpr::Var(AstNameRef::Global(global)) = expr
        {
            self.note_observation(&global.text, GlobalObservationKind::Read);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &AstLValue) {
        if let AstLValue::Name(AstNameRef::Global(global)) = lvalue {
            if self.function_depth == 0 {
                self.note_observation(&global.text, GlobalObservationKind::Write);
            } else {
                self.nested_written_here.insert(global.text.clone());
            }
        }
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        self.function_depth += 1;
        true
    }

    fn leave_function_expr(&mut self, _function: &AstFunctionExpr) {
        self.function_depth = self
            .function_depth
            .checked_sub(1)
            .expect("function_depth should stay balanced across enter/leave");
    }
}

fn global_declared_name(function_decl: &AstFunctionDecl) -> Option<&str> {
    let AstFunctionName::Plain(path) = &function_decl.target else {
        return None;
    };
    if !path.fields.is_empty() {
        return None;
    }
    match &path.root {
        AstNameRef::Global(global) => Some(global.text.as_str()),
        _ => None,
    }
}

fn global_function_root_read(function_decl: &AstFunctionDecl) -> Option<&str> {
    let path = match &function_decl.target {
        AstFunctionName::Plain(path) if !path.fields.is_empty() => path,
        AstFunctionName::Method(path, _) => path,
        AstFunctionName::Plain(_) => return None,
    };
    match &path.root {
        AstNameRef::Global(global) => Some(global.text.as_str()),
        _ => None,
    }
}

fn stmt_opens_global_gate(stmt: &AstStmt) -> bool {
    matches!(stmt, AstStmt::GlobalDecl(_))
        || matches!(stmt, AstStmt::FunctionDecl(function) if global_declared_name(function).is_some())
}

fn global_attr_allows(
    attr: AstGlobalAttr,
    observation: GlobalObservationKind,
    nested_write: bool,
) -> bool {
    attr == AstGlobalAttr::None || (observation == GlobalObservationKind::Read && !nested_write)
}

fn global_access_is_allowed(
    globals: &VisibleGlobals,
    name: &str,
    kind: GlobalObservationKind,
) -> bool {
    if !globals.has_explicit_gate() {
        return true;
    }
    globals
        .name_attr(name)
        .or_else(|| globals.collective())
        .is_some_and(|attr| global_attr_allows(attr, kind, false))
}

/// 判断把一段直属语句的 global 声明延伸到后继表达式后，是否保持每个 global 访问的
/// 许可结果不变。
///
/// `extending_stmts` 本身仍在原位置、原环境求值，因此这里只用其直属声明推进扩域后的
/// 环境，不重新验证其访问。表达式中的每个读写分别比较扩域前后；无关 missing global
/// 即使两边都暂时非法也不会掩盖另一个访问由合法变非法。嵌套函数继续使用同一套顺序
/// 词法解释器，所以函数内声明、global function 递归名和 repeat body outgoing 环境均
/// 按实际作用域继承。
pub(in crate::ast::readability) fn extending_global_scope_preserves_expr(
    incoming: &VisibleGlobals,
    extending_stmts: &[AstStmt],
    expr: &AstExpr,
) -> bool {
    let extended = extending_stmts
        .iter()
        .fold(incoming.clone(), |globals, stmt| globals.after_stmt(stmt));
    expr_global_accesses_satisfy(expr, incoming, Some(&extended))
}

fn expr_global_accesses_satisfy(
    expr: &AstExpr,
    globals: &VisibleGlobals,
    comparison: Option<&VisibleGlobals>,
) -> bool {
    let mut validator = ExprGlobalAccessValidator {
        globals,
        comparison,
        valid: true,
    };
    visit::visit_expr(expr, &mut validator);
    validator.valid
}

struct ExprGlobalAccessValidator<'a> {
    globals: &'a VisibleGlobals,
    comparison: Option<&'a VisibleGlobals>,
    valid: bool,
}

impl AstVisitor for ExprGlobalAccessValidator<'_> {
    fn visit_block(&mut self, _block: &AstBlock, _kind: BlockKind) -> bool {
        false
    }

    fn visit_expr(&mut self, expr: &AstExpr) {
        if let AstExpr::Var(AstNameRef::Global(name)) = expr {
            self.valid &= global_access_satisfies(
                self.globals,
                self.comparison,
                &name.text,
                GlobalObservationKind::Read,
            );
        }
    }

    fn visit_lvalue(&mut self, lvalue: &AstLValue) {
        if let AstLValue::Name(AstNameRef::Global(name)) = lvalue {
            self.valid &= global_access_satisfies(
                self.globals,
                self.comparison,
                &name.text,
                GlobalObservationKind::Write,
            );
        }
    }

    fn visit_function_expr(&mut self, function: &AstFunctionExpr) -> bool {
        self.valid &= check_block_global_accesses(&function.body, self.globals, self.comparison).0;
        false
    }
}

fn global_access_satisfies(
    globals: &VisibleGlobals,
    comparison: Option<&VisibleGlobals>,
    name: &str,
    kind: GlobalObservationKind,
) -> bool {
    let allowed = global_access_is_allowed(globals, name, kind);
    comparison.is_none_or(|other| allowed == global_access_is_allowed(other, name, kind))
}

fn check_block_global_accesses(
    block: &AstBlock,
    incoming: &VisibleGlobals,
    comparison: Option<&VisibleGlobals>,
) -> (bool, VisibleGlobals, Option<VisibleGlobals>) {
    check_stmts_global_accesses(&block.stmts, incoming, comparison)
}

fn check_stmts_global_accesses(
    stmts: &[AstStmt],
    incoming: &VisibleGlobals,
    comparison: Option<&VisibleGlobals>,
) -> (bool, VisibleGlobals, Option<VisibleGlobals>) {
    let mut globals = incoming.clone();
    let mut comparison = comparison.cloned();
    for stmt in stmts {
        if !check_stmt_global_accesses(stmt, &mut globals, &mut comparison) {
            return (false, globals, comparison);
        }
    }
    (true, globals, comparison)
}

fn check_stmt_global_accesses(
    stmt: &AstStmt,
    globals: &mut VisibleGlobals,
    comparison: &mut Option<VisibleGlobals>,
) -> bool {
    match stmt {
        AstStmt::GlobalDecl(decl) => {
            // 声明 initializer 位于新 binding 生效前；其中的闭包也不能提前看到新名字。
            if !decl
                .values
                .iter()
                .all(|value| expr_global_accesses_satisfy(value, globals, comparison.as_ref()))
            {
                return false;
            }
            GlobalFactsCollector::note_global_decl_bindings(
                &decl.bindings,
                &mut globals.names,
                &mut globals.collective,
            );
            if let Some(comparison) = comparison {
                GlobalFactsCollector::note_global_decl_bindings(
                    &decl.bindings,
                    &mut comparison.names,
                    &mut comparison.collective,
                );
            }
            true
        }
        AstStmt::FunctionDecl(decl) => {
            if let Some(name) = global_declared_name(decl) {
                // `global function f()` 形式的名字对函数体递归引用可见，也在语句后
                // 留在当前域；它等价于一个可写逐名声明，而不是普通 field store。
                globals.names.insert(name.to_owned(), AstGlobalAttr::None);
                if let Some(comparison) = comparison {
                    comparison
                        .names
                        .insert(name.to_owned(), AstGlobalAttr::None);
                }
            } else if let Some(name) = global_function_root_read(decl)
                && !global_access_satisfies(
                    globals,
                    comparison.as_ref(),
                    name,
                    GlobalObservationKind::Read,
                )
            {
                return false;
            }
            check_block_global_accesses(&decl.func.body, globals, comparison.as_ref()).0
        }
        AstStmt::LocalFunctionDecl(decl) => {
            check_block_global_accesses(&decl.func.body, globals, comparison.as_ref()).0
        }
        AstStmt::If(if_stmt) => {
            expr_global_accesses_satisfy(&if_stmt.cond, globals, comparison.as_ref())
                && check_block_global_accesses(&if_stmt.then_block, globals, comparison.as_ref()).0
                && if_stmt.else_block.as_ref().is_none_or(|block| {
                    check_block_global_accesses(block, globals, comparison.as_ref()).0
                })
        }
        AstStmt::While(while_stmt) => {
            expr_global_accesses_satisfy(&while_stmt.cond, globals, comparison.as_ref())
                && check_block_global_accesses(&while_stmt.body, globals, comparison.as_ref()).0
        }
        AstStmt::Repeat(repeat_stmt) => {
            let (valid, body_globals, body_comparison) =
                check_block_global_accesses(&repeat_stmt.body, globals, comparison.as_ref());
            valid
                && expr_global_accesses_satisfy(
                    &repeat_stmt.cond,
                    &body_globals,
                    body_comparison.as_ref(),
                )
        }
        AstStmt::NumericFor(for_stmt) => {
            expr_global_accesses_satisfy(&for_stmt.start, globals, comparison.as_ref())
                && expr_global_accesses_satisfy(&for_stmt.limit, globals, comparison.as_ref())
                && expr_global_accesses_satisfy(&for_stmt.step, globals, comparison.as_ref())
                && check_block_global_accesses(&for_stmt.body, globals, comparison.as_ref()).0
        }
        AstStmt::GenericFor(for_stmt) => {
            for_stmt
                .iterator
                .iter()
                .all(|value| expr_global_accesses_satisfy(value, globals, comparison.as_ref()))
                && check_block_global_accesses(&for_stmt.body, globals, comparison.as_ref()).0
        }
        AstStmt::DoBlock(block) => {
            check_block_global_accesses(block, globals, comparison.as_ref()).0
        }
        AstStmt::LocalDecl(_) | AstStmt::Assign(_) | AstStmt::CallStmt(_) | AstStmt::Return(_) => {
            check_leaf_stmt_global_accesses(stmt, globals, comparison.as_ref())
        }
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => true,
    }
}

fn check_leaf_stmt_global_accesses(
    stmt: &AstStmt,
    globals: &VisibleGlobals,
    comparison: Option<&VisibleGlobals>,
) -> bool {
    let mut validator = ExprGlobalAccessValidator {
        globals,
        comparison,
        valid: true,
    };
    visit::visit_stmt(stmt, &mut validator);
    validator.valid
}
