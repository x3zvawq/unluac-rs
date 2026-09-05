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
use super::super::walk::{BlockKind, RewriteScope};

#[derive(Default)]
pub(in crate::ast::readability) struct VisibleGlobals {
    names: BTreeMap<String, AstGlobalAttr>,
    collective: Option<AstGlobalAttr>,
    undo_names: Vec<(String, Option<AstGlobalAttr>)>,
}

impl RewriteScope for VisibleGlobals {
    type Checkpoint = (usize, Option<AstGlobalAttr>);

    fn checkpoint(&self) -> Self::Checkpoint {
        (self.undo_names.len(), self.collective)
    }

    fn restore(&mut self, (len, collective): Self::Checkpoint) {
        while self.undo_names.len() > len {
            let (name, previous) = self.undo_names.pop().unwrap();
            if let Some(attr) = previous {
                self.names.insert(name, attr);
            } else {
                self.names.remove(&name);
            }
        }
        self.collective = collective;
    }
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

    pub(in crate::ast::readability) fn apply_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::GlobalDecl(decl) => {
                for binding in &decl.bindings {
                    if let AstGlobalBindingTarget::Name(name) = &binding.target {
                        self.undo_names
                            .push((name.text.clone(), self.names.get(&name.text).copied()));
                    }
                }
                GlobalFactsCollector::note_global_decl_bindings(
                    &decl.bindings,
                    &mut self.names,
                    &mut self.collective,
                );
            }
            AstStmt::FunctionDecl(function) => {
                if let Some(name) = global_declared_name(function) {
                    let name = name.to_owned();
                    let previous = self.names.insert(name.clone(), AstGlobalAttr::None);
                    self.undo_names.push((name, previous));
                }
            }
            _ => {}
        }
    }

    pub(in crate::ast::readability) fn enter_stmt_children(&mut self, stmt: &AstStmt) {
        // global function 的自名对函数体可见；GlobalDecl initializer 仍使用声明前环境。
        if matches!(stmt, AstStmt::FunctionDecl(_)) {
            self.apply_stmt(stmt);
        }
    }
}

pub(super) struct BlockFacts {
    explicit_here: BTreeMap<String, AstGlobalAttr>,
    explicit_collective_here: Option<AstGlobalAttr>,
    nested_written_here: BTreeSet<String>,
    observations: Vec<GlobalObservation>,
    /// repeat body 求值结束后、同一词法域的 until 条件产生的观测。
    ///
    /// collective suffix 只给新建的 `do` 内部打开 gate，不能把这里的缺失访问一并
    /// 当成已覆盖；保留独立序列让 caller 在包裹成功后仍插入条件所需的逐名声明。
    trailing_observations: Vec<GlobalObservation>,
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
        let trailing_start = collector.observations.len();
        if let Some(expr) = trailing_expr {
            visit::visit_expr(expr, &mut collector);
        }
        let trailing_observations = collector.observations.split_off(trailing_start);

        Self {
            explicit_here: collector.explicit_here,
            explicit_collective_here: collector.explicit_collective_here,
            nested_written_here: collector.nested_written_here,
            observations: collector.observations,
            trailing_observations,
            first_explicit_index: block.stmts.iter().position(stmt_opens_global_gate),
        }
    }

    pub(super) fn infer_missing(&self, outer_visible: &VisibleGlobals) -> MissingGlobals {
        self.infer_missing_from(
            outer_visible,
            self.observations.iter().chain(&self.trailing_observations),
        )
    }

    /// 只返回当前 block 直属语句里的缺失访问。
    ///
    /// repeat collective suffix 的新 gate 仅覆盖这一部分；until 条件的缺失访问必须继续
    /// 留给外层逐名声明，不能因为名称恰好也在 body 出现就被集合差误删。
    pub(super) fn infer_body_missing(&self, outer_visible: &VisibleGlobals) -> MissingGlobals {
        self.infer_missing_from(outer_visible, &self.observations)
    }

    /// 只返回 repeat until 条件里的缺失访问；普通 block 恒为空。
    pub(super) fn infer_trailing_missing(&self, outer_visible: &VisibleGlobals) -> MissingGlobals {
        self.infer_missing_from(outer_visible, &self.trailing_observations)
    }

    fn infer_missing_from<'a>(
        &self,
        outer_visible: &VisibleGlobals,
        observations: impl IntoIterator<Item = &'a GlobalObservation>,
    ) -> MissingGlobals {
        let mut missing = MissingGlobals::default();
        for observation in observations {
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

/// 比较扩域前后每个 global 访问的许可，不能用整个表达式是否有效代替逐访问结果。
/// 两次遍历使用同一表达式和共享 visitor 顺序，只回退期间新增的词法声明，不复制祖先环境。
pub(in crate::ast::readability) fn extending_global_scope_preserves_expr(
    incoming: &mut VisibleGlobals,
    extending_stmts: &[AstStmt],
    expr: &AstExpr,
) -> bool {
    let mut permissions = Vec::new();
    visit_global_permissions(expr, incoming, |allowed| permissions.push(allowed));
    let checkpoint = incoming.checkpoint();
    for stmt in extending_stmts {
        incoming.apply_stmt(stmt);
    }
    let mut permissions = permissions.into_iter();
    let mut equal = true;
    visit_global_permissions(expr, incoming, |allowed| {
        equal &= permissions.next() == Some(allowed);
    });
    incoming.restore(checkpoint);
    equal && permissions.next().is_none()
}

fn visit_global_permissions(
    expr: &AstExpr,
    globals: &mut VisibleGlobals,
    record: impl FnMut(bool),
) {
    let mut visitor = GlobalPermissionVisitor {
        globals,
        record,
        repeat_scopes: Vec::new(),
        repeat_body_pending: false,
    };
    visit::visit_expr(expr, &mut visitor);
}

struct GlobalPermissionVisitor<'a, F> {
    globals: &'a mut VisibleGlobals,
    record: F,
    repeat_scopes: Vec<<VisibleGlobals as RewriteScope>::Checkpoint>,
    repeat_body_pending: bool,
}

impl<F: FnMut(bool)> GlobalPermissionVisitor<'_, F> {
    fn access(&mut self, name: &str, kind: GlobalObservationKind) {
        (self.record)(global_access_is_allowed(self.globals, name, kind));
    }
}

impl<F: FnMut(bool)> AstVisitor for GlobalPermissionVisitor<'_, F> {
    fn visit_block(&mut self, block: &AstBlock, _kind: BlockKind) -> bool {
        // 共享遍历保证 Repeat 的第一个 child 是 body。其声明须保留到 until 结束，
        // 普通 block（包括条件里的闭包）则在自身出口回退。
        let repeat_body = std::mem::take(&mut self.repeat_body_pending);
        let checkpoint = self.globals.checkpoint();
        for stmt in &block.stmts {
            visit::visit_stmt(stmt, self);
        }
        if !repeat_body {
            self.globals.restore(checkpoint);
        }
        false
    }

    fn visit_stmt(&mut self, stmt: &AstStmt) {
        self.globals.enter_stmt_children(stmt);
        match stmt {
            AstStmt::Repeat(_) => {
                self.repeat_scopes.push(self.globals.checkpoint());
                self.repeat_body_pending = true;
            }
            AstStmt::FunctionDecl(decl) => {
                if let Some(name) = global_function_root_read(decl) {
                    self.access(name, GlobalObservationKind::Read);
                }
            }
            _ => {}
        }
    }

    fn leave_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::Repeat(_) => self.globals.restore(self.repeat_scopes.pop().unwrap()),
            AstStmt::GlobalDecl(_) => self.globals.apply_stmt(stmt),
            _ => {}
        }
    }

    fn visit_expr(&mut self, expr: &AstExpr) {
        if let AstExpr::Var(AstNameRef::Global(name)) = expr {
            self.access(&name.text, GlobalObservationKind::Read);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &AstLValue) {
        if let AstLValue::Name(AstNameRef::Global(name)) = lvalue {
            self.access(&name.text, GlobalObservationKind::Write);
        }
    }
}
