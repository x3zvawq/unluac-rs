//! 这个子模块负责 `global_decl_pretty` pass 的事实收集。
//!
//! 它依赖共享 visitor 的 block pruning 在一次遍历里收集“当前 block 的显式 global、直属
//! 闭包写入、当前 block 的读写观测”，不会把普通子 block 的 gate 提升到父作用域，也不会
//! 在这里直接插入或合并声明。观测还会记录它位于当前 block 首个显式 gate 的前后，避免
//! 把隐式 `global *` 区域误算成受后续声明约束。
//! 例如：块里读到 `print`、写到 `installer` 时，这里会分别记成常量/可写观测；
//! 如果块里显式出现了 `global *`，这里也会把 collective gate 作为正式作用域事实留下来。

use std::collections::BTreeSet;

use crate::ast::common::{
    AstBlock, AstExpr, AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstGlobalAttr,
    AstGlobalBindingTarget, AstLValue, AstNameRef, AstStmt,
};

use super::super::visit::{self, AstVisitor};
use super::super::walk::BlockKind;

#[derive(Clone, Default)]
pub(super) struct VisibleGlobals {
    names: BTreeSet<String>,
    collective: Option<AstGlobalAttr>,
}

impl VisibleGlobals {
    pub(super) fn has_explicit_gate(&self) -> bool {
        self.collective.is_some() || !self.names.is_empty()
    }

    fn contains_name(&self, name: &str) -> bool {
        self.names.contains(name)
    }

    fn collective(&self) -> Option<AstGlobalAttr> {
        self.collective
    }

    pub(super) fn after_stmt(&self, stmt: &AstStmt) -> Self {
        let mut visible = self.clone();
        match stmt {
            AstStmt::GlobalDecl(decl) => GlobalFactsCollector::note_global_decl_bindings(
                &decl.bindings,
                &mut visible.names,
                &mut visible.collective,
            ),
            AstStmt::FunctionDecl(function) => {
                if let Some(name) = global_declared_name(function) {
                    visible.names.insert(name.to_owned());
                }
            }
            _ => {}
        }
        visible
    }
}

pub(super) struct BlockFacts {
    explicit_here: BTreeSet<String>,
    explicit_collective_here: Option<AstGlobalAttr>,
    nested_written_here: BTreeSet<String>,
    observations: Vec<GlobalObservation>,
    first_explicit_index: Option<usize>,
}

impl BlockFacts {
    pub(super) fn collect(block: &AstBlock) -> Self {
        let mut collector = GlobalFactsCollector::default();
        visit::visit_block(block, &mut collector);

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
            if outer_visible.contains_name(&observation.name) || observation.explicit_name_here {
                continue;
            }
            let visible_collective = merge_collective_attr(
                outer_visible.collective(),
                observation.explicit_collective_here,
            );
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
            if observation.kind == GlobalObservationKind::Write
                || self.nested_written_here.contains(&observation.name)
            {
                missing.note_none(&observation.name);
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
}

impl MissingGlobals {
    pub(super) fn is_empty(&self) -> bool {
        self.none.is_empty() && self.const_.is_empty()
    }

    fn note_none(&mut self, name: &str) {
        if self.seen_none.insert(name.to_owned()) {
            self.none.push(name.to_owned());
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
    explicit_name_here: bool,
    explicit_collective_here: Option<AstGlobalAttr>,
}

#[derive(Default)]
struct GlobalFactsCollector {
    explicit_here: BTreeSet<String>,
    explicit_collective_here: Option<AstGlobalAttr>,
    nested_written_here: BTreeSet<String>,
    observations: Vec<GlobalObservation>,
    function_depth: usize,
    root_seen: bool,
    direct_explicit_active: bool,
    pending_direct_global_decl: bool,
    active_explicit_names: BTreeSet<String>,
    active_explicit_collective: Option<AstGlobalAttr>,
}

impl GlobalFactsCollector {
    fn note_observation(&mut self, name: &str, kind: GlobalObservationKind) {
        self.observations.push(GlobalObservation {
            name: name.to_owned(),
            kind,
            after_explicit_here: self.direct_explicit_active,
            explicit_name_here: self.active_explicit_names.contains(name),
            explicit_collective_here: self.active_explicit_collective,
        });
    }

    fn note_global_decl_bindings(
        bindings: &[crate::ast::common::AstGlobalBinding],
        names: &mut BTreeSet<String>,
        collective: &mut Option<AstGlobalAttr>,
    ) {
        for binding in bindings {
            match &binding.target {
                AstGlobalBindingTarget::Name(name) => {
                    names.insert(name.text.clone());
                }
                AstGlobalBindingTarget::Wildcard => {
                    *collective = merge_collective_attr(*collective, Some(binding.attr));
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
                    let mut nested_collective = None;
                    Self::note_global_decl_bindings(
                        &global_decl.bindings,
                        &mut self.nested_written_here,
                        &mut nested_collective,
                    );
                }
            }
            AstStmt::FunctionDecl(function_decl) => {
                if let Some(name) = global_declared_name(function_decl) {
                    if self.function_depth == 0 {
                        self.explicit_here.insert(name.to_owned());
                        self.active_explicit_names.insert(name.to_owned());
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

fn merge_collective_attr(
    current: Option<AstGlobalAttr>,
    next: Option<AstGlobalAttr>,
) -> Option<AstGlobalAttr> {
    match (current, next) {
        (Some(AstGlobalAttr::None), _) | (_, Some(AstGlobalAttr::None)) => {
            Some(AstGlobalAttr::None)
        }
        (Some(AstGlobalAttr::Const), _) | (_, Some(AstGlobalAttr::Const)) => {
            Some(AstGlobalAttr::Const)
        }
        (None, None) => None,
    }
}
