//! 这个子模块负责 `global_decl_pretty` pass 的事实收集。
//!
//! 它依赖共享 visitor 在一次遍历里收集“显式 global、嵌套函数写入、读写观测”，不会在这里
//! 直接插入或合并声明。
//! 例如：块里读到 `print`、写到 `installer` 时，这里会分别记成常量/可写观测；
//! 如果块里显式出现了 `global *`，这里也会把 collective gate 作为正式作用域事实留下来。

use std::collections::BTreeSet;

use crate::ast::common::{
    AstBlock, AstExpr, AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstGlobalAttr,
    AstGlobalBindingTarget, AstLValue, AstNameRef, AstStmt,
};

use super::super::visit::{self, AstVisitor};

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
}

pub(super) struct BlockFacts {
    explicit_here: BTreeSet<String>,
    explicit_collective_here: Option<AstGlobalAttr>,
    nested_written_here: BTreeSet<String>,
    observations: Vec<GlobalObservation>,
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
        }
    }

    pub(super) fn infer_missing(&self, outer_visible: &VisibleGlobals) -> MissingGlobals {
        let mut missing = MissingGlobals::default();
        let visible_collective =
            merge_collective_attr(outer_visible.collective(), self.explicit_collective_here);
        for observation in &self.observations {
            if outer_visible.contains_name(&observation.name)
                || self.explicit_here.contains(&observation.name)
            {
                continue;
            }
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

    pub(super) fn visible_globals(
        &self,
        outer_visible: &VisibleGlobals,
        missing: &MissingGlobals,
    ) -> VisibleGlobals {
        let mut visible = outer_visible.clone();
        visible.names.extend(self.explicit_here.iter().cloned());
        visible.names.extend(missing.none.iter().cloned());
        visible.names.extend(missing.const_.iter().cloned());
        visible.collective =
            merge_collective_attr(visible.collective, self.explicit_collective_here);
        visible
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
}

#[derive(Default)]
struct GlobalFactsCollector {
    explicit_here: BTreeSet<String>,
    explicit_collective_here: Option<AstGlobalAttr>,
    nested_written_here: BTreeSet<String>,
    observations: Vec<GlobalObservation>,
    function_depth: usize,
}

impl GlobalFactsCollector {
    fn note_observation(&mut self, name: &str, kind: GlobalObservationKind) {
        self.observations.push(GlobalObservation {
            name: name.to_owned(),
            kind,
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
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::GlobalDecl(global_decl) => {
                if self.function_depth == 0 {
                    Self::note_global_decl_bindings(
                        &global_decl.bindings,
                        &mut self.explicit_here,
                        &mut self.explicit_collective_here,
                    );
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
                        self.explicit_here.insert(name);
                    } else {
                        self.nested_written_here.insert(name);
                    }
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
            | AstStmt::Label(_) => {}
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

fn global_declared_name(function_decl: &AstFunctionDecl) -> Option<String> {
    let path = match &function_decl.target {
        AstFunctionName::Plain(path) | AstFunctionName::Method(path, _) => path,
    };
    match &path.root {
        AstNameRef::Global(global) => Some(global.text.clone()),
        _ => None,
    }
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
