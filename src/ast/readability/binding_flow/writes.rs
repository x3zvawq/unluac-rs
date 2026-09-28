//! 当前 AST 语句快照的名字写入与重绑定位置索引。
//!
//! 消费共享访问角色，供区间查询使用；不进入 child function 或推断闭包潜在写入。

use std::collections::BTreeMap;
use std::ops::ControlFlow;

use crate::ast::common::{AstBindingRef, AstFunctionExpr, AstNameRef, AstStmt};
use crate::ast::visit::{self, AstVisitor, NameAccess};

#[derive(Default)]
struct NameWrites {
    assignments: Vec<usize>,
    last_function_declaration: Option<usize>,
}

#[derive(Default)]
pub(in crate::ast::readability) struct BindingWriteIndex {
    names: BTreeMap<AstNameRef, NameWrites>,
}

impl BindingWriteIndex {
    pub(in crate::ast::readability) fn for_stmts(stmts: &[AstStmt]) -> Self {
        let mut index = Self::default();
        for (stmt_index, stmt) in stmts.iter().enumerate() {
            visit::visit_stmt(
                stmt,
                &mut WriteCollector {
                    stmt_index,
                    index: &mut index,
                },
            );
        }
        index
    }

    fn assignments(&self, name: &AstNameRef) -> &[usize] {
        self.names
            .get(name)
            .map_or(&[], |writes| writes.assignments.as_slice())
    }

    pub(in crate::ast::readability) fn stmt_directly_writes_name(
        &self,
        stmt_index: usize,
        name: &AstNameRef,
    ) -> bool {
        self.assignments(name).binary_search(&stmt_index).is_ok()
    }

    pub(in crate::ast::readability) fn has_write_after(
        &self,
        stmt_index: usize,
        binding: AstBindingRef,
    ) -> bool {
        self.name_has_write_after(stmt_index, &binding.to_name_ref())
    }

    pub(in crate::ast::readability) fn writes_only_at(
        &self,
        stmt_index: usize,
        binding: AstBindingRef,
    ) -> bool {
        self.assignments(&binding.to_name_ref()) == [stmt_index]
    }

    pub(in crate::ast::readability) fn name_has_write_after(
        &self,
        stmt_index: usize,
        name: &AstNameRef,
    ) -> bool {
        self.assignments(name)
            .last()
            .is_some_and(|last| *last > stmt_index)
    }

    pub(in crate::ast::readability) fn name_has_write_in_range(
        &self,
        start: usize,
        end: usize,
        name: &AstNameRef,
    ) -> bool {
        let writes = self.assignments(name);
        writes
            .get(writes.partition_point(|index| *index < start))
            .is_some_and(|index| *index < end)
    }

    pub(in crate::ast::readability) fn name_write_indices_after(
        &self,
        stmt_index: usize,
        name: &AstNameRef,
    ) -> &[usize] {
        let writes = self.assignments(name);
        &writes[writes.partition_point(|index| *index <= stmt_index)..]
    }

    pub(in crate::ast::readability) fn writes_start_after(
        &self,
        stmt_index: usize,
        binding: AstBindingRef,
    ) -> bool {
        self.assignments(&binding.to_name_ref())
            .first()
            .is_some_and(|first| *first > stmt_index)
    }

    pub(in crate::ast::readability) fn has_rebinding_after(
        &self,
        stmt_index: usize,
        binding: AstBindingRef,
    ) -> bool {
        self.name_has_rebinding_after(stmt_index, &binding.to_name_ref())
    }

    /// 删除声明必须同时排除后续赋值与 local function 的同身份定义。
    pub(in crate::ast::readability) fn name_has_rebinding_after(
        &self,
        stmt_index: usize,
        name: &AstNameRef,
    ) -> bool {
        self.names.get(name).is_some_and(|writes| {
            writes
                .assignments
                .last()
                .is_some_and(|last| *last > stmt_index)
                || writes
                    .last_function_declaration
                    .is_some_and(|last| last > stmt_index)
        })
    }
}

struct WriteCollector<'a> {
    stmt_index: usize,
    index: &'a mut BindingWriteIndex,
}

impl WriteCollector<'_> {
    fn record_assignment(&mut self, name: &AstNameRef) {
        let writes = &mut self
            .index
            .names
            .entry(name.clone())
            .or_default()
            .assignments;
        if writes.last() != Some(&self.stmt_index) {
            writes.push(self.stmt_index);
        }
    }
}

impl AstVisitor for WriteCollector<'_> {
    fn visit_name(&mut self, name: &AstNameRef, access: NameAccess) -> ControlFlow<()> {
        match access {
            NameAccess::Write => self.record_assignment(name),
            NameAccess::LocalFunctionDeclaration => {
                self.index
                    .names
                    .entry(name.clone())
                    .or_default()
                    .last_function_declaration = Some(self.stmt_index);
            }
            _ => {}
        }
        ControlFlow::Continue(())
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}
