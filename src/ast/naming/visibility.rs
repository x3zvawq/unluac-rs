//! 按最终 AST 定义位置查询已分配名字的外层可见性。
//!
//! lexical 发布绑定的有效区间，父函数完成 NameMap 后才把区间关联到最终名字。
//! 同名区间合并为不相交集合，查询不再复制或遍历祖先绑定；例如 `do local a;
//! f = function() end end; g = function() end` 只让 f 的参数避让 a。
//! 名字仍按 HIR proto 顺序分配，因此区间必须支持任意顺序插入。

use std::collections::BTreeMap;
use std::ops::Range;

use crate::hir::HirProtoRef;

use super::NamingError;
use super::common::FunctionNameMap;
use super::lexical::FunctionLexicalContext;
use super::strategy::resolve_visible_binding_name;

#[derive(Default)]
pub(super) struct VisibleNames {
    ranges: BTreeMap<String, BTreeMap<usize, usize>>,
}

impl VisibleNames {
    pub(super) fn publish(
        &mut self,
        function: HirProtoRef,
        lexical: &FunctionLexicalContext,
        assigned_functions: &[FunctionNameMap],
    ) -> Result<(), NamingError> {
        for (binding, range) in &lexical.visible_bindings {
            if !range.is_empty() {
                let name = resolve_visible_binding_name(function, *binding, assigned_functions)?;
                self.insert(name, range.clone());
            }
        }
        Ok(())
    }

    pub(super) fn contains(&self, name: &str, position: usize) -> bool {
        self.ranges
            .get(name)
            .and_then(|ranges| ranges.range(..=position).next_back())
            .is_some_and(|(_, &end)| position < end)
    }

    fn insert(&mut self, name: String, mut range: Range<usize>) {
        let ranges = self.ranges.entry(name).or_default();
        if let Some((&start, &end)) = ranges.range(..=range.start).next_back()
            && end >= range.start
        {
            ranges.remove(&start);
            range.start = start;
            range.end = range.end.max(end);
        }
        while let Some((&start, &end)) = ranges.range(range.start..=range.end).next() {
            ranges.remove(&start);
            range.end = range.end.max(end);
        }
        ranges.insert(range.start, range.end);
    }
}
