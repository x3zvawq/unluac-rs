//! 按最终 AST 定义位置查询已分配名字的外层可见性。
//!
//! 消费 lexical 区间与父函数 NameMap，供参数和局部命名避让。

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

    fn insert(&mut self, name: &str, mut range: Range<usize>) {
        let ranges = if let Some(ranges) = self.ranges.get_mut(name) {
            ranges
        } else {
            self.ranges.entry(name.to_owned()).or_default()
        };
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
