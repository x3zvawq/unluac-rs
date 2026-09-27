//! HIR 构建与 simplify 共用的定点表达式替换。
//!
//! 调用方先证明替换合法，本模块只消费 single 或 substitution DAG，按共享 HIR 子节点
//! 定义替换并返回次数。它不重建 reaching-def、root lifetime 或协议归属。
//! single 不进入刚插入的值；DAG 按活动路径展开，成本随实际输出增长，不反复扫描 sink。
//! 例如 `t2 -> t1 -> value` 的批量替换产生 value 并计两次，单次 `t2 -> t1` 只计一次。
//! capture 只替换父级绑定身份；pack tail 保持 Call/VarArg 宽度。赋值目标的替换次数和
//! generic-for iterator 的前后区间分别交给原有 producer 失效规则，不互相代替。

use std::collections::{BTreeMap, BTreeSet};

use super::traverse::{
    traverse_hir_call_children, traverse_hir_decision_children, traverse_hir_expr_children,
    traverse_hir_lvalue_children, traverse_hir_stmt_children,
    traverse_hir_table_constructor_children, traverse_hir_value_pack_children,
};
use super::{
    HirBinding, HirBlock, HirCallExpr, HirCapture, HirExpr, HirLValue, HirStmt, HirValuePack,
    TempId,
};

pub(crate) fn replace_temp_in_expr(
    expr: &mut HirExpr,
    temp: TempId,
    replacement: &HirExpr,
) -> usize {
    SingleReplacement { temp, replacement }.expr(expr)
}

/// 消费调用方已证明的读取身份；参数或循环 binding 不一定使用 TempRef。
pub(crate) fn replace_binding_in_expr(
    expr: &mut HirExpr,
    binding: HirBinding,
    replacement: &HirExpr,
) -> usize {
    BindingReplacement {
        binding,
        replacement,
    }
    .expr(expr)
}

struct BindingReplacement<'a> {
    binding: HirBinding,
    replacement: &'a HirExpr,
}

impl Substitution for BindingReplacement<'_> {
    fn replace_temp(&mut self, temp: TempId) -> Option<(HirExpr, usize)> {
        self.replace_binding(HirBinding::Temp(temp))
    }

    fn replace_binding(&mut self, binding: HirBinding) -> Option<(HirExpr, usize)> {
        (binding == self.binding).then(|| (self.replacement.clone(), 1))
    }
}

pub(crate) fn replace_temp_in_stmt(stmt: &mut HirStmt, temp: TempId, replacement: &HirExpr) {
    SingleReplacement { temp, replacement }.stmt(stmt);
}

/// 调用方须先证明 map 无环；逐引用展开，不为每个 map key 重扫增长中的 sink。
pub(crate) fn replace_temps_in_stmt(
    stmt: &mut HirStmt,
    replacements: &BTreeMap<TempId, HirExpr>,
) -> usize {
    ReplacementDag {
        replacements,
        active: BTreeSet::new(),
    }
    .stmt(stmt)
}

struct SingleReplacement<'a> {
    temp: TempId,
    replacement: &'a HirExpr,
}

impl Substitution for SingleReplacement<'_> {
    fn replace_temp(&mut self, temp: TempId) -> Option<(HirExpr, usize)> {
        (temp == self.temp).then(|| (self.replacement.clone(), 1))
    }
}

struct ReplacementDag<'a> {
    replacements: &'a BTreeMap<TempId, HirExpr>,
    active: BTreeSet<TempId>,
}

impl Substitution for ReplacementDag<'_> {
    fn replace_temp(&mut self, temp: TempId) -> Option<(HirExpr, usize)> {
        let replacement = self.replacements.get(&temp)?;
        // 活动路径的重入边保留原引用且不计数；合法调用方已在构造 DAG 时排除环。
        if !self.active.insert(temp) {
            return None;
        }
        let mut expanded = replacement.clone();
        let nested = self.expr(&mut expanded);
        self.active.remove(&temp);
        Some((expanded, 1 + nested))
    }
}

/// 两种代换只决定如何展开一个 Temp，节点关系与提交边界使用同一实现。
trait Substitution {
    fn replace_temp(&mut self, temp: TempId) -> Option<(HirExpr, usize)>;

    fn replace_binding(&mut self, binding: HirBinding) -> Option<(HirExpr, usize)> {
        match binding {
            HirBinding::Temp(temp) => self.replace_temp(temp),
            _ => None,
        }
    }

    fn expr(&mut self, expr: &mut HirExpr) -> usize {
        if let Some(binding) = HirBinding::from_expr(expr)
            && let Some((replacement, count)) = self.replace_binding(binding)
        {
            *expr = replacement;
            return count;
        }
        let mut count = 0;
        traverse_hir_expr_children!(
            expr, iter = iter_mut, borrow = [&mut],
            expr(child) => { count += self.expr(child); },
            call(call) => { count += self.call(call); },
            decision(decision) => {
                traverse_hir_decision_children!(
                    decision, iter = iter_mut, borrow = [&mut],
                    expr(child) => { count += self.expr(child); },
                    condition(child) => { count += self.expr(child); }
                );
            },
            table_constructor(table) => {
                traverse_hir_table_constructor_children!(
                    table, iter = iter_mut, opt = as_mut, borrow = [&mut],
                    expr(child) => { count += self.expr(child); },
                    tail_call(call) => { count += self.call(call); }
                );
            },
            capture(capture) => { count += self.capture(capture); }
        );
        count
    }

    fn capture(&mut self, capture: &mut HirCapture) -> usize {
        let HirBinding::Temp(temp) = capture.binding else {
            return 0;
        };
        let Some((replacement, count)) = self.replace_temp(temp) else {
            return 0;
        };
        capture.binding = HirBinding::from_expr(&replacement)
            .expect("capture replacement must preserve parent binding identity");
        count
    }

    fn call(&mut self, call: &mut HirCallExpr) -> usize {
        let mut count = 0;
        traverse_hir_call_children!(
            call, iter = iter_mut, borrow = [&mut],
            expr(expr) => { count += self.expr(expr); },
            tail_call(call) => { count += self.call(call); }
        );
        count
    }

    fn value_pack(&mut self, pack: &mut HirValuePack) -> usize {
        let mut count = 0;
        traverse_hir_value_pack_children!(
            pack, iter = iter_mut,
            expr(expr) => { count += self.expr(expr); },
            call(call) => { count += self.call(call); }
        );
        count
    }

    fn lvalue(&mut self, lvalue: &mut HirLValue) -> usize {
        let mut count = 0;
        traverse_hir_lvalue_children!(
            lvalue, borrow = [&mut], expr(expr) => { count += self.expr(expr); }
        );
        count
    }

    fn block(&mut self, block: &mut HirBlock) -> usize {
        block.stmts.iter_mut().map(|stmt| self.stmt(stmt)).sum()
    }

    fn stmt(&mut self, stmt: &mut HirStmt) -> usize {
        match stmt {
            HirStmt::Assign(assign) => {
                let targets = assign
                    .targets
                    .iter_mut()
                    .map(|target| self.lvalue(target))
                    .sum::<usize>();
                if targets != 0 {
                    assign.generic_for_initializer_producer = None;
                }
                return targets + self.value_pack(&mut assign.values);
            }
            HirStmt::GenericFor(generic_for) => {
                let iterator = generic_for.rewrite_iterator(|iterator| self.value_pack(iterator));
                return iterator + self.block(&mut generic_for.body);
            }
            _ => {}
        }
        let mut count = 0;
        traverse_hir_stmt_children!(
            stmt, iter = iter_mut, opt = as_mut, borrow = [&mut],
            expr(expr) => { count += self.expr(expr); },
            tail_call(call) => { count += self.call(call); },
            lvalue(lvalue) => { count += self.lvalue(lvalue); },
            release(_local) => {},
            block(block) => { count += self.block(block); },
            call(call) => { count += self.call(call); },
            condition(expr) => { count += self.expr(expr); }
        );
        count
    }
}
