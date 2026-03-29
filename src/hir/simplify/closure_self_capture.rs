//! 这个文件负责把递归闭包初始化里残留的“自引用 temp”认回真实 binding。
//!
//! Lua 会先为递归局部函数准备一个自引用槽位，再把 closure 本体写回这个槽位。
//! HIR lowering 里这条关系最初只能安全地表示成一个 `TempRef` capture；如果后面不把它
//! 收回真实 binding，Naming/AST 只能把它当普通 upvalue，最终就会输出成 `u0(...)`。
//!
//! 这里不做宽泛猜测，只处理一个非常窄的结构：
//! - closure 直接作为某个 local/assign 的初始化值
//! - capture 里出现了一个在当前 proto 里从未被任何语句显式定义过的 temp
//!
//! 这种“悬空 temp”正是递归 self slot 在 HIR 里的残影，把它改写成当前初始化目标，
//! 后面的 AST/Readability/Naming 就都能看到稳定的绑定身份。

use std::collections::BTreeSet;

use crate::hir::common::{HirExpr, HirLValue, HirProto, HirStmt, TempId};

use super::visit::{HirVisitor, visit_proto};
use super::walk::{HirRewritePass, rewrite_proto};

pub(super) fn resolve_recursive_closure_self_captures_in_proto(proto: &mut HirProto) -> bool {
    let defined_temps = collect_defined_temps(proto);
    let mut pass = RecursiveClosureSelfCapturePass {
        defined_temps: &defined_temps,
    };
    rewrite_proto(proto, &mut pass)
}

struct RecursiveClosureSelfCapturePass<'a> {
    defined_temps: &'a BTreeSet<TempId>,
}

impl HirRewritePass for RecursiveClosureSelfCapturePass<'_> {
    fn rewrite_stmt(&mut self, stmt: &mut HirStmt) -> bool {
        match stmt {
            HirStmt::LocalDecl(local_decl)
                if local_decl.bindings.len() == 1 && local_decl.values.len() == 1 =>
            {
                rewrite_closure_self_captures(
                    &mut local_decl.values[0],
                    HirExpr::LocalRef(local_decl.bindings[0]),
                    self.defined_temps,
                )
            }
            HirStmt::Assign(assign) if assign.targets.len() == 1 && assign.values.len() == 1 => {
                let Some(binding_expr) = lvalue_as_expr(&assign.targets[0]) else {
                    return false;
                };
                rewrite_closure_self_captures(
                    &mut assign.values[0],
                    binding_expr,
                    self.defined_temps,
                )
            }
            _ => false,
        }
    }
}

fn rewrite_closure_self_captures(
    expr: &mut HirExpr,
    replacement: HirExpr,
    defined_temps: &BTreeSet<TempId>,
) -> bool {
    let HirExpr::Closure(closure) = expr else {
        return false;
    };

    let mut changed = false;
    for capture in &mut closure.captures {
        let HirExpr::TempRef(temp) = capture.value else {
            continue;
        };
        if defined_temps.contains(&temp) {
            continue;
        }
        capture.value = replacement.clone();
        changed = true;
    }
    changed
}

fn lvalue_as_expr(target: &HirLValue) -> Option<HirExpr> {
    match target {
        HirLValue::Temp(temp) => Some(HirExpr::TempRef(*temp)),
        HirLValue::Local(local) => Some(HirExpr::LocalRef(*local)),
        HirLValue::Upvalue(upvalue) => Some(HirExpr::UpvalueRef(*upvalue)),
        HirLValue::Global(global) => Some(HirExpr::GlobalRef(global.clone())),
        HirLValue::TableAccess(_) => None,
    }
}

fn collect_defined_temps(proto: &HirProto) -> BTreeSet<TempId> {
    let mut collector = DefinedTempCollector::default();
    visit_proto(proto, &mut collector);
    collector.defined
}

#[derive(Default)]
struct DefinedTempCollector {
    defined: BTreeSet<TempId>,
}

impl HirVisitor for DefinedTempCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::Assign(assign) = stmt else {
            return;
        };
        for target in &assign.targets {
            if let HirLValue::Temp(temp) = target {
                self.defined.insert(*temp);
            }
        }
    }
}

#[cfg(test)]
mod tests;
