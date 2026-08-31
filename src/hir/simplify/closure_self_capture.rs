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
                if local_decl.bindings.len() == 1
                    && local_decl.values.tail.is_none()
                    && local_decl.values.fixed.len() == 1 =>
            {
                rewrite_closure_self_captures(
                    &mut local_decl.values.fixed[0],
                    HirExpr::LocalRef(local_decl.bindings[0]),
                    self.defined_temps,
                )
            }
            HirStmt::Assign(assign)
                if assign.targets.len() == 1
                    && assign.values.tail.is_none()
                    && assign.values.fixed.len() == 1 =>
            {
                // 证明缺陷[PotentialUnsoundness:Capture]：仅凭“closure 当前被赋给该 lvalue”就把 target 当原 self slot，缺少 closure-result origin/home；producer 被前轮内联到 global/upvalue/另一 local 后会把稳定 self cell 错换成可变目标 binding。
                // 候选拒绝[SemanticBarrier:Capture]：table lvalue 不建立可捕获 binding；把
                // `t[k] = closure` 的悬空 capture 改成 `t[k]` 会新增可触发 `__index` 的读取，
                // 且该读取不保证仍返回刚写入的 closure。
                let Some(binding_expr) = lvalue_as_expr(&assign.targets[0]) else {
                    return false;
                };
                rewrite_closure_self_captures(
                    &mut assign.values.fixed[0],
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
        // 候选拒绝[SemanticBarrier:Capture]：已定义 temp 是普通捕获值而非递归 self 槽；
        // `temp = 1; local f = function() return temp end` 不能把 capture 改成 `f`。
        if defined_temps.contains(&temp) {
            // 候选拒绝[ProofIncomplete]：全 proto defined 集不区分定义在 capture 前后或是否可达；后置/互递归 self def 也会被 blanket 当成普通值，应改用 reaching-def 与 closure-result origin。
            continue;
        }
        // 证明缺陷[PotentialUnsoundness:Capture]：未校验 capture mode 与唯一 self provenance；ByValue self 在目标后来重绑时仍应指向原 closure，改成目标 binding 会观察新值，多个未定义 capture 也会被错误折成同一 cell。
        capture.value = replacement.clone();
        changed = true;
    }
    changed
}

fn lvalue_as_expr(target: &HirLValue) -> Option<HirExpr> {
    match target {
        HirLValue::Param(param) => Some(HirExpr::ParamRef(*param)),
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
