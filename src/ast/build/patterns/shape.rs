//! 这里收的是仍然必须留在 AST build 的“语义保真形状恢复”。
//!
//! 它们和 `installer_iife` 这类纯可读性 sugar 不一样：一旦离开 HIR，这些事实就会丢失，
//! 后面的 Readability/Generate 也无法再猜回来。

use crate::hir::{HirCallExpr, HirExpr, HirStmt, LocalId};

use super::super::{AstLowerError, AstLowerer};
use crate::ast::common::{AstCallKind, AstCallStmt, AstExpr, AstStmt};

impl<'a> AstLowerer<'a> {
    pub(in crate::ast::build) fn try_lower_forwarded_multiret_call_stmt(
        &mut self,
        proto_index: usize,
        stmts: &[HirStmt],
        index: usize,
    ) -> Result<Option<(AstStmt, usize)>, AstLowerError> {
        // 形如
        // `local x = probe(); print(tag, x)`
        // 在 HIR 里还能看见 `probe()` 是 multiret carrier，AST 如果错过这一层，
        // 后面只剩一个普通 `local x = call`，就再也分不清它到底该不该回收到 final arg。
        let Some(HirStmt::LocalDecl(local_decl)) = stmts.get(index) else {
            return Ok(None);
        };
        let [binding] = local_decl.bindings.as_slice() else {
            return Ok(None);
        };
        let [HirExpr::Call(source_call)] = local_decl.values.as_slice() else {
            return Ok(None);
        };
        if !source_call.multiret {
            return Ok(None);
        }

        let Some(HirStmt::CallStmt(call_stmt)) = stmts.get(index + 1) else {
            return Ok(None);
        };
        if super::super::analysis::count_local_uses_in_stmts(&stmts[(index + 1)..], *binding) != 1
            || !call_stmt_uses_local_as_final_arg_only(&call_stmt.call, *binding)
        {
            return Ok(None);
        }

        let mut forwarded_call = call_stmt.call.clone();
        let Some(last_arg) = forwarded_call.args.last_mut() else {
            return Ok(None);
        };
        *last_arg = HirExpr::Call(Box::new((**source_call).clone()));

        Ok(Some((
            AstStmt::CallStmt(Box::new(AstCallStmt {
                call: self.lower_call(proto_index, &forwarded_call)?,
            })),
            2,
        )))
    }

    pub(in crate::ast::build) fn try_lower_single_value_final_call_arg_stmt(
        &mut self,
        proto_index: usize,
        stmts: &[HirStmt],
        index: usize,
    ) -> Result<Option<(AstStmt, usize)>, AstLowerError> {
        let Some(HirStmt::CallStmt(call_stmt)) = stmts.get(index) else {
            return Ok(None);
        };
        let Some(HirExpr::Call(arg_call)) = call_stmt.call.args.last() else {
            return Ok(None);
        };
        if arg_call.multiret {
            return Ok(None);
        }

        // Lua/Luau 只有“语法上的最后一个调用参数”会展开多返回。
        // HIR 里这里已经明确是单值调用；如果 AST 不把这个事实继续带下去，
        // 后面的 Generate 看到 `print(x, values())` 时就分不清这里是单值还是展开调用。
        let mut lowered_call = self.lower_call(proto_index, &call_stmt.call)?;
        let lowered_last_arg = AstExpr::SingleValue(Box::new(
            self.lower_expr(
                proto_index,
                call_stmt
                    .call
                    .args
                    .last()
                    .expect("checked above, final arg must exist"),
            )?,
        ));

        match &mut lowered_call {
            AstCallKind::Call(call) => {
                let last_arg = call
                    .args
                    .last_mut()
                    .expect("final arg must still exist after lower_call");
                *last_arg = lowered_last_arg;
            }
            AstCallKind::MethodCall(call) => {
                let last_arg = call
                    .args
                    .last_mut()
                    .expect("final arg must still exist after lower_call");
                *last_arg = lowered_last_arg;
            }
        }

        Ok(Some((
            AstStmt::CallStmt(Box::new(AstCallStmt { call: lowered_call })),
            1,
        )))
    }
}

fn call_stmt_uses_local_as_final_arg_only(call: &HirCallExpr, local: LocalId) -> bool {
    matches!(
        call.args.last(),
        Some(HirExpr::LocalRef(last_local)) if *last_local == local
    ) && super::super::analysis::count_local_uses_in_call(call, local) == 1
}
