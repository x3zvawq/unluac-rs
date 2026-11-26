//! 轻量 AST 语法糖整理与词法作用域修复（最多 2 轮即可收敛，彻底告别 20-pass 固定点泥潭）。
//!
//! 负责：
//! - 安全短路值表达折叠（`a or b`、`a and b`、严格守住 falsy 陷阱的 `cond and a or b`）
//! - `local f; f = function(...)` → `local function f(...)`
//! - 去除冗余末尾裸 `return`、空 `then` 分支反转（严守 NaN 语义）与冗余 `do ... end`
//! - Lua 5.2+/LuaJIT `goto` 跨局部作用域自动上提修复

use std::collections::{BTreeMap, BTreeSet};

use super::common::{
    AstAssign, AstBindingRef, AstBlock, AstCallExpr, AstCallKind, AstCaptureBinding,
    AstCaptureMode, AstExpr, AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstLValue,
    AstLocalAttr, AstLocalBinding, AstLocalDecl, AstLocalFunctionDecl, AstLogicalExpr, AstModule,
    AstNamePath, AstNameRef, AstProtoMeta, AstStmt, AstTargetDialect, AstUnaryExpr,
    AstUnaryOpKind, ProtoId,
};
use super::error::AstLowerError;
use super::goto_scope;
use super::visit::{ExprNode, expr_nodes};

/// 对 `AstModule` 执行轻量语法整形与 `goto` 作用域自动修复。
pub fn polish_module(
    module: &mut AstModule,
    target: AstTargetDialect,
    mode: crate::generate::GenerateMode,
) -> Result<(), AstLowerError> {
    for _ in 0..8 {
        let captured = collect_captured_names_in_block(&module.body);
        let debug_hinted = collect_debug_hinted_names_in_block(&module.body);
        let mut changed = polish_block(
            &mut module.body,
            target,
            true,
            true,
            &captured,
            &debug_hinted,
        );
        if target.version == crate::decompile::DecompileDialect::Luau {
            changed |= fold_inlined_recursive_closure_factories(
                &mut module.body,
                module.entry_function,
                &module.protos,
                &debug_hinted,
            );
        }
        if !changed {
            break;
        }
    }

    // 对 Lua 5.2+ / LuaJIT 逐函数独立修复向前 goto 跨入 local 作用域的问题
    repair_goto_scopes_in_function(module.entry_function.index(), &mut module.body);

    goto_scope::verify_or_diagnose(module, mode)
}

fn repair_goto_scopes_in_function(function: usize, body: &mut AstBlock) {
    for _ in 0..256 {
        match goto_scope::verify_function_only(function, body) {
            Ok(()) => break,
            Err(AstLowerError::GotoEntersLocalScope {
                function: err_fn,
                binding,
                ..
            }) if err_fn == function => {
                if !hoist_binding_above_goto(body, binding) {
                    break;
                }
            }
            Err(_) => break,
        }
    }
    repair_goto_scopes_in_nested_functions(body);
}

fn repair_goto_scopes_in_nested_functions(block: &mut AstBlock) {
    for stmt in &mut block.stmts {
        match stmt {
            AstStmt::FunctionDecl(d) => {
                repair_goto_scopes_in_function(d.func.function.index(), &mut d.func.body);
            }
            AstStmt::LocalFunctionDecl(d) => {
                repair_goto_scopes_in_function(d.func.function.index(), &mut d.func.body);
            }
            AstStmt::If(if_stmt) => {
                repair_goto_scopes_in_nested_functions(&mut if_stmt.then_block);
                if let Some(eb) = &mut if_stmt.else_block {
                    repair_goto_scopes_in_nested_functions(eb);
                }
                repair_goto_scopes_in_expr(&mut if_stmt.cond);
            }
            AstStmt::While(w) => {
                repair_goto_scopes_in_expr(&mut w.cond);
                repair_goto_scopes_in_nested_functions(&mut w.body);
            }
            AstStmt::Repeat(r) => {
                repair_goto_scopes_in_nested_functions(&mut r.body);
                repair_goto_scopes_in_expr(&mut r.cond);
            }
            AstStmt::NumericFor(nf) => {
                repair_goto_scopes_in_expr(&mut nf.start);
                repair_goto_scopes_in_expr(&mut nf.limit);
                repair_goto_scopes_in_expr(&mut nf.step);
                repair_goto_scopes_in_nested_functions(&mut nf.body);
            }
            AstStmt::GenericFor(gf) => {
                for e in &mut gf.iterator {
                    repair_goto_scopes_in_expr(e);
                }
                repair_goto_scopes_in_nested_functions(&mut gf.body);
            }
            AstStmt::DoBlock(b) => repair_goto_scopes_in_nested_functions(b),
            AstStmt::LocalDecl(d) => {
                for v in &mut d.values {
                    repair_goto_scopes_in_expr(v);
                }
            }
            AstStmt::GlobalDecl(d) => {
                for v in &mut d.values {
                    repair_goto_scopes_in_expr(v);
                }
            }
            AstStmt::Assign(a) => {
                for v in &mut a.values {
                    repair_goto_scopes_in_expr(v);
                }
            }
            AstStmt::Return(r) => {
                for v in &mut r.values {
                    repair_goto_scopes_in_expr(v);
                }
            }
            AstStmt::CallStmt(c) => match &mut c.call {
                super::common::AstCallKind::Call(call) => {
                    repair_goto_scopes_in_expr(&mut call.callee);
                    for a in &mut call.args {
                        repair_goto_scopes_in_expr(a);
                    }
                }
                super::common::AstCallKind::MethodCall(m) => {
                    repair_goto_scopes_in_expr(&mut m.receiver);
                    for a in &mut m.args {
                        repair_goto_scopes_in_expr(a);
                    }
                }
            },
            _ => {}
        }
    }
}

fn repair_goto_scopes_in_expr(expr: &mut AstExpr) {
    use super::traverse::traverse_expr_children;
    traverse_expr_children!(
        expr,
        iter = iter_mut,
        borrow = [&mut],
        expr(child) => { repair_goto_scopes_in_expr(child); },
        function(func) => {
            repair_goto_scopes_in_function(func.function.index(), &mut func.body);
        }
    );
}

/// 收集当前函数体内被任何子闭包捕获的局部/形参名集合（不进入子函数 body）。
fn collect_captured_names_in_block(block: &AstBlock) -> BTreeSet<AstNameRef> {
    let mut out = BTreeSet::new();
    collect_captured_in_block_rec(block, &mut out);
    out
}

fn collect_captured_in_block_rec(block: &AstBlock, out: &mut BTreeSet<AstNameRef>) {
    for stmt in &block.stmts {
        match stmt {
            AstStmt::FunctionDecl(d) => record_func_captures(&d.func, out),
            AstStmt::LocalFunctionDecl(d) => record_func_captures(&d.func, out),
            AstStmt::LocalDecl(d) => {
                for v in &d.values {
                    collect_captured_in_expr(v, out);
                }
            }
            AstStmt::GlobalDecl(d) => {
                for v in &d.values {
                    collect_captured_in_expr(v, out);
                }
            }
            AstStmt::Assign(a) => {
                for v in &a.values {
                    collect_captured_in_expr(v, out);
                }
            }
            AstStmt::CallStmt(c) => match &c.call {
                super::common::AstCallKind::Call(call) => {
                    collect_captured_in_expr(&call.callee, out);
                    for a in &call.args {
                        collect_captured_in_expr(a, out);
                    }
                }
                super::common::AstCallKind::MethodCall(m) => {
                    collect_captured_in_expr(&m.receiver, out);
                    for a in &m.args {
                        collect_captured_in_expr(a, out);
                    }
                }
            },
            AstStmt::Return(r) => {
                for v in &r.values {
                    collect_captured_in_expr(v, out);
                }
            }
            AstStmt::If(if_stmt) => {
                collect_captured_in_expr(&if_stmt.cond, out);
                collect_captured_in_block_rec(&if_stmt.then_block, out);
                if let Some(eb) = &if_stmt.else_block {
                    collect_captured_in_block_rec(eb, out);
                }
            }
            AstStmt::While(w) => {
                collect_captured_in_expr(&w.cond, out);
                collect_captured_in_block_rec(&w.body, out);
            }
            AstStmt::Repeat(r) => {
                collect_captured_in_block_rec(&r.body, out);
                collect_captured_in_expr(&r.cond, out);
            }
            AstStmt::NumericFor(nf) => {
                collect_captured_in_expr(&nf.start, out);
                collect_captured_in_expr(&nf.limit, out);
                collect_captured_in_expr(&nf.step, out);
                collect_captured_in_block_rec(&nf.body, out);
            }
            AstStmt::GenericFor(gf) => {
                for e in &gf.iterator {
                    collect_captured_in_expr(e, out);
                }
                collect_captured_in_block_rec(&gf.body, out);
            }
            AstStmt::DoBlock(b) => collect_captured_in_block_rec(b, out),
            _ => {}
        }
    }
}

fn collect_captured_in_expr(expr: &AstExpr, out: &mut BTreeSet<AstNameRef>) {
    for node in expr_nodes(expr) {
        if let ExprNode::Function(func) = node {
            record_func_captures(func, out);
        }
    }
}

fn record_func_captures(func: &super::common::AstFunctionExpr, out: &mut BTreeSet<AstNameRef>) {
    for &b in &func.captured_bindings {
        out.insert(b.to_name_ref());
    }
    for &p in &func.captured_params {
        out.insert(AstNameRef::Param(p));
    }
}

/// 收集当前函数体内带有源码 debug 名字提示或属性（`<close>`/`<const>`）的局部集合（不进入子函数 body）。
fn collect_debug_hinted_names_in_block(block: &AstBlock) -> BTreeSet<AstNameRef> {
    let mut out = BTreeSet::new();
    collect_debug_hinted_rec(block, &mut out);
    out
}

fn collect_debug_hinted_rec(block: &AstBlock, out: &mut BTreeSet<AstNameRef>) {
    for stmt in &block.stmts {
        match stmt {
            AstStmt::LocalDecl(d) => {
                for b in &d.bindings {
                    if b.is_debug_hinted || b.attr != AstLocalAttr::None {
                        out.insert(b.id.to_name_ref());
                    }
                }
            }
            AstStmt::If(if_stmt) => {
                collect_debug_hinted_rec(&if_stmt.then_block, out);
                if let Some(eb) = &if_stmt.else_block {
                    collect_debug_hinted_rec(eb, out);
                }
            }
            AstStmt::While(w) => collect_debug_hinted_rec(&w.body, out),
            AstStmt::Repeat(r) => collect_debug_hinted_rec(&r.body, out),
            AstStmt::NumericFor(nf) => collect_debug_hinted_rec(&nf.body, out),
            AstStmt::GenericFor(gf) => collect_debug_hinted_rec(&gf.body, out),
            AstStmt::DoBlock(b) => collect_debug_hinted_rec(b, out),
            _ => {}
        }
    }
}

fn polish_block(
    block: &mut AstBlock,
    target: AstTargetDialect,
    is_function_root: bool,
    allow_tail_else_flatten: bool,
    captured: &BTreeSet<AstNameRef>,
    debug_hinted: &BTreeSet<AstNameRef>,
) -> bool {
    let mut changed = false;

    // 1. 递归整理所有子语句与子函数体
    for stmt in &mut block.stmts {
        changed |= polish_stmt(stmt, target, captured, debug_hinted);
        changed |= fold_pure_method_calls_in_stmt(stmt, captured, debug_hinted);
    }

    // 2. 块内相邻语句折叠（`local f; f = function`、`local x; x = expr`、多返回接棒合流、
    //    跨短路参数被打散的 `SELF` 方法调用还原、单用纯临时前向内联、`a and b or c` 等）
    let mut i = 0;
    while i + 1 < block.stmts.len() {
        if try_fold_local_function_pair(&mut block.stmts, i) {
            changed = true;
            continue;
        }
        if try_fold_empty_local_init_pair(&mut block.stmts, i) {
            changed = true;
            continue;
        }
        if try_absorb_following_local_copies(&mut block.stmts, i, captured) {
            changed = true;
            continue;
        }
        if try_coalesce_multi_assign(&mut block.stmts, i, is_function_root, target, captured) {
            changed = true;
            continue;
        }
        if target.version != crate::decompile::DecompileDialect::Luau
            && let Some(win_start) =
                try_coalesce_reverse_parallel_assign(&mut block.stmts, i, target, captured)
        {
            changed = true;
            i = win_start;
            continue;
        }
        if try_fold_short_circuit_value_pair(&mut block.stmts, i, captured) {
            changed = true;
            continue;
        }
        if try_fold_bool_init_and_pair(&mut block.stmts, i, captured) {
            changed = true;
            continue;
        }
        if try_fold_const_truthy_or_pair(&mut block.stmts, i, captured) {
            changed = true;
            continue;
        }
        if try_fold_split_method_call(&mut block.stmts, i, captured, debug_hinted) {
            changed = true;
            i = i.saturating_sub(1);
            continue;
        }
        if try_inline_single_use_pure_temp(
            &mut block.stmts,
            i,
            target,
            is_function_root,
            captured,
            debug_hinted,
        ) {
            changed = true;
            i = i.saturating_sub(1);
            continue;
        }
        i += 1;
    }

    // 2b. 清理因折叠/合流后已无任何读取的匿名空 `local t1, t2` 及其死字面量写回
    if prune_unused_empty_local_decls(&mut block.stmts, captured) {
        changed = true;
    }

    // 2c. 合并 Lua 5.5 逆序多目标 `global` 声明帧：
    //     `local t1 = e1; local t2, t3 = f(); global g3 = t3; global g2 = t2; global g1 = t1`
    //     → `global g1, g2, g3 = e1, f()`（完整还原原右向左探针/赋值协议与槽位生命周期）
    if target.caps.global_decl
        && merge_reversed_global_decls(&mut block.stmts, captured, debug_hinted)
    {
        changed = true;
    }

    // 2d. 清理被宽全局声明配对或前序折叠消费后完全不再读取的匿名纯常量/环境快照 `local r = _ENV` / `local r = "const"`
    if prune_unused_pure_single_local_decls(&mut block.stmts, captured) {
        changed = true;
    }

    // 2e. Luau：传播并清理从无后续赋值的匿名纯布尔常量局部（`local r = false/true` → 替换后继读取为字面量），
    //     避免 Luau `-O2` 重编译时延迟常量传播导致额外收敛轮次（不触碰 LuaJIT `TNEW`/`TDUP` 表构造常量槽）。
    if target.version == crate::decompile::DecompileDialect::Luau
        && propagate_immutable_anon_bool_locals(&mut block.stmts, captured, debug_hinted)
    {
        changed = true;
    }

    // 3. 单条 `if` 语句折叠为 `x = cond and a or b` / `x = a or b` / `return ...`
    for stmt in &mut block.stmts {
        if try_fold_if_value_assign(stmt, target) || try_fold_if_return(stmt, target) {
            changed = true;
        }
    }

    // 3b. 折叠短路真值早退返回阶梯（如 Luau 宽 `(a01 and a02) or (a03 and a04) ...`）：
    //     `if c then [local] x = b; if x then return x end end; return rest`
    //     → `return (c and b) or rest`（线性单遍向左结合，语义 100% 等价且无 falsy 陷阱！）
    if try_fold_guarded_truthy_return_chain(&mut block.stmts, captured, debug_hinted) {
        changed = true;
    }

    // 3c. Luau 常量条件分支死臂清理：
    //     - `if true then A else B end` → `do A end`（仅当死臂无标签且无 retain-debug 局部）
    //     - `if false then A [else B] end` → `do B end` 或移除（保留单句 `if false then x = nil end` 常量捕获防传播护栏与 retain-debug 局部！）
    if target.version == crate::decompile::DecompileDialect::Luau {
        let mut cf_idx = 0usize;
        while cf_idx < block.stmts.len() {
            let action = match &block.stmts[cf_idx] {
                AstStmt::If(if_stmt)
                    if matches!(if_stmt.cond, AstExpr::Boolean(true))
                        && if_stmt.else_block.as_ref().is_none_or(|eb| {
                            !block_contains_any_label(eb)
                                && collect_debug_hinted_names_in_block(eb).is_empty()
                        }) =>
                {
                    Some(true)
                }
                AstStmt::If(if_stmt)
                    if matches!(if_stmt.cond, AstExpr::Boolean(false) | AstExpr::Nil)
                        && !block_contains_any_label(&if_stmt.then_block)
                        && collect_debug_hinted_names_in_block(&if_stmt.then_block).is_empty()
                        && !is_luau_fresh_const_capture_guard(if_stmt) =>
                {
                    Some(false)
                }
                _ => None,
            };
            match action {
                Some(true) => {
                    let AstStmt::If(taken) =
                        std::mem::replace(&mut block.stmts[cf_idx], AstStmt::Break)
                    else {
                        unreachable!()
                    };
                    block.stmts[cf_idx] = AstStmt::DoBlock(Box::new(taken.then_block));
                    changed = true;
                    cf_idx += 1;
                }
                Some(false) => {
                    let AstStmt::If(taken) = block.stmts.remove(cf_idx) else {
                        unreachable!()
                    };
                    if let Some(eb) = taken.else_block {
                        block.stmts.insert(cf_idx, AstStmt::DoBlock(Box::new(eb)));
                        cf_idx += 1;
                    }
                    changed = true;
                }
                None => cf_idx += 1,
            }
        }
    }

    // 3d. 块尾早退阶梯拍平：当非 `repeat` 块末尾的 `if cond then <必然终结> else <len >= 2> end`
    //     且 `else` 块无直接 `<close>` / `global` / `label` 时，拍平为 `if cond then <必然终结> end; <else...>`，
    //     消除事件分发等场景的 30+ 层右倾 `return / else / if` 阶梯（保留单句 `elseif` 不动）。
    if allow_tail_else_flatten && flatten_tail_terminating_if_else(&mut block.stmts) {
        changed = true;
    }

    // 4. 清理空 `DoBlock` 与无局部/标签/全局声明的纯冗余 `DoBlock`（如 LuaJIT 剥离后遗留的 `do r = i end`）
    let mut splice_idx = 0usize;
    while splice_idx < block.stmts.len() {
        let can_splice = match &block.stmts[splice_idx] {
            AstStmt::DoBlock(b) => {
                b.stmts.is_empty()
                    || !b.stmts.iter().any(|s| {
                        matches!(
                            s,
                            AstStmt::LocalDecl(_)
                                | AstStmt::LocalFunctionDecl(_)
                                | AstStmt::GlobalDecl(_)
                                | AstStmt::Label(_)
                        )
                    })
            }
            _ => false,
        };
        if can_splice {
            let AstStmt::DoBlock(b) = block.stmts.remove(splice_idx) else {
                unreachable!()
            };
            let n = b.stmts.len();
            block.stmts.splice(splice_idx..splice_idx, b.stmts);
            splice_idx += n;
            changed = true;
        } else {
            splice_idx += 1;
        }
    }

    // 4b. Lua 5.4/5.5 末尾标签 `<close>` 保护：
    //     在 Lua 5.4 中，若块尾存在被前序 `DoBlock` 内 `<close>` 作用域 `goto` 指向的末尾标签 `::L::`，
    //     且该 `DoBlock` 与 `::L::` 之间夹杂新的 `local` 声明，stock `luac5.4` 会按末尾 `nactvar` 发射
    //     更高槽号的 `CLOSE`，导致跳转跳过原 `<close>` 的关闭！将中间含 `local` 的段落包进 `do ... end` 即可 100% 规避。
    if target.caps.local_close && guard_trailing_label_after_close_goto(&mut block.stmts) {
        changed = true;
    }

    // 5. 函数体末尾多余的裸 `return` 移除
    if is_function_root
        && matches!(block.stmts.last(), Some(AstStmt::Return(r)) if r.values.is_empty())
    {
        block.stmts.pop();
        changed = true;
    }

    // 6. Lua 语法要求 `return`（以及 Lua 5.1/LuaJIT 的 `break`）必须位于所在语句块末尾；
    //    若其后存在标签或其它语句，用 `do ... end` 合法包裹以保语法通过。
    let len = block.stmts.len();
    for stmt in &mut block.stmts[..len.saturating_sub(1)] {
        if matches!(stmt, AstStmt::Return(_) | AstStmt::Break) {
            let taken = std::mem::replace(stmt, AstStmt::Break);
            *stmt = AstStmt::DoBlock(Box::new(AstBlock { stmts: vec![taken] }));
            changed = true;
        }
    }

    // 7. Lua 5.5 语义：一旦函数内出现显式 `global name`，同作用域及嵌套函数内未声明的隐式全局读写会变成编译错误；
    //    仅当函数体（或其嵌套函数）实际引用了隐式 `AstNameRef::Global(_)` 且开头尚无通配符 `global *` 时，
    //    才在首部补入 `global *`（避免污染仅含 `local _ENV = env; global ...` 的纯局部环境函数）。
    if is_function_root
        && target.caps.global_decl
        && block_contains_global_decl(block)
        && block_references_any_global_name(block)
        && !starts_with_global_wildcard(block)
    {
        block.stmts.insert(
            0,
            AstStmt::GlobalDecl(Box::new(super::common::AstGlobalDecl {
                bindings: vec![super::common::AstGlobalBinding {
                    target: super::common::AstGlobalBindingTarget::Wildcard,
                    attr: super::common::AstGlobalAttr::None,
                }],
                values: Vec::new(),
            })),
        );
        changed = true;
    }

    changed
}

fn starts_with_global_wildcard(block: &AstBlock) -> bool {
    matches!(
        block.stmts.first(),
        Some(AstStmt::GlobalDecl(d))
            if d.bindings.iter().any(|b| matches!(b.target, super::common::AstGlobalBindingTarget::Wildcard))
    )
}

/// 递归判断语句块的所有路径是否必然提前终结（`return`/`break`/`continue`/`goto`），绝不自然落出。
fn block_always_terminates(block: &AstBlock) -> bool {
    let Some(last) = block.stmts.last() else {
        return false;
    };
    match last {
        AstStmt::Return(_) | AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) => true,
        AstStmt::DoBlock(b) => block_always_terminates(b),
        AstStmt::If(i) => {
            block_always_terminates(&i.then_block)
                && i.else_block
                    .as_ref()
                    .is_some_and(block_always_terminates)
        }
        _ => false,
    }
}

/// 检查块顶层是否存在 `<close>` 声明、`global` 声明或标签（用于保护块尾 `else` 拍平不越界改写作用域）。
fn block_has_direct_close_global_or_label(block: &AstBlock) -> bool {
    block.stmts.iter().any(|s| match s {
        AstStmt::LocalDecl(d) => d.bindings.iter().any(|b| b.attr == AstLocalAttr::Close),
        AstStmt::GlobalDecl(_) | AstStmt::Label(_) => true,
        _ => false,
    })
}

/// 拍平块尾 `if cond then <必然终结> else <len >= 2> end` → `if cond then <必然终结> end; <else...>`，
/// 保留单句 `elseif` 不动，循环展开以单遍拍平多层右倾事件分发阶梯。
fn flatten_tail_terminating_if_else(stmts: &mut Vec<AstStmt>) -> bool {
    let mut changed = false;
    loop {
        let can_flatten = match stmts.last() {
            Some(AstStmt::If(if_stmt)) => {
                if_stmt.else_block.as_ref().is_some_and(|eb| {
                    eb.stmts.len() >= 2 && !block_has_direct_close_global_or_label(eb)
                }) && block_always_terminates(&if_stmt.then_block)
            }
            _ => false,
        };
        if !can_flatten {
            break;
        }
        let Some(AstStmt::If(if_stmt)) = stmts.last_mut() else {
            unreachable!()
        };
        let eb = if_stmt.else_block.take().unwrap();
        stmts.extend(eb.stmts);
        changed = true;
    }
    changed
}

fn is_pure_truthy_literal(expr: &AstExpr) -> bool {
    matches!(
        expr,
        AstExpr::Boolean(true)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_)
            | AstExpr::Int64(_)
            | AstExpr::UInt64(_)
            | AstExpr::Complex { .. }
            | AstExpr::Vector(_)
    )
}

/// 递归判断单值表达式是否绝对为真（含表/函数与复合 `or`/`and`/`if` 表达式），
/// 专用于消除不可达的 `truthy_lhs or dead_rhs` 死分支，不触发 `if -> and/or` 嵌套改写震荡。
fn expr_always_truthy_single_value(expr: &AstExpr) -> bool {
    if expr.is_guaranteed_truthy() {
        return true;
    }
    match expr {
        AstExpr::LogicalOr(l) => {
            expr_always_truthy_single_value(&l.lhs) || expr_always_truthy_single_value(&l.rhs)
        }
        AstExpr::LogicalAnd(l) => {
            expr_always_truthy_single_value(&l.lhs) && expr_always_truthy_single_value(&l.rhs)
        }
        AstExpr::IfExpr(ie) => {
            expr_always_truthy_single_value(&ie.then_expr)
                && expr_always_truthy_single_value(&ie.else_expr)
        }
        _ => false,
    }
}

/// 空单臂 `if cond then end` 中，最末端布尔测试的真假取反不触发任何元方法、不改变短路前序求值，
/// 也不改变控制流；递归剥除顶层或最右 `and`/`or` 尾项的 `not`，消除 2 周期翻转震荡。
fn strip_empty_if_terminal_not(expr: &mut AstExpr) -> bool {
    match expr {
        AstExpr::Unary(u) if u.op == AstUnaryOpKind::Not => {
            let old = std::mem::replace(expr, AstExpr::Boolean(true));
            if let AstExpr::Unary(u) = old {
                *expr = u.expr;
                return true;
            }
            false
        }
        AstExpr::LogicalAnd(l) | AstExpr::LogicalOr(l) => {
            strip_empty_if_terminal_not(&mut l.rhs)
        }
        _ => false,
    }
}

/// 检查当前循环体内（不进入嵌套循环/闭包）是否存在直接 `continue`。
fn block_contains_direct_continue(block: &AstBlock) -> bool {
    block.stmts.iter().any(|stmt| match stmt {
        AstStmt::Continue => true,
        AstStmt::If(i) => {
            block_contains_direct_continue(&i.then_block)
                || i.else_block
                    .as_ref()
                    .is_some_and(block_contains_direct_continue)
        }
        AstStmt::DoBlock(b) => block_contains_direct_continue(b),
        _ => false,
    })
}

fn block_contains_global_decl(block: &AstBlock) -> bool {
    block.stmts.iter().any(|stmt| match stmt {
        AstStmt::GlobalDecl(_) => true,
        AstStmt::If(i) => {
            block_contains_global_decl(&i.then_block)
                || i.else_block.as_ref().is_some_and(block_contains_global_decl)
        }
        AstStmt::While(w) => block_contains_global_decl(&w.body),
        AstStmt::Repeat(r) => block_contains_global_decl(&r.body),
        AstStmt::NumericFor(nf) => block_contains_global_decl(&nf.body),
        AstStmt::GenericFor(gf) => block_contains_global_decl(&gf.body),
        AstStmt::DoBlock(b) => block_contains_global_decl(b),
        _ => false,
    })
}

/// 检查当前块及其所有子语句与嵌套函数体是否引用了任何隐式全局名 `AstNameRef::Global(_)`。
fn block_references_any_global_name(block: &AstBlock) -> bool {
    fn expr_has_global(expr: &AstExpr) -> bool {
        for node in expr_nodes(expr) {
            match node {
                ExprNode::Expr(AstExpr::Var(AstNameRef::Global(_))) => return true,
                ExprNode::Function(func) if block_references_any_global_name(&func.body) => {
                    return true;
                }
                _ => {}
            }
        }
        false
    }
    fn lvalue_has_global(lv: &AstLValue) -> bool {
        match lv {
            AstLValue::Name(AstNameRef::Global(_)) => true,
            AstLValue::Name(_) => false,
            AstLValue::FieldAccess(f) => expr_has_global(&f.base),
            AstLValue::IndexAccess(i) => expr_has_global(&i.base) || expr_has_global(&i.index),
        }
    }
    block.stmts.iter().any(|stmt| match stmt {
        AstStmt::LocalDecl(d) => d.values.iter().any(expr_has_global),
        AstStmt::GlobalDecl(d) => d.values.iter().any(expr_has_global),
        AstStmt::Assign(a) => {
            a.targets.iter().any(lvalue_has_global) || a.values.iter().any(expr_has_global)
        }
        AstStmt::CallStmt(c) => match &c.call {
            super::common::AstCallKind::Call(call) => {
                expr_has_global(&call.callee) || call.args.iter().any(expr_has_global)
            }
            super::common::AstCallKind::MethodCall(m) => {
                expr_has_global(&m.receiver) || m.args.iter().any(expr_has_global)
            }
        },
        AstStmt::FunctionDecl(fd) => {
            let root = match &fd.target {
                super::common::AstFunctionName::Plain(p)
                | super::common::AstFunctionName::Method(p, _) => &p.root,
            };
            matches!(root, AstNameRef::Global(_)) || block_references_any_global_name(&fd.func.body)
        }
        AstStmt::LocalFunctionDecl(lfd) => block_references_any_global_name(&lfd.func.body),
        AstStmt::Return(r) => r.values.iter().any(expr_has_global),
        AstStmt::If(i) => {
            expr_has_global(&i.cond)
                || block_references_any_global_name(&i.then_block)
                || i.else_block
                    .as_ref()
                    .is_some_and(block_references_any_global_name)
        }
        AstStmt::While(w) => {
            expr_has_global(&w.cond) || block_references_any_global_name(&w.body)
        }
        AstStmt::Repeat(r) => {
            block_references_any_global_name(&r.body) || expr_has_global(&r.cond)
        }
        AstStmt::NumericFor(nf) => {
            expr_has_global(&nf.start)
                || expr_has_global(&nf.limit)
                || expr_has_global(&nf.step)
                || block_references_any_global_name(&nf.body)
        }
        AstStmt::GenericFor(gf) => {
            gf.iterator.iter().any(expr_has_global) || block_references_any_global_name(&gf.body)
        }
        AstStmt::DoBlock(b) => block_references_any_global_name(b),
        _ => false,
    })
}

/// 合并 Lua 5.5 逆序多目标 `global` 声明帧：
/// `local t1 = e1; local t2, t3 = f(); global g3 = t3; global g2 = t2; global g1 = t1`
/// 或 `local t1 = e1; global g2 = e2; global g1 = t1`
/// → `global g1, g2[, g3] = e1, e2/f()`。
fn merge_reversed_global_decls(
    stmts: &mut Vec<AstStmt>,
    captured: &BTreeSet<AstNameRef>,
    debug_hinted: &BTreeSet<AstNameRef>,
) -> bool {
    let mut changed = false;
    let mut g_start = 0usize;
    while g_start < stmts.len() {
        let is_single_plain_global = |s: &AstStmt| -> bool {
            matches!(
                s,
                AstStmt::GlobalDecl(d)
                    if d.bindings.len() == 1
                        && d.bindings[0].attr == super::common::AstGlobalAttr::None
                        && matches!(
                            d.bindings[0].target,
                            super::common::AstGlobalBindingTarget::Name(_)
                        )
                        && d.values.len() == 1
            )
        };
        if !is_single_plain_global(&stmts[g_start]) {
            g_start += 1;
            continue;
        }
        let mut g_end = g_start + 1;
        while g_end < stmts.len() && is_single_plain_global(&stmts[g_end]) {
            g_end += 1;
        }
        let g_count = g_end - g_start;
        if g_count < 2 || g_start == 0 {
            g_start = g_end;
            continue;
        }

        // 从 `g_start..g_end` 中尽量匹配出最长的逆序临时序列：
        // 支持 Case A（全部 `g_count` 个 global 均取自紧邻前序 `LocalDecl` 临时变量）
        // 以及 Case B（首个 `stmts[g_start]` 直接求值尾表达式，其余 `g_count - 1` 个取自前序 `LocalDecl`）。
        let mut matched: Option<(usize, usize, bool)> = None;
        for &direct_tail in &[false, true] {
            let var_start = g_start + usize::from(direct_tail);
            if var_start >= g_end {
                continue;
            }
            // 收集 `stmts[var_start..g_end]` 的 RHS 变量名（逆序即前序 `LocalDecl` 的正序绑定列表）
            let mut rev_temps: Vec<AstNameRef> = Vec::with_capacity(g_end - var_start);
            let mut all_vars = true;
            for stmt in &stmts[var_start..g_end] {
                if let AstStmt::GlobalDecl(d) = stmt
                    && let [AstExpr::Var(nr)] = d.values.as_slice()
                    && !captured.contains(nr)
                    && !debug_hinted.contains(nr)
                    && matches!(nr, AstNameRef::Local(_) | AstNameRef::SyntheticLocal(_))
                {
                    rev_temps.push(nr.clone());
                } else {
                    all_vars = false;
                    break;
                }
            }
            if !all_vars || rev_temps.is_empty() {
                continue;
            }
            let expected_temps: Vec<AstNameRef> = rev_temps.into_iter().rev().collect();
            // 确保每个临时名互不重复，且在 `stmts[g_end..]` 之后不再被引用
            let temp_set: BTreeSet<AstNameRef> = expected_temps.iter().cloned().collect();
            if temp_set.len() != expected_temps.len() {
                continue;
            }
            if stmts[g_end..]
                .iter()
                .any(|s| temp_set.iter().any(|t| stmt_mentions_name_ref(s, t)))
            {
                continue;
            }
            // 若为 Case B，尾表达式自身不得引用将被消除的临时变量
            if direct_tail
                && let AstStmt::GlobalDecl(d) = &stmts[g_start]
                && temp_set
                    .iter()
                    .any(|t| expr_mentions_name_ref(&d.values[0], t))
            {
                continue;
            }

            // 向前匹配 `stmts[l_start..g_start]` 中的连续 `LocalDecl`，使其绑定拼接恰好等于 `expected_temps`
            let mut rem = expected_temps.len();
            let mut l_start = g_start;
            let mut ok = true;
            while rem > 0 {
                if l_start == 0 {
                    ok = false;
                    break;
                }
                let prev_idx = l_start - 1;
                let AstStmt::LocalDecl(ld) = &stmts[prev_idx] else {
                    ok = false;
                    break;
                };
                if ld.bindings.is_empty()
                    || ld.bindings.len() > rem
                    || ld
                        .bindings
                        .iter()
                        .any(|b| b.attr != AstLocalAttr::None || b.is_debug_hinted)
                {
                    ok = false;
                    break;
                }
                let slice_start = rem - ld.bindings.len();
                let bindings_match = ld
                    .bindings
                    .iter()
                    .enumerate()
                    .all(|(k, b)| b.id.to_name_ref() == expected_temps[slice_start + k]);
                if !bindings_match {
                    ok = false;
                    break;
                }
                // 只有整段声明列表的最后一条表达式允许展开多返回值（Case A 的最后一条 `LocalDecl`）
                let is_last_expr_stmt = !direct_tail && prev_idx + 1 == g_start;
                if ld.values.len() > ld.bindings.len() {
                    ok = false;
                    break;
                }
                if !is_last_expr_stmt && ld.values.len() != ld.bindings.len() && !ld.values.is_empty()
                {
                    ok = false;
                    break;
                }
                if is_last_expr_stmt
                    && ld.values.len() < ld.bindings.len()
                    && !ld.values.is_empty()
                    && !matches!(
                        ld.values.last(),
                        Some(AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg)
                    )
                {
                    ok = false;
                    break;
                }
                // 前序 LocalDecl 的 RHS 不得互相引用待消除临时变量
                if ld
                    .values
                    .iter()
                    .any(|v| temp_set.iter().any(|t| expr_mentions_name_ref(v, t)))
                {
                    ok = false;
                    break;
                }
                l_start = prev_idx;
                rem = slice_start;
            }
            if ok && rem == 0 {
                matched = Some((l_start, g_end, direct_tail));
                break;
            }
        }

        if let Some((l_start, end_idx, direct_tail)) = matched {
            let mut merged_values: Vec<AstExpr> = Vec::new();
            let mut merged_bindings: Vec<super::common::AstGlobalBinding> = Vec::new();
            let mut drained: Vec<AstStmt> = stmts.drain(l_start..end_idx).collect();
            let local_cnt = g_start - l_start;
            let globals: Vec<AstStmt> = drained.split_off(local_cnt);

            for stmt in drained {
                if let AstStmt::LocalDecl(ld) = stmt {
                    if ld.values.is_empty() {
                        for _ in 0..ld.bindings.len() {
                            merged_values.push(AstExpr::Nil);
                        }
                    } else {
                        merged_values.extend(ld.values);
                    }
                }
            }
            let mut global_iter = globals.into_iter();
            if direct_tail
                && let Some(AstStmt::GlobalDecl(mut first_g)) = global_iter.next()
            {
                if let Some(v) = first_g.values.pop() {
                    merged_values.push(v);
                }
                if let Some(b) = first_g.bindings.pop() {
                    merged_bindings.push(b);
                }
            }
            for stmt in global_iter {
                if let AstStmt::GlobalDecl(mut d) = stmt
                    && let Some(b) = d.bindings.pop()
                {
                    merged_bindings.push(b);
                }
            }
            merged_bindings.reverse();
            stmts.insert(
                l_start,
                AstStmt::GlobalDecl(Box::new(super::common::AstGlobalDecl {
                    bindings: merged_bindings,
                    values: merged_values,
                })),
            );
            changed = true;
            g_start = l_start + 1;
        } else {
            g_start = g_end;
        }
    }
    changed
}

fn guard_trailing_label_after_close_goto(stmts: &mut Vec<AstStmt>) -> bool {
    let Some(AstStmt::Label(trail_lbl)) = stmts.last() else {
        return false;
    };
    let target = trail_lbl.id;
    let label_pos = stmts.len() - 1;
    if label_pos < 2 {
        return false;
    }
    fn block_has_close_and_goto(block: &AstBlock, target: super::common::AstLabelId) -> (bool, bool) {
        let mut has_close = false;
        let mut has_goto = false;
        for s in &block.stmts {
            match s {
                AstStmt::LocalDecl(d) => {
                    if d.bindings.iter().any(|b| b.attr == AstLocalAttr::Close) {
                        has_close = true;
                    }
                }
                AstStmt::Goto(g) if g.target == target => has_goto = true,
                AstStmt::DoBlock(b) => {
                    let (c, g) = block_has_close_and_goto(b, target);
                    has_close |= c;
                    has_goto |= g;
                }
                AstStmt::If(i) => {
                    let (c1, g1) = block_has_close_and_goto(&i.then_block, target);
                    has_close |= c1;
                    has_goto |= g1;
                    if let Some(eb) = &i.else_block {
                        let (c2, g2) = block_has_close_and_goto(eb, target);
                        has_close |= c2;
                        has_goto |= g2;
                    }
                }
                AstStmt::While(w) => {
                    let (c, g) = block_has_close_and_goto(&w.body, target);
                    has_close |= c;
                    has_goto |= g;
                }
                AstStmt::Repeat(r) => {
                    let (c, g) = block_has_close_and_goto(&r.body, target);
                    has_close |= c;
                    has_goto |= g;
                }
                AstStmt::NumericFor(nf) => {
                    let (c, g) = block_has_close_and_goto(&nf.body, target);
                    has_close |= c;
                    has_goto |= g;
                }
                AstStmt::GenericFor(gf) => {
                    let (c, g) = block_has_close_and_goto(&gf.body, target);
                    has_close |= c;
                    has_goto |= g;
                }
                _ => {}
            }
        }
        (has_close, has_goto)
    }
    let Some(close_do_idx) = stmts[..label_pos].iter().rposition(|s| {
        if let AstStmt::DoBlock(b) = s {
            let (has_close, has_goto) = block_has_close_and_goto(b, target);
            has_close && has_goto
        } else {
            false
        }
    }) else {
        return false;
    };
    let mid_start = close_do_idx + 1;
    if mid_start >= label_pos {
        return false;
    }
    let mid_has_local_decl = stmts[mid_start..label_pos]
        .iter()
        .any(|s| matches!(s, AstStmt::LocalDecl(_) | AstStmt::LocalFunctionDecl(_)));
    if !mid_has_local_decl {
        return false;
    }
    let wrapped: Vec<AstStmt> = stmts.drain(mid_start..label_pos).collect();
    stmts.insert(
        mid_start,
        AstStmt::DoBlock(Box::new(AstBlock { stmts: wrapped })),
    );
    true
}

fn propagate_immutable_anon_bool_locals(
    stmts: &mut Vec<AstStmt>,
    captured: &BTreeSet<AstNameRef>,
    debug_hinted: &BTreeSet<AstNameRef>,
) -> bool {
    let mut changed = false;
    let mut idx = 0usize;
    while idx < stmts.len() {
        let candidate = match &stmts[idx] {
            AstStmt::LocalDecl(d)
                if d.bindings.len() == 1
                    && d.values.len() == 1
                    && d.bindings[0].attr == AstLocalAttr::None
                    && !d.bindings[0].is_debug_hinted =>
            {
                if let AstExpr::Boolean(bval) = d.values[0] {
                    let name = d.bindings[0].id.to_name_ref();
                    if !captured.contains(&name)
                        && !debug_hinted.contains(&name)
                        && !stmts[idx + 1..]
                            .iter()
                            .any(|s| stmt_writes_name_ref(s, &name))
                    {
                        Some((name, bval))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some((name, bval)) = candidate {
            for s in &mut stmts[idx + 1..] {
                replace_all_var_reads_in_stmt(s, &name, AstExpr::Boolean(bval));
            }
            stmts.remove(idx);
            changed = true;
        } else {
            idx += 1;
        }
    }
    changed
}

fn stmt_writes_name_ref(stmt: &AstStmt, target: &AstNameRef) -> bool {
    match stmt {
        AstStmt::Assign(a) => a
            .targets
            .iter()
            .any(|t| matches!(t, AstLValue::Name(n) if n == target)),
        AstStmt::If(i) => {
            i.then_block
                .stmts
                .iter()
                .any(|s| stmt_writes_name_ref(s, target))
                || i.else_block
                    .as_ref()
                    .is_some_and(|eb| eb.stmts.iter().any(|s| stmt_writes_name_ref(s, target)))
        }
        AstStmt::While(w) => w.body.stmts.iter().any(|s| stmt_writes_name_ref(s, target)),
        AstStmt::Repeat(r) => r.body.stmts.iter().any(|s| stmt_writes_name_ref(s, target)),
        AstStmt::NumericFor(nf) => nf.body.stmts.iter().any(|s| stmt_writes_name_ref(s, target)),
        AstStmt::GenericFor(gf) => gf.body.stmts.iter().any(|s| stmt_writes_name_ref(s, target)),
        AstStmt::DoBlock(b) => b.stmts.iter().any(|s| stmt_writes_name_ref(s, target)),
        _ => false,
    }
}

fn replace_all_var_reads_in_stmt(stmt: &mut AstStmt, target: &AstNameRef, val: AstExpr) {
    use super::traverse::{traverse_call_children, traverse_lvalue_children, traverse_stmt_children};
    traverse_stmt_children!(
        stmt,
        iter = iter_mut,
        opt = as_mut,
        borrow = [&mut],
        expr(e) => { replace_all_var_reads_in_expr(e, target, &val); },
        lvalue(lv) => {
            traverse_lvalue_children!(lv, borrow = [&mut], expr(e) => {
                replace_all_var_reads_in_expr(e, target, &val);
            });
        },
        block(b) => {
            for s in &mut b.stmts {
                replace_all_var_reads_in_stmt(s, target, val.clone());
            }
        },
        function(_func) => {},
        condition(c) => { replace_all_var_reads_in_expr(c, target, &val); },
        call(call) => {
            traverse_call_children!(call, iter = iter_mut, borrow = [&mut], expr(e) => {
                replace_all_var_reads_in_expr(e, target, &val);
            });
        }
    );
}

fn replace_all_var_reads_in_expr(expr: &mut AstExpr, target: &AstNameRef, val: &AstExpr) {
    if matches!(expr, AstExpr::Var(n) if n == target) {
        *expr = val.clone();
        return;
    }
    use super::traverse::traverse_expr_children;
    traverse_expr_children!(
        expr,
        iter = iter_mut,
        borrow = [&mut],
        expr(child) => { replace_all_var_reads_in_expr(child, target, val); },
        function(_func) => {}
    );
}

fn prune_unused_pure_single_local_decls(
    stmts: &mut Vec<AstStmt>,
    captured: &BTreeSet<AstNameRef>,
) -> bool {
    let mut changed = false;
    let mut idx = 0usize;
    while idx < stmts.len() {
        let dead_pure = match &stmts[idx] {
            AstStmt::LocalDecl(d)
                if d.bindings.len() == 1
                    && d.values.len() == 1
                    && d.bindings[0].attr == AstLocalAttr::None
                    && !d.bindings[0].is_debug_hinted =>
            {
                let name = d.bindings[0].id.to_name_ref();
                let pure_rhs = matches!(
                    &d.values[0],
                    AstExpr::Nil
                        | AstExpr::Boolean(_)
                        | AstExpr::Integer(_)
                        | AstExpr::Number(_)
                        | AstExpr::String(_)
                        | AstExpr::Var(AstNameRef::Environment)
                );
                pure_rhs
                    && !captured.contains(&name)
                    && !stmts[idx + 1..]
                        .iter()
                        .any(|s| stmt_mentions_name_ref(s, &name))
            }
            _ => false,
        };
        if dead_pure {
            stmts.remove(idx);
            changed = true;
        } else {
            idx += 1;
        }
    }
    changed
}

fn polish_stmt(
    stmt: &mut AstStmt,
    target: AstTargetDialect,
    captured: &BTreeSet<AstNameRef>,
    debug_hinted: &BTreeSet<AstNameRef>,
) -> bool {
    let mut changed = false;
    match stmt {
        AstStmt::LocalDecl(decl) => {
            for v in &mut decl.values {
                changed |= polish_expr(v, target, false);
            }
            // `local f = function(...) end` → `local function f(...) end`（非自捕获且无属性时）
            if decl.bindings.len() == 1
                && decl.bindings[0].attr == AstLocalAttr::None
                && decl.values.len() == 1
                && matches!(&decl.values[0], AstExpr::FunctionExpr(f) if !f.captured_bindings.contains(&decl.bindings[0].id))
            {
                let binding = decl.bindings[0].id;
                let AstExpr::FunctionExpr(func) = decl.values.pop().unwrap() else {
                    unreachable!()
                };
                *stmt = AstStmt::LocalFunctionDecl(Box::new(AstLocalFunctionDecl {
                    name: binding,
                    func: *func,
                }));
                return true;
            }
        }
        AstStmt::GlobalDecl(decl) => {
            for v in &mut decl.values {
                changed |= polish_expr(v, target, false);
            }
        }
        AstStmt::Assign(assign) => {
            for v in &mut assign.values {
                changed |= polish_expr(v, target, false);
            }
            // 全局/简单表字段函数赋值 `foo = function(...)` → `function foo(...)`
            if assign.compound_op.is_none()
                && assign.targets.len() == 1
                && assign.values.len() == 1
                && matches!(&assign.values[0], AstExpr::FunctionExpr(_))
                && let Some(func_name) = lvalue_to_function_name(&assign.targets[0])
            {
                let AstExpr::FunctionExpr(func) = assign.values.pop().unwrap() else {
                    unreachable!()
                };
                *stmt = AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                    target: func_name,
                    global_declaration: false,
                    func: *func,
                }));
                return true;
            }
        }
        AstStmt::CallStmt(call) => match &mut call.call {
            super::common::AstCallKind::Call(c) => {
                changed |= polish_expr(&mut c.callee, target, false);
                for a in &mut c.args {
                    changed |= polish_expr(a, target, false);
                }
            }
            super::common::AstCallKind::MethodCall(m) => {
                changed |= polish_expr(&mut m.receiver, target, false);
                for a in &mut m.args {
                    changed |= polish_expr(a, target, false);
                }
            }
        },
        AstStmt::Return(ret) => {
            for v in &mut ret.values {
                changed |= polish_expr(v, target, false);
            }
        }
        AstStmt::If(if_stmt) => {
            changed |= polish_expr(&mut if_stmt.cond, target, true);
            changed |= polish_block(
                &mut if_stmt.then_block,
                target,
                false,
                true,
                captured,
                debug_hinted,
            );
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= polish_block(else_block, target, false, true, captured, debug_hinted);
                if else_block.stmts.is_empty() {
                    if_stmt.else_block = None;
                    changed = true;
                }
            }
            // 空 `then` 臂 + 非空 `else` 臂 → 取反条件（仅在非 NaN 敏感场景或用 `not (...)` 包裹，100% 保持 NaN 安全！）
            if if_stmt.then_block.stmts.is_empty()
                && let Some(else_block) = if_stmt.else_block.take()
            {
                let old_cond = std::mem::replace(&mut if_stmt.cond, AstExpr::Boolean(true));
                if_stmt.cond = negate_condition_safe(old_cond);
                if_stmt.then_block = else_block;
                changed = true;
            }
            // 折叠同体嵌套条件阶梯（去重共享分支，严格保持短路求值序与 NaN 安全）：
            // - `if c1 then if c2 then B end else B end` → `if (not c1) or c2 then B end`
            // - `if c1 then B else if c2 then B end end` → `if c1 or c2 then B end`
            // - `if c1 then if c2 then A else B end else B end` → `if c1 and c2 then A else B end`
            if try_flatten_shared_branch_nested_if(if_stmt) {
                changed = true;
            }
            // 规范化空单臂 `if cond then end`（两臂皆空仅保留条件短路与求值副作用）：
            // 递归剥除顶层或最右 `and`/`or` 尾项上的 `not`，消除 `if A and b then end` <-> `if A and not b then end` 2 周期震荡。
            if if_stmt.then_block.stmts.is_empty()
                && if_stmt.else_block.is_none()
                && strip_empty_if_terminal_not(&mut if_stmt.cond)
            {
                changed = true;
            }
            // 规范化双臂 `if not cond then A else B end` → `if cond then B else A end`
            // 统一 `~=`/`not` 与 `==` 双臂的方向，彻底消除重编译时的 2 周期翻转震荡（100% NaN 安全）。
            if let Some(else_block) = &mut if_stmt.else_block
                && !else_block.stmts.is_empty()
                && matches!(&if_stmt.cond, AstExpr::Unary(u) if u.op == AstUnaryOpKind::Not)
            {
                let old_cond = std::mem::replace(&mut if_stmt.cond, AstExpr::Boolean(true));
                if let AstExpr::Unary(u) = old_cond {
                    if_stmt.cond = u.expr;
                    std::mem::swap(&mut if_stmt.then_block, else_block);
                    changed = true;
                }
            }
        }
        AstStmt::While(w) => {
            changed |= polish_expr(&mut w.cond, target, true);
            changed |= polish_block(&mut w.body, target, false, true, captured, debug_hinted);
            // `while true do if guard then break end; <rest> end` → `while not guard do <rest> end`
            if matches!(w.cond, AstExpr::Boolean(true))
                && let Some(AstStmt::If(head_if)) = w.body.stmts.first()
                && head_if.else_block.is_none()
                && head_if.then_block.stmts.len() == 1
                && matches!(head_if.then_block.stmts[0], AstStmt::Break)
            {
                let AstStmt::If(head_if) = w.body.stmts.remove(0) else {
                    unreachable!()
                };
                w.cond = negate_condition_safe(head_if.cond);
                changed = true;
            } else if matches!(w.cond, AstExpr::Boolean(true))
                && w.body.stmts.len() >= 2
                && let Some(AstStmt::If(tail_if)) = w.body.stmts.last()
                && tail_if.else_block.is_none()
                && tail_if.then_block.stmts.len() == 1
                && matches!(tail_if.then_block.stmts[0], AstStmt::Break)
                && !block_contains_direct_continue(&w.body)
            {
                // `while true do <body...>; if cond then break end end` → `repeat <body...> until cond`
                let AstStmt::If(tail_if) = w.body.stmts.pop().unwrap() else {
                    unreachable!()
                };
                let body = std::mem::take(&mut w.body);
                *stmt = AstStmt::Repeat(Box::new(super::common::AstRepeat {
                    body,
                    cond: tail_if.cond,
                }));
                return true;
            } else if matches!(w.cond, AstExpr::Boolean(true))
                && w.body.stmts.len() >= 2
                && matches!(w.body.stmts.last(), Some(AstStmt::Break))
                && !block_contains_direct_continue(&w.body)
            {
                // `while true do <body...>; break end` → `repeat <body...> until true`
                w.body.stmts.pop();
                let body = std::mem::take(&mut w.body);
                *stmt = AstStmt::Repeat(Box::new(super::common::AstRepeat {
                    body,
                    cond: AstExpr::Boolean(true),
                }));
                return true;
            }
        }
        AstStmt::Repeat(r) => {
            // Lua 规则：`repeat ... until cond` 的 cond 可读取 body 内声明的 local，
            // 把 cond 引用的名字并入 `captured`（保守禁止将其视为块尾死变量或删掉其声明）。
            let mut repeat_protected = captured.clone();
            collect_expr_var_names(&r.cond, &mut repeat_protected);
            changed |= polish_block(
                &mut r.body,
                target,
                false,
                false,
                &repeat_protected,
                debug_hinted,
            );
            changed |= polish_expr(&mut r.cond, target, true);
            // 将循环体尾部的单用匿名条件临时 `local t = expr; until t` 直接并入 `until expr`，
            // 消除不必要的 `repeat-condition-local`（例如 Luau `continue_16`）。
            if try_fold_repeat_tail_cond_local(r, captured, debug_hinted) {
                changed = true;
            }
        }
        AstStmt::NumericFor(nf) => {
            changed |= polish_expr(&mut nf.start, target, false);
            changed |= polish_expr(&mut nf.limit, target, false);
            changed |= polish_expr(&mut nf.step, target, false);
            changed |= polish_block(&mut nf.body, target, false, true, captured, debug_hinted);
        }
        AstStmt::GenericFor(gf) => {
            for e in &mut gf.iterator {
                changed |= polish_expr(e, target, false);
            }
            changed |= polish_block(&mut gf.body, target, false, true, captured, debug_hinted);
        }
        AstStmt::DoBlock(b) => {
            changed |= polish_block(b, target, false, true, captured, debug_hinted);
        }
        AstStmt::FunctionDecl(decl) => {
            let child_cap = collect_captured_names_in_block(&decl.func.body);
            let child_dbg = collect_debug_hinted_names_in_block(&decl.func.body);
            changed |= polish_block(
                &mut decl.func.body,
                target,
                true,
                true,
                &child_cap,
                &child_dbg,
            );
        }
        AstStmt::LocalFunctionDecl(decl) => {
            let child_cap = collect_captured_names_in_block(&decl.func.body);
            let child_dbg = collect_debug_hinted_names_in_block(&decl.func.body);
            changed |= polish_block(
                &mut decl.func.body,
                target,
                true,
                true,
                &child_cap,
                &child_dbg,
            );
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) | AstStmt::Error(_) => {}
    }
    changed
}

fn polish_expr(expr: &mut AstExpr, target: AstTargetDialect, in_bool_context: bool) -> bool {
    let mut changed = false;
    match expr {
        AstExpr::Unary(u) => {
            let child_bool = u.op == AstUnaryOpKind::Not;
            changed |= polish_expr(&mut u.expr, target, child_bool);
            // 仅在布尔条件语境中消除双重否定 `not (not x)` → `x`（值语境保留布尔强制转换！）
            if in_bool_context
                && u.op == AstUnaryOpKind::Not
                && let AstExpr::Unary(inner) = &mut u.expr
                && inner.op == AstUnaryOpKind::Not
            {
                let unwrapped = std::mem::replace(&mut inner.expr, AstExpr::Nil);
                *expr = unwrapped;
                return true;
            }
        }
        AstExpr::Binary(b) => {
            changed |= polish_expr(&mut b.lhs, target, false);
            changed |= polish_expr(&mut b.rhs, target, false);
            // Luau `-O2` 会在重编译时把纯字符串/布尔常量相等直接折叠为布尔常量；提前在 polish 折叠消除两轮差异。
            if target.version == crate::decompile::DecompileDialect::Luau
                && b.op == super::common::AstBinaryOpKind::Eq
            {
                match (&b.lhs, &b.rhs) {
                    (AstExpr::String(ls), AstExpr::String(rs)) => {
                        *expr = AstExpr::Boolean(ls == rs);
                        return true;
                    }
                    (AstExpr::Boolean(lb), AstExpr::Boolean(rb)) => {
                        *expr = AstExpr::Boolean(lb == rb);
                        return true;
                    }
                    _ => {}
                }
            }
            // 纯原始字面量 `==`/`~=`/`>`/`>=` 均无元方法与副作用：规范化为确定性方向，
            // 消除 PUC Lua `EQK`/`EQI` 与 LuaJIT `ISGT`/`ISGE` 重编译时的两轮翻转震荡。
            if let (Some(lk), Some(rk)) = (
                pure_primitive_literal_order_key(&b.lhs),
                pure_primitive_literal_order_key(&b.rhs),
            ) {
                match b.op {
                    super::common::AstBinaryOpKind::Eq if lk > rk => {
                        std::mem::swap(&mut b.lhs, &mut b.rhs);
                        changed = true;
                    }
                    super::common::AstBinaryOpKind::Gt => {
                        b.op = super::common::AstBinaryOpKind::Lt;
                        std::mem::swap(&mut b.lhs, &mut b.rhs);
                        changed = true;
                    }
                    super::common::AstBinaryOpKind::Ge => {
                        b.op = super::common::AstBinaryOpKind::Le;
                        std::mem::swap(&mut b.lhs, &mut b.rhs);
                        changed = true;
                    }
                    _ => {}
                }
            }
        }
        AstExpr::LogicalAnd(l) => {
            changed |= polish_expr(&mut l.lhs, target, in_bool_context);
            changed |= polish_expr(&mut l.rhs, target, in_bool_context);
            if matches!(l.lhs, AstExpr::Boolean(false) | AstExpr::Nil) {
                let lhs = std::mem::replace(&mut l.lhs, AstExpr::Nil);
                *expr = lhs;
                return true;
            }
            if is_pure_truthy_literal(&l.lhs)
                && !matches!(
                    l.rhs,
                    AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg
                )
            {
                let rhs = std::mem::replace(&mut l.rhs, AstExpr::Nil);
                *expr = rhs;
                return true;
            }
            if matches!(l.rhs, AstExpr::Boolean(true)) && expr_is_guaranteed_boolean(&l.lhs) {
                let lhs = std::mem::replace(&mut l.lhs, AstExpr::Nil);
                *expr = lhs;
                return true;
            }
        }
        AstExpr::LogicalOr(l) => {
            changed |= polish_expr(&mut l.lhs, target, in_bool_context);
            changed |= polish_expr(&mut l.rhs, target, in_bool_context);
            if expr_always_truthy_single_value(&l.lhs) {
                let lhs = std::mem::replace(&mut l.lhs, AstExpr::Nil);
                *expr = lhs;
                return true;
            }
            if matches!(l.lhs, AstExpr::Boolean(false) | AstExpr::Nil)
                && !matches!(
                    l.rhs,
                    AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg
                )
            {
                let rhs = std::mem::replace(&mut l.rhs, AstExpr::Nil);
                *expr = rhs;
                return true;
            }
        }
        AstExpr::IfExpr(ie) => {
            changed |= polish_expr(&mut ie.cond, target, true);
            changed |= polish_expr(&mut ie.then_expr, target, false);
            changed |= polish_expr(&mut ie.else_expr, target, false);
            if matches!(ie.cond, AstExpr::Boolean(true)) {
                let taken = std::mem::replace(&mut ie.then_expr, AstExpr::Nil);
                *expr = taken;
                return true;
            }
            if matches!(ie.cond, AstExpr::Boolean(false) | AstExpr::Nil) {
                let taken = std::mem::replace(&mut ie.else_expr, AstExpr::Nil);
                *expr = taken;
                return true;
            }
            // 当 `then_expr` 恒真且 `else_expr` 为单值表达式时，将 `(if c then truthy else b)`
            // 规范化为标准 Lua `c and truthy or b`，彻底消除 Luau `-O0` 在两轮间交替震荡的问题！
            if ie.then_expr.is_guaranteed_truthy()
                && !matches!(
                    ie.else_expr,
                    AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg
                )
            {
                let cond = std::mem::replace(&mut ie.cond, AstExpr::Nil);
                let then_expr = std::mem::replace(&mut ie.then_expr, AstExpr::Nil);
                let else_expr = std::mem::replace(&mut ie.else_expr, AstExpr::Nil);
                *expr = AstExpr::LogicalOr(Box::new(AstLogicalExpr {
                    lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                        lhs: cond,
                        rhs: then_expr,
                    })),
                    rhs: else_expr,
                }));
                return true;
            }
        }
        AstExpr::FieldAccess(fa) => {
            changed |= polish_expr(&mut fa.base, target, false);
        }
        AstExpr::IndexAccess(ia) => {
            changed |= polish_expr(&mut ia.base, target, false);
            changed |= polish_expr(&mut ia.index, target, false);
        }
        AstExpr::Call(c) => {
            changed |= polish_expr(&mut c.callee, target, false);
            for a in &mut c.args {
                changed |= polish_expr(a, target, false);
            }
        }
        AstExpr::MethodCall(m) => {
            changed |= polish_expr(&mut m.receiver, target, false);
            for a in &mut m.args {
                changed |= polish_expr(a, target, false);
            }
        }
        AstExpr::SingleValue(inner) => {
            changed |= polish_expr(inner, target, in_bool_context);
        }
        AstExpr::TableConstructor(t) => {
            for f in &mut t.fields {
                match f {
                    super::common::AstTableField::Array(v) => {
                        changed |= polish_expr(v, target, false);
                    }
                    super::common::AstTableField::Record(r) => {
                        if let super::common::AstTableKey::Expr(k) = &mut r.key {
                            changed |= polish_expr(k, target, false);
                        }
                        changed |= polish_expr(&mut r.value, target, false);
                    }
                }
            }
        }
        AstExpr::FunctionExpr(func) => {
            let child_cap = collect_captured_names_in_block(&func.body);
            let child_dbg = collect_debug_hinted_names_in_block(&func.body);
            changed |= polish_block(
                &mut func.body,
                target,
                true,
                true,
                &child_cap,
                &child_dbg,
            );
        }
        _ => {}
    }
    changed
}

fn pure_primitive_literal_order_key(expr: &AstExpr) -> Option<(u8, i64, u64, Vec<u8>)> {
    match expr {
        AstExpr::Nil => Some((0, 0, 0, Vec::new())),
        AstExpr::Boolean(b) => Some((1, i64::from(*b), 0, Vec::new())),
        AstExpr::Integer(i) => Some((2, *i, 0, Vec::new())),
        AstExpr::Number(n) => Some((3, 0, n.to_bits(), Vec::new())),
        AstExpr::String(s) => Some((4, 0, 0, s.as_bytes().to_vec())),
        _ => None,
    }
}

/// 安全的条件取反（严守浮点 `NaN` 语义：不将 `not (a < b)` 改写为 `a >= b`）。
fn negate_condition_safe(expr: AstExpr) -> AstExpr {
    match expr {
        AstExpr::Boolean(b) => AstExpr::Boolean(!b),
        AstExpr::Unary(u) if u.op == AstUnaryOpKind::Not => u.expr,
        other => AstExpr::Unary(Box::new(AstUnaryExpr {
            op: AstUnaryOpKind::Not,
            expr: other,
        })),
    }
}

/// `local f; f = function(...) end` → `local function f(...) end`
fn fold_pure_method_calls_in_stmt(
    stmt: &mut AstStmt,
    captured: &BTreeSet<AstNameRef>,
    debug_hinted: &BTreeSet<AstNameRef>,
) -> bool {
    let mut changed = false;
    match stmt {
        AstStmt::LocalDecl(d) => {
            for v in &mut d.values {
                changed |= fold_pure_method_calls_in_expr(v, captured, debug_hinted);
            }
        }
        AstStmt::GlobalDecl(d) => {
            for v in &mut d.values {
                changed |= fold_pure_method_calls_in_expr(v, captured, debug_hinted);
            }
        }
        AstStmt::Assign(a) => {
            for t in &mut a.targets {
                match t {
                    AstLValue::FieldAccess(f) => {
                        changed |=
                            fold_pure_method_calls_in_expr(&mut f.base, captured, debug_hinted);
                    }
                    AstLValue::IndexAccess(ia) => {
                        changed |=
                            fold_pure_method_calls_in_expr(&mut ia.base, captured, debug_hinted);
                        changed |=
                            fold_pure_method_calls_in_expr(&mut ia.index, captured, debug_hinted);
                    }
                    AstLValue::Name(_) => {}
                }
            }
            for v in &mut a.values {
                changed |= fold_pure_method_calls_in_expr(v, captured, debug_hinted);
            }
        }
        AstStmt::CallStmt(cs) => match &mut cs.call {
            AstCallKind::Call(c) => {
                changed |= fold_pure_method_calls_in_expr(&mut c.callee, captured, debug_hinted);
                for a in &mut c.args {
                    changed |= fold_pure_method_calls_in_expr(a, captured, debug_hinted);
                }
                if let Some(method) =
                    try_convert_pure_receiver_call_to_method(c, captured, debug_hinted)
                {
                    cs.call = AstCallKind::MethodCall(Box::new(method));
                    changed = true;
                }
            }
            AstCallKind::MethodCall(m) => {
                changed |= fold_pure_method_calls_in_expr(&mut m.receiver, captured, debug_hinted);
                for a in &mut m.args {
                    changed |= fold_pure_method_calls_in_expr(a, captured, debug_hinted);
                }
            }
        },
        AstStmt::Return(r) => {
            for v in &mut r.values {
                changed |= fold_pure_method_calls_in_expr(v, captured, debug_hinted);
            }
        }
        AstStmt::If(i) => {
            changed |= fold_pure_method_calls_in_expr(&mut i.cond, captured, debug_hinted);
        }
        AstStmt::While(w) => {
            changed |= fold_pure_method_calls_in_expr(&mut w.cond, captured, debug_hinted);
        }
        AstStmt::Repeat(r) => {
            changed |= fold_pure_method_calls_in_expr(&mut r.cond, captured, debug_hinted);
        }
        AstStmt::NumericFor(nf) => {
            changed |= fold_pure_method_calls_in_expr(&mut nf.start, captured, debug_hinted);
            changed |= fold_pure_method_calls_in_expr(&mut nf.limit, captured, debug_hinted);
            changed |= fold_pure_method_calls_in_expr(&mut nf.step, captured, debug_hinted);
        }
        AstStmt::GenericFor(gf) => {
            for e in &mut gf.iterator {
                changed |= fold_pure_method_calls_in_expr(e, captured, debug_hinted);
            }
        }
        _ => {}
    }
    changed
}

fn fold_pure_method_calls_in_expr(
    expr: &mut AstExpr,
    captured: &BTreeSet<AstNameRef>,
    debug_hinted: &BTreeSet<AstNameRef>,
) -> bool {
    let mut changed = false;
    match expr {
        AstExpr::Unary(u) => {
            changed |= fold_pure_method_calls_in_expr(&mut u.expr, captured, debug_hinted)
        }
        AstExpr::Binary(b) => {
            changed |= fold_pure_method_calls_in_expr(&mut b.lhs, captured, debug_hinted);
            changed |= fold_pure_method_calls_in_expr(&mut b.rhs, captured, debug_hinted);
        }
        AstExpr::LogicalAnd(l) | AstExpr::LogicalOr(l) => {
            changed |= fold_pure_method_calls_in_expr(&mut l.lhs, captured, debug_hinted);
            changed |= fold_pure_method_calls_in_expr(&mut l.rhs, captured, debug_hinted);
        }
        AstExpr::IfExpr(ie) => {
            changed |= fold_pure_method_calls_in_expr(&mut ie.cond, captured, debug_hinted);
            changed |= fold_pure_method_calls_in_expr(&mut ie.then_expr, captured, debug_hinted);
            changed |= fold_pure_method_calls_in_expr(&mut ie.else_expr, captured, debug_hinted);
        }
        AstExpr::FieldAccess(f) => {
            changed |= fold_pure_method_calls_in_expr(&mut f.base, captured, debug_hinted);
        }
        AstExpr::IndexAccess(ia) => {
            changed |= fold_pure_method_calls_in_expr(&mut ia.base, captured, debug_hinted);
            changed |= fold_pure_method_calls_in_expr(&mut ia.index, captured, debug_hinted);
        }
        AstExpr::Call(c) => {
            changed |= fold_pure_method_calls_in_expr(&mut c.callee, captured, debug_hinted);
            for a in &mut c.args {
                changed |= fold_pure_method_calls_in_expr(a, captured, debug_hinted);
            }
            if let Some(method) =
                try_convert_pure_receiver_call_to_method(c, captured, debug_hinted)
            {
                *expr = AstExpr::MethodCall(Box::new(method));
                return true;
            }
        }
        AstExpr::MethodCall(m) => {
            changed |= fold_pure_method_calls_in_expr(&mut m.receiver, captured, debug_hinted);
            for a in &mut m.args {
                changed |= fold_pure_method_calls_in_expr(a, captured, debug_hinted);
            }
        }
        AstExpr::TableConstructor(t) => {
            for f in &mut t.fields {
                match f {
                    super::common::AstTableField::Array(v) => {
                        changed |= fold_pure_method_calls_in_expr(v, captured, debug_hinted);
                    }
                    super::common::AstTableField::Record(r) => {
                        if let super::common::AstTableKey::Expr(k) = &mut r.key {
                            changed |= fold_pure_method_calls_in_expr(k, captured, debug_hinted);
                        }
                        changed |=
                            fold_pure_method_calls_in_expr(&mut r.value, captured, debug_hinted);
                    }
                }
            }
        }
        AstExpr::SingleValue(inner) => {
            changed |= fold_pure_method_calls_in_expr(inner, captured, debug_hinted);
        }
        _ => {}
    }
    changed
}

fn try_convert_pure_receiver_call_to_method(
    c: &mut AstCallExpr,
    captured: &BTreeSet<AstNameRef>,
    debug_hinted: &BTreeSet<AstNameRef>,
) -> Option<super::common::AstMethodCallExpr> {
    let AstExpr::FieldAccess(fa) = &c.callee else {
        return None;
    };
    let AstExpr::Var(recv) = &fa.base else {
        return None;
    };
    // 含 debug 名称的局部可能在 `__index` 中经 `debug.setlocal` 被反射改写，
    // 保留显式 `obj.m(obj)` 的两次读取语义，避免与原生 `SELF` 混淆。
    if !matches!(
        recv,
        AstNameRef::Local(_) | AstNameRef::Param(_) | AstNameRef::SyntheticLocal(_)
    ) || captured.contains(recv)
        || debug_hinted.contains(recv)
    {
        return None;
    }
    if c.args.first() != Some(&fa.base) {
        return None;
    }
    let receiver = c.args.remove(0);
    let AstExpr::FieldAccess(fa) = std::mem::replace(&mut c.callee, AstExpr::Nil) else {
        unreachable!()
    };
    Some(super::common::AstMethodCallExpr {
        receiver,
        method: fa.field,
        args: std::mem::take(&mut c.args),
        interpolation: None,
    })
}

fn try_fold_local_function_pair(stmts: &mut Vec<AstStmt>, idx: usize) -> bool {
    let matches = matches!(
        (&stmts[idx], &stmts[idx + 1]),
        (AstStmt::LocalDecl(decl), AstStmt::Assign(assign))
            if decl.bindings.len() == 1
                && decl.bindings[0].attr == AstLocalAttr::None
                && decl.values.is_empty()
                && assign.compound_op.is_none()
                && assign.targets.len() == 1
                && assign.values.len() == 1
                && matches!(&assign.targets[0], AstLValue::Name(n) if decl.bindings[0].id.matches_name_ref(n))
                && matches!(&assign.values[0], AstExpr::FunctionExpr(_))
    );
    if !matches {
        return false;
    }
    let AstStmt::LocalDecl(decl) = stmts.remove(idx) else {
        unreachable!()
    };
    let AstStmt::Assign(mut assign) = stmts.remove(idx) else {
        unreachable!()
    };
    let AstExpr::FunctionExpr(func) = assign.values.pop().unwrap() else {
        unreachable!()
    };
    stmts.insert(
        idx,
        AstStmt::LocalFunctionDecl(Box::new(AstLocalFunctionDecl {
            name: decl.bindings[0].id,
            func: *func,
        })),
    );
    true
}

/// `local x; x = expr` → `local x = expr`（常由 `if` 折叠为短路赋值表达式后产生）；
/// `local x = nil; x = nil` → `local x = nil`（消除重编译拆分 `LOADNIL` 产生的冗余空赋值）。
fn try_fold_empty_local_init_pair(stmts: &mut Vec<AstStmt>, idx: usize) -> bool {
    let redundant_nil_assign = matches!(
        (&stmts[idx], &stmts[idx + 1]),
        (AstStmt::LocalDecl(decl), AstStmt::Assign(assign))
            if decl.bindings.len() == 1
                && decl.bindings[0].attr == AstLocalAttr::None
                && decl.values.len() == 1
                && matches!(decl.values[0], AstExpr::Nil)
                && assign.compound_op.is_none()
                && assign.targets.len() == 1
                && assign.values.len() == 1
                && matches!(assign.values[0], AstExpr::Nil)
                && matches!(&assign.targets[0], AstLValue::Name(n) if decl.bindings[0].id.matches_name_ref(n))
    );
    if redundant_nil_assign {
        stmts.remove(idx + 1);
        return true;
    }
    let matches = matches!(
        (&stmts[idx], &stmts[idx + 1]),
        (AstStmt::LocalDecl(decl), AstStmt::Assign(assign))
            if decl.bindings.len() == 1
                && decl.bindings[0].attr == AstLocalAttr::None
                && decl.values.is_empty()
                && assign.compound_op.is_none()
                && assign.targets.len() == 1
                && assign.values.len() == 1
                && matches!(&assign.targets[0], AstLValue::Name(n) if decl.bindings[0].id.matches_name_ref(n))
                && !expr_mentions_name_ref(&assign.values[0], &decl.bindings[0].id.to_name_ref())
                && !expr_captures_binding(&assign.values[0], decl.bindings[0].id)
    );
    if !matches {
        return false;
    }
    let AstStmt::Assign(mut assign) = stmts.remove(idx + 1) else {
        unreachable!()
    };
    let AstStmt::LocalDecl(decl) = &mut stmts[idx] else {
        unreachable!()
    };
    decl.values = std::mem::take(&mut assign.values);
    true
}

fn expr_captures_binding(expr: &AstExpr, target: AstBindingRef) -> bool {
    for node in expr_nodes(expr) {
        if let ExprNode::Function(func) = node
            && func.captured_bindings.contains(&target)
        {
            return true;
        }
    }
    false
}

/// 合并多返回调用后的死接棒赋值：`[local] t1, t2 = f(...); b = t2; a = t1` → `a, b = f(...)`。
///
/// 将紧随 `local ..., t_p, ... = vals` 之后的单用冗余局部拷贝 `local d = t_p`（含多返回值逆序/部分接棒）
/// 直接吸收到前导 `LocalDecl` 对应槽位中，零开销消除 `local r1, r2 = f(); local y = r2; local x = r1`。
fn try_absorb_following_local_copies(
    stmts: &mut Vec<AstStmt>,
    idx: usize,
    captured: &BTreeSet<AstNameRef>,
) -> bool {
    let mut absorbed = false;
    while idx + 1 < stmts.len() {
        let (pos, new_binding) = {
            let AstStmt::LocalDecl(decl) = &stmts[idx] else {
                break;
            };
            if decl.bindings.is_empty() || decl.values.is_empty() {
                break;
            }
            let AstStmt::LocalDecl(next) = &stmts[idx + 1] else {
                break;
            };
            if next.bindings.len() != 1
                || next.values.len() != 1
                || next.bindings[0].attr == AstLocalAttr::Close
            {
                break;
            }
            let AstExpr::Var(src_name) = &next.values[0] else {
                break;
            };
            let Some(pos) = decl.bindings.iter().position(|b| {
                b.attr == AstLocalAttr::None
                    && !b.is_debug_hinted
                    && b.id.to_name_ref() == *src_name
                    && !captured.contains(src_name)
            }) else {
                break;
            };
            let new_id = next.bindings[0].id;
            let new_name = new_id.to_name_ref();
            if decl.bindings.iter().any(|b| b.id == new_id)
                || decl
                    .values
                    .iter()
                    .any(|v| expr_mentions_name_ref(v, &new_name))
                || stmts[idx + 2..]
                    .iter()
                    .any(|s| stmt_mentions_name_ref(s, src_name))
            {
                break;
            }
            (pos, next.bindings[0].clone())
        };
        if let AstStmt::LocalDecl(decl) = &mut stmts[idx] {
            decl.bindings[pos] = new_binding;
        }
        stmts.remove(idx + 1);
        absorbed = true;
    }
    absorbed
}

/// 还原 Lua 编译平行多赋值 `lhs_0, ..., lhs_{k-1} = rhs_0, ..., rhs_{k-1}` 时生成的
/// “匿名临时快照 + 逆序逐项写回”序列（如 `local t0 = a; A.max = b; A.min = t0` 或
/// `local t0 = e0; local t1 = e1; x2 = e2; x1 = t1; x0 = t0`）。
///
/// 严格守住求值顺序、变量别名与目标方言存储顺序（PUC Lua 5.1~5.5/LuaJIT 右向左存储，Luau 左向右存储）。
fn try_coalesce_reverse_parallel_assign(
    stmts: &mut Vec<AstStmt>,
    assign_start: usize,
    target: AstTargetDialect,
    captured: &BTreeSet<AstNameRef>,
) -> Option<usize> {
    if assign_start == 0 || assign_start + 1 >= stmts.len() {
        return None;
    }
    let AstStmt::Assign(first_assign) = &stmts[assign_start] else {
        return None;
    };
    if first_assign.compound_op.is_some()
        || first_assign.targets.len() != 1
        || first_assign.values.len() != 1
    {
        return None;
    }

    // 1. 从 `assign_start` 向前收集最多 16 条连续匿名临时局部声明
    let max_lookback = assign_start.min(16);
    let mut temp_decl_pos: BTreeMap<AstNameRef, usize> = BTreeMap::new();
    let mut suffix_start = assign_start;
    for offset in 1..=max_lookback {
        let pos = assign_start - offset;
        let Some((name, _)) = anon_single_temp_decl(&stmts[pos], captured) else {
            break;
        };
        temp_decl_pos.insert(name, pos);
        suffix_start = pos;
    }
    if temp_decl_pos.is_empty() {
        return None;
    }

    // 2. 从 `assign_start + 1` 向后收集严格按声明位置递减引用的逆序赋值链
    let mut rev_rhs_tmps: Vec<(AstNameRef, usize)> = Vec::new();
    let mut prev_pos = usize::MAX;
    let mut cursor = assign_start + 1;
    while cursor < stmts.len() {
        let AstStmt::Assign(a) = &stmts[cursor] else {
            break;
        };
        if a.compound_op.is_some() || a.targets.len() != 1 || a.values.len() != 1 {
            break;
        }
        let AstExpr::Var(src_name) = &a.values[0] else {
            break;
        };
        let Some(&dpos) = temp_decl_pos.get(src_name) else {
            break;
        };
        if dpos >= prev_pos {
            break;
        }
        prev_pos = dpos;
        rev_rhs_tmps.push((src_name.clone(), dpos));
        cursor += 1;
    }
    if rev_rhs_tmps.is_empty() {
        return None;
    }

    let k = 1 + rev_rhs_tmps.len();
    let assign_end = assign_start + k;
    let first_rhs_pos = rev_rhs_tmps.last().unwrap().1;

    // 按最终多赋值顺序排列目标：[dst_0 (assign_end - 1), ..., dst_{k-1} (assign_start)]
    let dst_indices: Vec<usize> = (assign_start..assign_end).rev().collect();
    let dst_lvalues: Vec<&AstLValue> = dst_indices
        .iter()
        .map(|&si| match &stmts[si] {
            AstStmt::Assign(a) => &a.targets[0],
            _ => unreachable!(),
        })
        .collect();

    // 3. 向前延伸窗口以纳入紧邻的 LHS 基址/下标快照临时（如 `local t = A; local v = a; A.max = b; t.min = v`）
    let mut win_start = first_rhs_pos;
    while win_start > suffix_start {
        let prev = win_start - 1;
        let Some((name, _)) = anon_single_temp_decl(&stmts[prev], captured) else {
            break;
        };
        if dst_lvalues
            .iter()
            .any(|lv| lvalue_subexprs_mention(lv, &name))
        {
            win_start = prev;
        } else {
            break;
        }
    }

    // 4. 校验窗口内每条临时声明：严格单用、无交叉依赖、后续完全死亡，且 LHS 快照早于所有 RHS 并保序
    let rhs_tmp_pos_set: BTreeSet<usize> = rev_rhs_tmps.iter().map(|(_, p)| *p).collect();
    let mut lhs_snapshot_names: BTreeSet<AstNameRef> = BTreeSet::new();
    let mut last_lhs_slot: Option<(usize, u8)> = None;
    for pos in win_start..assign_start {
        let (tmp_name, _) = anon_single_temp_decl(&stmts[pos], captured)?;
        // 临时变量自身不得作为任意逆序赋值的直接目标（否则先覆写该变量再读取会改变语义，如 `local t = true; t = false; x = t`）
        if dst_lvalues
            .iter()
            .any(|lv| matches!(lv, AstLValue::Name(n) if n == &tmp_name))
        {
            return None;
        }
        if stmts[assign_end..]
            .iter()
            .any(|s| stmt_mentions_name_ref(s, &tmp_name))
        {
            return None;
        }
        for (other_pos, other_stmt) in stmts
            .iter()
            .enumerate()
            .take(assign_start)
            .skip(win_start)
        {
            if other_pos != pos {
                let (_, other_init) = anon_single_temp_decl(other_stmt, captured)?;
                if expr_mentions_name_ref(other_init, &tmp_name) {
                    return None;
                }
            }
        }
        if expr_mentions_name_ref(&first_assign.values[0], &tmp_name) {
            return None;
        }
        if rhs_tmp_pos_set.contains(&pos) {
            if dst_lvalues
                .iter()
                .any(|lv| lvalue_subexprs_mention(lv, &tmp_name))
            {
                return None;
            }
        } else {
            // LHS 基址/下标快照：必须位于全部 RHS 临时之前，且仅作为某一目标的整块 base/index 出现恰好一次
            if pos >= first_rhs_pos {
                return None;
            }
            let mut match_slot: Option<(usize, u8)> = None;
            for (ti, lv) in dst_lvalues.iter().enumerate() {
                match lv {
                    AstLValue::Name(_) => {}
                    AstLValue::FieldAccess(f) => {
                        if matches!(&f.base, AstExpr::Var(n) if n == &tmp_name) {
                            if match_slot.is_some() {
                                return None;
                            }
                            match_slot = Some((ti, 0));
                        } else if expr_mentions_name_ref(&f.base, &tmp_name) {
                            return None;
                        }
                    }
                    AstLValue::IndexAccess(ia) => {
                        if matches!(&ia.base, AstExpr::Var(n) if n == &tmp_name) {
                            if match_slot.is_some() {
                                return None;
                            }
                            match_slot = Some((ti, 0));
                        } else if expr_mentions_name_ref(&ia.base, &tmp_name) {
                            return None;
                        }
                        if matches!(&ia.index, AstExpr::Var(n) if n == &tmp_name) {
                            if match_slot.is_some() {
                                return None;
                            }
                            match_slot = Some((ti, 1));
                        } else if expr_mentions_name_ref(&ia.index, &tmp_name) {
                            return None;
                        }
                    }
                }
            }
            let slot = match_slot?;
            if let Some(prev_slot) = last_lhs_slot
                && slot <= prev_slot
            {
                return None;
            }
            last_lhs_slot = Some(slot);
            lhs_snapshot_names.insert(tmp_name);
        }
    }

    // 5. 目标去重与方言存储序检查（Luau 多赋值左向右存储，带表/全局写时禁止将逆序写回合流）
    let mut seen_target_names: BTreeSet<AstNameRef> = BTreeSet::new();
    let mut has_observable_store = false;
    for lv in &dst_lvalues {
        match lv {
            AstLValue::Name(n) => {
                if !seen_target_names.insert(n.clone()) {
                    return None;
                }
                if !matches!(
                    n,
                    AstNameRef::Local(_) | AstNameRef::Param(_) | AstNameRef::Upvalue(_)
                ) {
                    has_observable_store = true;
                }
            }
            AstLValue::FieldAccess(_) | AstLValue::IndexAccess(_) => {
                has_observable_store = true;
            }
        }
    }
    if has_observable_store && target.version == crate::decompile::DecompileDialect::Luau {
        return None;
    }

    // 6. 检查非快照 LHS 子表达式前移到所有 RHS 求值之前是否严格保序
    let all_rhs_pure_no_global = rev_rhs_tmps.iter().all(|(_, p)| {
        anon_single_temp_decl(&stmts[*p], captured).is_some_and(|(_, init)| {
            expr_is_pure_inlineable(init) && !expr_contains_global_var(init)
        })
    }) && expr_is_pure_inlineable(&first_assign.values[0])
        && !expr_contains_global_var(&first_assign.values[0]);

    for (i, lv) in dst_lvalues.iter().enumerate() {
        let mut written_before_i: BTreeSet<AstNameRef> = BTreeSet::new();
        let mut table_store_before_i = false;
        for later_lv in &dst_lvalues[(i + 1)..] {
            match later_lv {
                AstLValue::Name(n) => {
                    written_before_i.insert(n.clone());
                    if !matches!(
                        n,
                        AstNameRef::Local(_) | AstNameRef::Param(_) | AstNameRef::Upvalue(_)
                    ) {
                        table_store_before_i = true;
                    }
                }
                AstLValue::FieldAccess(_) | AstLValue::IndexAccess(_) => {
                    table_store_before_i = true;
                }
            }
        }
        let check_subexpr = |expr: &AstExpr| -> bool {
            if let AstExpr::Var(n) = expr
                && lhs_snapshot_names.contains(n)
            {
                return true;
            }
            match expr {
                AstExpr::Nil
                | AstExpr::Boolean(_)
                | AstExpr::Integer(_)
                | AstExpr::Number(_)
                | AstExpr::String(_) => true,
                AstExpr::Var(n @ (AstNameRef::Local(_) | AstNameRef::Param(_)))
                    if !captured.contains(n) =>
                {
                    !written_before_i.contains(n)
                }
                AstExpr::Var(n @ (AstNameRef::Upvalue(_) | AstNameRef::Local(_))) => {
                    !written_before_i.contains(n) && !table_store_before_i && all_rhs_pure_no_global
                }
                _ => false,
            }
        };
        match lv {
            AstLValue::Name(_) => {}
            AstLValue::FieldAccess(f) => {
                if !check_subexpr(&f.base) {
                    return None;
                }
            }
            AstLValue::IndexAccess(ia) => {
                if !check_subexpr(&ia.base) || !check_subexpr(&ia.index) {
                    return None;
                }
            }
        }
    }

    // 7. 全部护栏通过：将窗口与逆序赋值链合流为单条平行多赋值语句
    let split = assign_start - win_start;
    let mut temp_inits: BTreeMap<AstNameRef, AstExpr> = BTreeMap::new();
    let mut assign_stmts: Vec<Box<AstAssign>> = Vec::with_capacity(k);
    for (offset, stmt) in stmts.drain(win_start..assign_end).enumerate() {
        if offset < split {
            let AstStmt::LocalDecl(mut d) = stmt else {
                unreachable!()
            };
            let name = d.bindings[0].id.to_name_ref();
            temp_inits.insert(name, d.values.pop().unwrap());
        } else {
            let AstStmt::Assign(a) = stmt else {
                unreachable!()
            };
            assign_stmts.push(a);
        }
    }

    let mut last_assign = assign_stmts.remove(0);
    let last_target = last_assign.targets.pop().unwrap();
    let last_value = last_assign.values.pop().unwrap();

    let mut targets = Vec::with_capacity(k);
    let mut values = Vec::with_capacity(k);
    for mut assign in assign_stmts.into_iter().rev() {
        let mut lv = assign.targets.pop().unwrap();
        substitute_lhs_snapshot(&mut lv, &mut temp_inits);
        let AstExpr::Var(rhs_tmp) = assign.values.pop().unwrap() else {
            unreachable!()
        };
        targets.push(lv);
        values.push(temp_inits.remove(&rhs_tmp).unwrap());
    }
    let mut last_target = last_target;
    substitute_lhs_snapshot(&mut last_target, &mut temp_inits);
    targets.push(last_target);
    values.push(last_value);

    stmts.insert(
        win_start,
        AstStmt::Assign(Box::new(AstAssign {
            targets,
            values,
            compound_op: None,
        })),
    );
    Some(win_start)
}

fn anon_single_temp_decl<'a>(
    stmt: &'a AstStmt,
    captured: &BTreeSet<AstNameRef>,
) -> Option<(AstNameRef, &'a AstExpr)> {
    let AstStmt::LocalDecl(d) = stmt else {
        return None;
    };
    if d.bindings.len() != 1
        || d.values.len() != 1
        || d.bindings[0].attr != AstLocalAttr::None
        || d.bindings[0].is_debug_hinted
    {
        return None;
    }
    let name = d.bindings[0].id.to_name_ref();
    if captured.contains(&name) {
        return None;
    }
    Some((name, &d.values[0]))
}

fn lvalue_subexprs_mention(lv: &AstLValue, target: &AstNameRef) -> bool {
    match lv {
        AstLValue::Name(_) => false,
        AstLValue::FieldAccess(f) => expr_mentions_name_ref(&f.base, target),
        AstLValue::IndexAccess(ia) => {
            expr_mentions_name_ref(&ia.base, target) || expr_mentions_name_ref(&ia.index, target)
        }
    }
}

fn substitute_lhs_snapshot(lv: &mut AstLValue, temp_inits: &mut BTreeMap<AstNameRef, AstExpr>) {
    match lv {
        AstLValue::Name(_) => {}
        AstLValue::FieldAccess(f) => {
            if let AstExpr::Var(n) = &f.base
                && let Some(init) = temp_inits.remove(n)
            {
                f.base = init;
            }
        }
        AstLValue::IndexAccess(ia) => {
            if let AstExpr::Var(n) = &ia.base
                && let Some(init) = temp_inits.remove(n)
            {
                ia.base = init;
            }
            if let AstExpr::Var(n) = &ia.index
                && let Some(init) = temp_inits.remove(n)
            {
                ia.index = init;
            }
        }
    }
}

fn expr_contains_global_var(expr: &AstExpr) -> bool {
    expr_nodes(expr).any(|n| matches!(n, ExprNode::Expr(AstExpr::Var(AstNameRef::Global(_)))))
}

/// Lua 编译 `a, b = f(...)`（当 `a`/`b` 是既有局部时）总是把结果写入临时寄存器再逆序 `MOVE` 写回；
/// 只要全部临时 `t_k` 非捕获、非 `<close>`、无 debug 提示且在接棒之后立即死亡，直接合流消除重编译接棒链膨胀！
fn try_coalesce_multi_assign(
    stmts: &mut Vec<AstStmt>,
    idx: usize,
    is_function_root: bool,
    target: AstTargetDialect,
    captured: &BTreeSet<AstNameRef>,
) -> bool {
    let (is_local_decl, temp_locals): (bool, Vec<AstBindingRef>) = match &stmts[idx] {
        AstStmt::LocalDecl(decl)
            if decl.values.len() == 1
                && decl.bindings.len() >= 2
                && decl.bindings.iter().all(|b| {
                    b.attr == AstLocalAttr::None
                        && !b.is_debug_hinted
                        && !captured.contains(&b.id.to_name_ref())
                }) =>
        {
            (true, decl.bindings.iter().map(|b| b.id).collect())
        }
        AstStmt::Assign(assign)
            if assign.compound_op.is_none()
                && assign.values.len() == 1
                && assign.targets.len() >= 2
                && assign.targets.iter().all(|t| {
                    matches!(t, AstLValue::Name(AstNameRef::Local(l))
                        if !captured.contains(&AstNameRef::Local(*l)))
                }) =>
        {
            let ids = assign
                .targets
                .iter()
                .map(|t| match t {
                    AstLValue::Name(AstNameRef::Local(l)) => AstBindingRef::Local(*l),
                    _ => unreachable!(),
                })
                .collect();
            (false, ids)
        }
        _ => return false,
    };

    let n = temp_locals.len();
    if idx + n >= stmts.len() {
        return false;
    }
    let temp_set: BTreeSet<AstBindingRef> = temp_locals.iter().copied().collect();
    if temp_set.len() != n {
        return false;
    }

    let mut mapped_dsts: Vec<Option<AstLValue>> = vec![None; n];
    let mut dst_order_indices: Vec<usize> = Vec::with_capacity(n);
    let mut seen_dst_names: BTreeSet<AstNameRef> = BTreeSet::new();
    let mut all_local_or_param_or_upval = true;
    for step in 0..n {
        let AstStmt::Assign(copy) = &stmts[idx + 1 + step] else {
            return false;
        };
        if copy.compound_op.is_some() || copy.targets.len() != 1 || copy.values.len() != 1 {
            return false;
        }
        let AstExpr::Var(src_name) = &copy.values[0] else {
            return false;
        };
        let Some(pos) = temp_locals.iter().position(|b| b.to_name_ref() == *src_name) else {
            return false;
        };
        if mapped_dsts[pos].is_some() {
            return false;
        }
        match &copy.targets[0] {
            AstLValue::Name(dst_name) => {
                if temp_locals.iter().any(|b| b.to_name_ref() == *dst_name) {
                    return false;
                }
                if !seen_dst_names.insert(dst_name.clone()) {
                    return false;
                }
                if !matches!(
                    dst_name,
                    AstNameRef::Local(_) | AstNameRef::Param(_) | AstNameRef::Upvalue(_)
                ) {
                    all_local_or_param_or_upval = false;
                }
            }
            _ => return false,
        }
        mapped_dsts[pos] = Some(copy.targets[0].clone());
        dst_order_indices.push(pos);
    }

    // 含全局/表字段等可观察写目标时，必须与目标方言的多赋值落地顺序一致：
    // PUC Lua / LuaJIT 按从右到左（`n - 1 - step`）写入，Luau 按从左到右（`step`）写入。
    let order_matches = if target.version == crate::decompile::DecompileDialect::Luau {
        dst_order_indices
            .iter()
            .enumerate()
            .all(|(step, &pos)| pos == step)
    } else {
        dst_order_indices
            .iter()
            .enumerate()
            .all(|(step, &pos)| pos == n - 1 - step)
    };
    if !all_local_or_param_or_upval && !order_matches {
        return false;
    }

    for &b in &temp_locals {
        let name = b.to_name_ref();
        if !is_local_decl && !is_function_root && !block_declares_binding_before(stmts, idx, b) {
            return false;
        }
        if is_local_decl {
            if stmts[idx + 1 + n..]
                .iter()
                .any(|s| stmt_mentions_name_ref(s, &name))
            {
                return false;
            }
        } else {
            let allow_exit_dead =
                is_function_root || block_declares_binding_before(stmts, idx, b);
            if !is_dead_before_overwrite(&stmts[idx + 1 + n..], &name, allow_exit_dead) {
                return false;
            }
        }
    }

    let values = match &mut stmts[idx] {
        AstStmt::LocalDecl(d) => std::mem::take(&mut d.values),
        AstStmt::Assign(a) => std::mem::take(&mut a.values),
        _ => unreachable!(),
    };
    let targets: Vec<AstLValue> = mapped_dsts.into_iter().map(Option::unwrap).collect();
    stmts[idx] = AstStmt::Assign(Box::new(AstAssign {
        targets,
        values,
        compound_op: None,
    }));
    stmts.drain((idx + 1)..=(idx + n));
    true
}

fn collect_expr_var_names(expr: &AstExpr, out: &mut BTreeSet<AstNameRef>) {
    for node in expr_nodes(expr) {
        if let ExprNode::Expr(AstExpr::Var(n)) = node {
            out.insert(n.clone());
        }
    }
}

fn block_declares_binding_before(stmts: &[AstStmt], limit: usize, binding: AstBindingRef) -> bool {
    stmts[..limit].iter().any(|s| {
        matches!(
            s,
            AstStmt::LocalDecl(d) if d.bindings.iter().any(|b| {
                b.id == binding && b.attr == AstLocalAttr::None && !b.is_debug_hinted
            })
        )
    })
}

/// 检查变量 `name` 在 `tail` 语句序列中是否在任何读取之前即被无条件覆写或到达函数/作用域末尾（即死变量）。
/// 当 `allow_block_exit_dead` 为 `false`（外层局部处于 `if`/`while`/`for` 嵌套块中）时，到达块尾不得视为死亡！
fn is_dead_before_overwrite(
    tail: &[AstStmt],
    name: &AstNameRef,
    allow_block_exit_dead: bool,
) -> bool {
    for stmt in tail {
        match stmt {
            AstStmt::Assign(a) => {
                let lvalue_reads = a.targets.iter().any(|t| match t {
                    AstLValue::Name(n) => a.compound_op.is_some() && n == name,
                    AstLValue::FieldAccess(f) => expr_mentions_name_ref(&f.base, name),
                    AstLValue::IndexAccess(ia) => {
                        expr_mentions_name_ref(&ia.base, name)
                            || expr_mentions_name_ref(&ia.index, name)
                    }
                });
                if lvalue_reads || a.values.iter().any(|v| expr_mentions_name_ref(v, name)) {
                    return false;
                }
                if a.compound_op.is_none()
                    && a.targets
                        .iter()
                        .any(|t| matches!(t, AstLValue::Name(n) if n == name))
                {
                    return true;
                }
            }
            AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) => {
                return false;
            }
            AstStmt::Return(r) => {
                return !r.values.iter().any(|v| expr_mentions_name_ref(v, name));
            }
            other => {
                if stmt_mentions_name_ref(other, name) {
                    return false;
                }
            }
        }
    }
    allow_block_exit_dead
}

/// 清理无初始化值的空 `local t1, t2` 中已完全不再被读取的匿名临时绑定（含对其的死纯字面量写回）。
fn prune_unused_empty_local_decls(
    stmts: &mut Vec<AstStmt>,
    captured: &BTreeSet<AstNameRef>,
) -> bool {
    let mut changed = false;
    let mut idx = 0;
    while idx < stmts.len() {
        let should_inspect = matches!(
            &stmts[idx],
            AstStmt::LocalDecl(d)
                if d.values.is_empty()
                    && d.bindings
                        .iter()
                        .any(|b| b.attr == AstLocalAttr::None && !b.is_debug_hinted)
        );
        if !should_inspect {
            idx += 1;
            continue;
        }
        let mut keep = Vec::new();
        let mut removed_names = Vec::new();
        if let AstStmt::LocalDecl(d) = &stmts[idx] {
            for b in &d.bindings {
                let name = b.id.to_name_ref();
                let is_dead_anon = b.attr == AstLocalAttr::None
                    && !b.is_debug_hinted
                    && !captured.contains(&name)
                    && stmts[idx + 1..]
                        .iter()
                        .all(|s| stmt_has_no_reads_and_only_pure_writes(s, &name));
                if is_dead_anon {
                    removed_names.push(name);
                } else {
                    keep.push(b.clone());
                }
            }
        }
        if !removed_names.is_empty() {
            changed = true;
            for dead_name in &removed_names {
                strip_pure_writes_in_stmts(&mut stmts[idx + 1..], dead_name);
                let mut k = idx + 1;
                while k < stmts.len() {
                    if is_pure_dead_write_assign(&stmts[k], dead_name) {
                        stmts.remove(k);
                    } else {
                        k += 1;
                    }
                }
            }
            if keep.is_empty() {
                stmts.remove(idx);
                continue;
            }
            if let AstStmt::LocalDecl(d) = &mut stmts[idx] {
                d.bindings = keep;
            }
        }
        idx += 1;
    }
    changed
}

fn is_pure_dead_write_assign(stmt: &AstStmt, target: &AstNameRef) -> bool {
    matches!(
        stmt,
        AstStmt::Assign(a)
            if a.compound_op.is_none()
                && a.targets.len() == 1
                && a.values.len() == 1
                && matches!(&a.targets[0], AstLValue::Name(n) if n == target)
                && matches!(
                    &a.values[0],
                    AstExpr::Nil
                        | AstExpr::Boolean(_)
                        | AstExpr::Integer(_)
                        | AstExpr::Number(_)
                        | AstExpr::String(_)
                )
    )
}

fn stmt_has_no_reads_and_only_pure_writes(stmt: &AstStmt, target: &AstNameRef) -> bool {
    if is_pure_dead_write_assign(stmt, target) {
        return true;
    }
    match stmt {
        AstStmt::If(i) => {
            !expr_mentions_name_ref(&i.cond, target)
                && i.then_block
                    .stmts
                    .iter()
                    .all(|s| stmt_has_no_reads_and_only_pure_writes(s, target))
                && i.else_block.as_ref().is_none_or(|eb| {
                    eb.stmts
                        .iter()
                        .all(|s| stmt_has_no_reads_and_only_pure_writes(s, target))
                })
        }
        AstStmt::DoBlock(b) => b
            .stmts
            .iter()
            .all(|s| stmt_has_no_reads_and_only_pure_writes(s, target)),
        AstStmt::While(w) => {
            !expr_mentions_name_ref(&w.cond, target)
                && w.body
                    .stmts
                    .iter()
                    .all(|s| stmt_has_no_reads_and_only_pure_writes(s, target))
        }
        AstStmt::Repeat(r) => {
            !expr_mentions_name_ref(&r.cond, target)
                && r.body
                    .stmts
                    .iter()
                    .all(|s| stmt_has_no_reads_and_only_pure_writes(s, target))
        }
        AstStmt::NumericFor(nf) => {
            !expr_mentions_name_ref(&nf.start, target)
                && !expr_mentions_name_ref(&nf.limit, target)
                && !expr_mentions_name_ref(&nf.step, target)
                && nf
                    .body
                    .stmts
                    .iter()
                    .all(|s| stmt_has_no_reads_and_only_pure_writes(s, target))
        }
        AstStmt::GenericFor(gf) => {
            !gf.iterator.iter().any(|e| expr_mentions_name_ref(e, target))
                && gf
                    .body
                    .stmts
                    .iter()
                    .all(|s| stmt_has_no_reads_and_only_pure_writes(s, target))
        }
        other => !stmt_mentions_name_ref(other, target),
    }
}

fn strip_pure_writes_in_stmts(stmts: &mut [AstStmt], target: &AstNameRef) {
    for stmt in stmts {
        match stmt {
            AstStmt::If(i) => {
                strip_pure_writes_in_block(&mut i.then_block, target);
                if let Some(eb) = &mut i.else_block {
                    strip_pure_writes_in_block(eb, target);
                }
            }
            AstStmt::DoBlock(b) => strip_pure_writes_in_block(b, target),
            AstStmt::While(w) => strip_pure_writes_in_block(&mut w.body, target),
            AstStmt::Repeat(r) => strip_pure_writes_in_block(&mut r.body, target),
            AstStmt::NumericFor(nf) => strip_pure_writes_in_block(&mut nf.body, target),
            AstStmt::GenericFor(gf) => strip_pure_writes_in_block(&mut gf.body, target),
            _ => {}
        }
    }
}

fn strip_pure_writes_in_block(block: &mut AstBlock, target: &AstNameRef) {
    block
        .stmts
        .retain(|s| !is_pure_dead_write_assign(s, target));
    strip_pure_writes_in_stmts(&mut block.stmts, target);
}

/// 还原因短路参数跨基本块冲刷而被拆散的三行 `SELF` 方法调用：
/// `local r1 = base; local r2 = r1.Method; r2(r1, args...)` → `base:Method(args...)`
/// （同样覆盖作为首值出现在 `local ... = r2(r1, ...)`、`x = r2(r1, ...)`、`return r2(r1, ...)` 的情形）。
fn try_fold_split_method_call(
    stmts: &mut Vec<AstStmt>,
    idx: usize,
    captured: &BTreeSet<AstNameRef>,
    debug_hinted: &BTreeSet<AstNameRef>,
) -> bool {
    if idx + 2 >= stmts.len() {
        return false;
    }
    let AstStmt::LocalDecl(d0) = &stmts[idx] else {
        return false;
    };
    if d0.bindings.len() != 1
        || d0.values.len() != 1
        || d0.bindings[0].attr != AstLocalAttr::None
        || d0.bindings[0].is_debug_hinted
        || matches!(d0.values[0], AstExpr::VarArg)
    {
        return false;
    }
    let obj_name = d0.bindings[0].id.to_name_ref();
    if captured.contains(&obj_name)
        || debug_hinted.contains(&obj_name)
        || expr_mentions_name_ref(&d0.values[0], &obj_name)
    {
        return false;
    }

    let AstStmt::LocalDecl(d1) = &stmts[idx + 1] else {
        return false;
    };
    if d1.bindings.len() != 1
        || d1.values.len() != 1
        || d1.bindings[0].attr != AstLocalAttr::None
        || d1.bindings[0].is_debug_hinted
    {
        return false;
    }
    let fn_name = d1.bindings[0].id.to_name_ref();
    if fn_name == obj_name || captured.contains(&fn_name) || debug_hinted.contains(&fn_name) {
        return false;
    }
    let AstExpr::FieldAccess(fa) = &d1.values[0] else {
        return false;
    };
    if !matches!(&fa.base, AstExpr::Var(v) if v == &obj_name) {
        return false;
    }

    // 校验第 3 句中位于纯前置表达式之后的首个调用是否恰好为 `r_fn(r_obj, ...)` 且无其它非法引用
    let call_matches = |c: &AstCallExpr| -> bool {
        matches!(&c.callee, AstExpr::Var(v) if v == &fn_name)
            && matches!(c.args.first(), Some(AstExpr::Var(v)) if v == &obj_name)
            && c.args[1..].iter().all(|a| {
                !expr_mentions_name_ref(a, &obj_name) && !expr_mentions_name_ref(a, &fn_name)
            })
    };
    let expr_clean = |v: &AstExpr| -> bool {
        !expr_mentions_name_ref(v, &obj_name) && !expr_mentions_name_ref(v, &fn_name)
    };
    let is_pure_prefix = |v: &AstExpr| -> bool {
        expr_clean(v)
            && expr_is_pure_inlineable(v)
            && !expr_reads_mutable_external_var(v, captured)
    };
    let find_matching_value_pos = |vals: &[AstExpr]| -> Option<usize> {
        for (pos, v) in vals.iter().enumerate() {
            if let AstExpr::Call(c) = v
                && call_matches(c)
            {
                return vals[pos + 1..].iter().all(expr_clean).then_some(pos);
            }
            if !is_pure_prefix(v) {
                return None;
            }
        }
        None
    };

    enum SplitMethodSite {
        CallStmtRoot,
        LocalDeclValue(usize),
        ReturnValue(usize),
        AssignValue(usize),
    }

    let site = match &stmts[idx + 2] {
        AstStmt::CallStmt(cs)
            if matches!(&cs.call, AstCallKind::Call(c) if call_matches(c)) =>
        {
            Some(SplitMethodSite::CallStmtRoot)
        }
        AstStmt::LocalDecl(d2) => find_matching_value_pos(&d2.values).map(SplitMethodSite::LocalDeclValue),
        AstStmt::Return(r) => find_matching_value_pos(&r.values).map(SplitMethodSite::ReturnValue),
        AstStmt::Assign(a)
            if a.compound_op.is_none()
                && a.targets.iter().all(|t| {
                    matches!(t, AstLValue::Name(n) if n != &obj_name && n != &fn_name)
                }) =>
        {
            find_matching_value_pos(&a.values).map(SplitMethodSite::AssignValue)
        }
        _ => None,
    };
    let Some(site) = site else {
        return false;
    };
    if stmts[idx + 3..]
        .iter()
        .any(|s| stmt_mentions_name_ref(s, &obj_name) || stmt_mentions_name_ref(s, &fn_name))
    {
        return false;
    }

    // 执行三行合并：`base:method(args[1..])`
    let AstStmt::LocalDecl(mut d0) = stmts.remove(idx) else {
        unreachable!()
    };
    let receiver = d0.values.pop().unwrap();
    let AstStmt::LocalDecl(mut d1) = stmts.remove(idx) else {
        unreachable!()
    };
    let AstExpr::FieldAccess(fa) = d1.values.pop().unwrap() else {
        unreachable!()
    };
    let method = fa.field;

    let build_method = |mut call: AstCallExpr| -> super::common::AstMethodCallExpr {
        let mut args = Vec::with_capacity(call.args.len().saturating_sub(1));
        if call.args.len() > 1 {
            args.extend(call.args.drain(1..));
        }
        super::common::AstMethodCallExpr {
            receiver,
            method,
            args,
            interpolation: None,
        }
    };

    match (&mut stmts[idx], site) {
        (AstStmt::CallStmt(cs), SplitMethodSite::CallStmtRoot) => {
            let old = std::mem::replace(
                &mut cs.call,
                AstCallKind::Call(Box::new(AstCallExpr {
                    callee: AstExpr::Nil,
                    args: Vec::new(),
                })),
            );
            let AstCallKind::Call(c) = old else {
                unreachable!()
            };
            cs.call = AstCallKind::MethodCall(Box::new(build_method(*c)));
        }
        (AstStmt::LocalDecl(d2), SplitMethodSite::LocalDeclValue(pos)) => {
            let AstExpr::Call(c) = std::mem::replace(&mut d2.values[pos], AstExpr::Nil) else {
                unreachable!()
            };
            d2.values[pos] = AstExpr::MethodCall(Box::new(build_method(*c)));
        }
        (AstStmt::Return(r), SplitMethodSite::ReturnValue(pos)) => {
            let AstExpr::Call(c) = std::mem::replace(&mut r.values[pos], AstExpr::Nil) else {
                unreachable!()
            };
            r.values[pos] = AstExpr::MethodCall(Box::new(build_method(*c)));
        }
        (AstStmt::Assign(a), SplitMethodSite::AssignValue(pos)) => {
            let AstExpr::Call(c) = std::mem::replace(&mut a.values[pos], AstExpr::Nil) else {
                unreachable!()
            };
            a.values[pos] = AstExpr::MethodCall(Box::new(build_method(*c)));
        }
        _ => unreachable!(),
    }
    true
}

/// 将相邻的纯/无副作用单用匿名临时赋值（常由三元 `if` 折叠为 `cond and a or b` 遗留）
/// 安全前向内联进下一条语句，并级联收回外层被冲刷的 `callee`/算术/拼接准备。
fn try_inline_single_use_pure_temp(
    stmts: &mut Vec<AstStmt>,
    idx: usize,
    target: AstTargetDialect,
    is_function_root: bool,
    captured: &BTreeSet<AstNameRef>,
    debug_hinted: &BTreeSet<AstNameRef>,
) -> bool {
    let (is_local_decl, binding_opt, local_binding_ref, name, rhs) = match &stmts[idx] {
        AstStmt::LocalDecl(d)
            if d.bindings.len() == 1
                && d.values.len() == 1
                && d.bindings[0].attr == AstLocalAttr::None
                && !d.bindings[0].is_debug_hinted =>
        {
            (
                true,
                Some(d.bindings[0].clone()),
                d.bindings[0].id,
                d.bindings[0].id.to_name_ref(),
                &d.values[0],
            )
        }
        AstStmt::Assign(a)
            if a.compound_op.is_none()
                && a.targets.len() == 1
                && a.values.len() == 1
                && matches!(&a.targets[0], AstLValue::Name(AstNameRef::Local(_))) =>
        {
            let AstLValue::Name(n @ AstNameRef::Local(l)) = &a.targets[0] else {
                unreachable!()
            };
            (false, None, AstBindingRef::Local(*l), n.clone(), &a.values[0])
        }
        _ => return false,
    };

    let is_pure_rhs = expr_is_pure_inlineable(rhs);
    // 也允许将单值短路逻辑表达（如 `call() and fallback`）或纯基址表字段/下标读取（如 `x.y`、`t[k]`）
    // 直接内联进紧随下一条语句的首个无前序副作用求值位置（恢复 `self:send(x.y, a or b)` 等调用链），
    // 严格保住求值顺序与单值语义。
    let is_first_effect_logical = !is_pure_rhs && expr_is_first_effect_inlineable(rhs);
    if captured.contains(&name)
        || debug_hinted.contains(&name)
        || expr_mentions_name_ref(rhs, &name)
        || (!is_pure_rhs && !is_first_effect_logical)
    {
        return false;
    }

    // Lua 5.2/5.3/5.4/5.5 的 `SETTABUP` 会把表基址上值读取延后到键与右值求值之后；
    // 若把 `local t = upval; t[k] = f()` 错内联为 `upval[k] = f()`，且 f() 会改写 upval，将破坏快照语义！
    // Lua 5.1 / LuaJIT / Luau 无 `SETTABUP` 指令，`upval[k] = expr` 始终先快照 `upval` 再求值键与右值。
    if matches!(
        target.version,
        crate::decompile::DecompileDialect::Lua52
            | crate::decompile::DecompileDialect::Lua53
            | crate::decompile::DecompileDialect::Lua54
            | crate::decompile::DecompileDialect::Lua55
    ) && matches!(
        rhs,
        AstExpr::Var(AstNameRef::Upvalue(_) | AstNameRef::Global(_))
    ) && let AstStmt::Assign(a) = &stmts[idx + 1]
        && a.targets.iter().any(|t| match t {
            AstLValue::FieldAccess(f) => expr_mentions_name_ref(&f.base, &name),
            AstLValue::IndexAccess(ia) => expr_mentions_name_ref(&ia.base, &name),
            AstLValue::Name(_) => false,
        })
    {
        return false;
    }

    // 保守保留表构造器前的显式字面量局部声明（如 `local key = "x"; local t = { [key] = 1 }`）
    if is_local_decl
        && matches!(
            rhs,
            AstExpr::Nil
                | AstExpr::Boolean(_)
                | AstExpr::Integer(_)
                | AstExpr::Number(_)
                | AstExpr::String(_)
        )
        && matches!(
            &stmts[idx + 1],
            AstStmt::LocalDecl(d) if d.values.iter().any(|v| matches!(v, AstExpr::TableConstructor(_)))
        )
    {
        return false;
    }

    let overwrites_self = matches!(
        &stmts[idx + 1],
        AstStmt::Assign(a)
            if a.compound_op.is_none()
                && a.targets.len() == 1
                && matches!(&a.targets[0], AstLValue::Name(n) if n == &name)
    );
    if !overwrites_self {
        // 目标语句若把 name 放在多赋值或复合赋值左值上则放弃
        if let AstStmt::Assign(a) = &stmts[idx + 1]
            && a.targets
                .iter()
                .any(|t| matches!(t, AstLValue::Name(n) if n == &name))
        {
            return false;
        }
    }

    // 先以 O(1) 单语句扫描确认 `stmts[idx + 1]` 恰好单次安全读取 `name`，
    // 命中后再扫描 `stmts[idx + 2..]` 检查死活，消除大块平铺语句上的 O(N²) 退化！
    let mut scan = SingleUseScan {
        target: &name,
        captured,
        treat_mutable_var_as_effect: is_first_effect_logical,
        found: 0,
        invalid: false,
        seen_effect: false,
        effect_before_use: false,
    };
    scan_stmt_for_single_use(&stmts[idx + 1], &mut scan);
    if scan.invalid || scan.found != 1 {
        return false;
    }
    if (is_first_effect_logical || expr_reads_mutable_external_var(rhs, captured))
        && scan.effect_before_use
    {
        return false;
    }

    if !overwrites_self {
        if is_local_decl {
            if stmts[idx + 2..]
                .iter()
                .any(|s| stmt_mentions_name_ref(s, &name))
            {
                return false;
            }
        } else {
            let allow_exit_dead =
                is_function_root || block_declares_binding_before(stmts, idx, local_binding_ref);
            if !is_dead_before_overwrite(&stmts[idx + 2..], &name, allow_exit_dead) {
                return false;
            }
        }
    }

    // 确认满足所有语义与求值顺序护栏：执行单点替换并移除前导临时赋值
    let rhs_expr = match stmts.remove(idx) {
        AstStmt::LocalDecl(mut d) => d.values.pop().unwrap(),
        AstStmt::Assign(mut a) => a.values.pop().unwrap(),
        _ => unreachable!(),
    };
    let mut replacement = Some(rhs_expr);
    let replaced = replace_single_use_in_stmt(&mut stmts[idx], &name, &mut replacement);
    debug_assert!(replaced && replacement.is_none());

    // 若删掉的是 `local t = ...` 且后继语句就地覆写了 `t = ...`，须将后继升级为 `local t = ...` 以保留局部声明！
    if is_local_decl && overwrites_self {
        let AstStmt::Assign(mut a) = std::mem::replace(&mut stmts[idx], AstStmt::Break) else {
            unreachable!()
        };
        stmts[idx] = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![binding_opt.unwrap()],
            values: std::mem::take(&mut a.values),
        }));
    }
    true
}

fn expr_is_pure_inlineable(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Var(_) => true,
        AstExpr::Unary(u) if u.op == AstUnaryOpKind::Not => expr_is_pure_inlineable(&u.expr),
        AstExpr::LogicalAnd(l) | AstExpr::LogicalOr(l) => {
            expr_is_pure_inlineable(&l.lhs) && expr_is_pure_inlineable(&l.rhs)
        }
        AstExpr::IfExpr(ie) => {
            expr_is_pure_inlineable(&ie.cond)
                && expr_is_pure_inlineable(&ie.then_expr)
                && expr_is_pure_inlineable(&ie.else_expr)
        }
        AstExpr::Binary(b) => match b.op {
            super::common::AstBinaryOpKind::Add
            | super::common::AstBinaryOpKind::Sub
            | super::common::AstBinaryOpKind::Mul
            | super::common::AstBinaryOpKind::Div
            | super::common::AstBinaryOpKind::FloorDiv
            | super::common::AstBinaryOpKind::Mod => {
                expr_is_guaranteed_number(&b.lhs) && expr_is_guaranteed_number(&b.rhs)
            }
            super::common::AstBinaryOpKind::Concat => {
                expr_is_guaranteed_string(&b.lhs) && expr_is_guaranteed_string(&b.rhs)
            }
            // 至少一侧为原始字面量的 `==` 永不触发 `__eq` 元方法，严格纯且可安全内联（如 `a == 110 and b == 11`）
            super::common::AstBinaryOpKind::Eq => {
                (is_primitive_literal(&b.lhs) || is_primitive_literal(&b.rhs))
                    && expr_is_pure_inlineable(&b.lhs)
                    && expr_is_pure_inlineable(&b.rhs)
            }
            _ => false,
        },
        _ => false,
    }
}

fn expr_is_guaranteed_number(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Integer(_) | AstExpr::Number(_) => true,
        AstExpr::LogicalOr(l) => {
            let lhs_num = expr_is_guaranteed_number(&l.lhs)
                || matches!(&l.lhs, AstExpr::LogicalAnd(a) if expr_is_pure_inlineable(&a.lhs) && expr_is_guaranteed_number(&a.rhs));
            lhs_num && expr_is_guaranteed_number(&l.rhs)
        }
        AstExpr::Binary(b)
            if matches!(
                b.op,
                super::common::AstBinaryOpKind::Add
                    | super::common::AstBinaryOpKind::Sub
                    | super::common::AstBinaryOpKind::Mul
                    | super::common::AstBinaryOpKind::Div
                    | super::common::AstBinaryOpKind::FloorDiv
                    | super::common::AstBinaryOpKind::Mod
            ) =>
        {
            expr_is_guaranteed_number(&b.lhs) && expr_is_guaranteed_number(&b.rhs)
        }
        _ => false,
    }
}

fn expr_is_guaranteed_string(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::String(_) => true,
        AstExpr::LogicalOr(l) => {
            let lhs_str = expr_is_guaranteed_string(&l.lhs)
                || matches!(&l.lhs, AstExpr::LogicalAnd(a) if expr_is_pure_inlineable(&a.lhs) && expr_is_guaranteed_string(&a.rhs));
            lhs_str && expr_is_guaranteed_string(&l.rhs)
        }
        AstExpr::Binary(b) if b.op == super::common::AstBinaryOpKind::Concat => {
            expr_is_guaranteed_string(&b.lhs) && expr_is_guaranteed_string(&b.rhs)
        }
        _ => false,
    }
}

/// 检查表达式是否读取了可能被前序调用/全局 `__index` 改写的外部/被捕获变量
/// （非捕获的当前帧 `Local`/`Param` 不可能被任何外部调用或元方法改写，跨过 `assert` 等全局读取安全）。
fn expr_reads_mutable_external_var(expr: &AstExpr, captured: &BTreeSet<AstNameRef>) -> bool {
    for node in expr_nodes(expr) {
        if let ExprNode::Expr(AstExpr::Var(v)) = node
            && (matches!(
                v,
                AstNameRef::Global(_) | AstNameRef::Upvalue(_) | AstNameRef::Environment
            ) || captured.contains(v))
        {
            return true;
        }
    }
    false
}

fn expr_is_first_effect_inlineable(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::LogicalAnd(_) | AstExpr::LogicalOr(_) => true,
        AstExpr::FieldAccess(f) => expr_is_pure_inlineable(&f.base),
        AstExpr::IndexAccess(ia) => {
            expr_is_pure_inlineable(&ia.base) && expr_is_pure_inlineable(&ia.index)
        }
        _ => false,
    }
}

fn try_fold_repeat_tail_cond_local(
    r: &mut super::common::AstRepeat,
    captured: &BTreeSet<AstNameRef>,
    debug_hinted: &BTreeSet<AstNameRef>,
) -> bool {
    let Some(AstStmt::LocalDecl(decl)) = r.body.stmts.last() else {
        return false;
    };
    if decl.bindings.len() != 1
        || decl.values.len() != 1
        || decl.bindings[0].attr != AstLocalAttr::None
        || decl.bindings[0].is_debug_hinted
    {
        return false;
    }
    let name = decl.bindings[0].id.to_name_ref();
    let rhs = &decl.values[0];
    if captured.contains(&name)
        || debug_hinted.contains(&name)
        || expr_mentions_name_ref(rhs, &name)
    {
        return false;
    }
    let mut scan = SingleUseScan {
        target: &name,
        captured,
        treat_mutable_var_as_effect: !expr_is_pure_inlineable(rhs),
        found: 0,
        invalid: false,
        seen_effect: false,
        effect_before_use: false,
    };
    scan_expr_for_single_use(&r.cond, &mut scan);
    if scan.invalid || scan.found != 1 || scan.effect_before_use {
        return false;
    }
    let Some(AstStmt::LocalDecl(mut taken)) = r.body.stmts.pop() else {
        unreachable!()
    };
    let mut replacement = Some(taken.values.pop().unwrap());
    let replaced = replace_single_use_in_expr(&mut r.cond, &name, &mut replacement);
    debug_assert!(replaced && replacement.is_none());
    true
}

struct SingleUseScan<'a> {
    target: &'a AstNameRef,
    captured: &'a BTreeSet<AstNameRef>,
    treat_mutable_var_as_effect: bool,
    found: usize,
    invalid: bool,
    seen_effect: bool,
    effect_before_use: bool,
}

fn scan_stmt_for_single_use(stmt: &AstStmt, scan: &mut SingleUseScan<'_>) {
    match stmt {
        AstStmt::Assign(a) if a.compound_op.is_none() => {
            // 单目标表写 `t[k] = v` 的 `SETTABLE`（`__newindex`）发生在 `v` 求值之后，
            // `t` 与 `k` 自身的纯局部/形参读取不产生前序副作用（若含上值/全局/调用则由 `scan_expr_for_single_use` 标记）。
            let multi_target = a.targets.len() > 1;
            for t in &a.targets {
                match t {
                    AstLValue::Name(_) => {}
                    AstLValue::FieldAccess(f) => {
                        scan_expr_for_single_use(&f.base, scan);
                        if multi_target {
                            scan.seen_effect = true;
                        }
                    }
                    AstLValue::IndexAccess(ia) => {
                        scan_expr_for_single_use(&ia.base, scan);
                        scan_expr_for_single_use(&ia.index, scan);
                        if multi_target {
                            scan.seen_effect = true;
                        }
                    }
                }
            }
            for v in &a.values {
                scan_expr_for_single_use(v, scan);
            }
        }
        AstStmt::LocalDecl(d) => {
            for v in &d.values {
                scan_expr_for_single_use(v, scan);
            }
        }
        AstStmt::CallStmt(c) => match &c.call {
            super::common::AstCallKind::Call(call) => {
                scan_expr_for_single_use(&call.callee, scan);
                for a in &call.args {
                    scan_expr_for_single_use(a, scan);
                }
                scan.seen_effect = true;
            }
            super::common::AstCallKind::MethodCall(m) => {
                scan_expr_for_single_use(&m.receiver, scan);
                for a in &m.args {
                    scan_expr_for_single_use(a, scan);
                }
                scan.seen_effect = true;
            }
        },
        AstStmt::Return(r) => {
            for v in &r.values {
                scan_expr_for_single_use(v, scan);
            }
        }
        AstStmt::If(i) => {
            scan_expr_for_single_use(&i.cond, scan);
            if i.then_block
                .stmts
                .iter()
                .any(|s| stmt_mentions_name_ref(s, scan.target))
                || i.else_block.as_ref().is_some_and(|eb| {
                    eb.stmts
                        .iter()
                        .any(|s| stmt_mentions_name_ref(s, scan.target))
                })
            {
                scan.invalid = true;
            }
        }
        _ => {
            scan.invalid = true;
        }
    }
}

fn scan_expr_for_single_use(expr: &AstExpr, scan: &mut SingleUseScan<'_>) {
    if scan.invalid {
        return;
    }
    match expr {
        AstExpr::Var(n) if n == scan.target => {
            scan.found += 1;
            if scan.found == 1 {
                scan.effect_before_use = scan.seen_effect;
            } else {
                scan.invalid = true;
            }
        }
        AstExpr::Var(AstNameRef::Global(_)) => {
            // 全局变量读取可能触发 `_G`/`_ENV` 的 `__index` 元方法，视为可见副作用，禁止跨过它重排求值！
            scan.seen_effect = true;
        }
        AstExpr::Var(v) => {
            if scan.treat_mutable_var_as_effect
                && (matches!(v, AstNameRef::Upvalue(_)) || scan.captured.contains(v))
            {
                scan.seen_effect = true;
            }
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::VarArg
        | AstExpr::Error(_) => {}
        AstExpr::Unary(u) => {
            scan_expr_for_single_use(&u.expr, scan);
            if u.op != AstUnaryOpKind::Not {
                scan.seen_effect = true;
            }
        }
        AstExpr::Binary(b) => {
            scan_expr_for_single_use(&b.lhs, scan);
            scan_expr_for_single_use(&b.rhs, scan);
            if !expr_is_pure_inlineable(expr) {
                scan.seen_effect = true;
            }
        }
        AstExpr::LogicalAnd(l) | AstExpr::LogicalOr(l) => {
            scan_expr_for_single_use(&l.lhs, scan);
            if expr_mentions_name_ref(&l.rhs, scan.target) {
                scan.invalid = true;
                return;
            }
            if !expr_is_pure_inlineable(&l.rhs) {
                scan.seen_effect = true;
            }
        }
        AstExpr::FieldAccess(f) => {
            scan_expr_for_single_use(&f.base, scan);
            scan.seen_effect = true;
        }
        AstExpr::IndexAccess(ia) => {
            scan_expr_for_single_use(&ia.base, scan);
            scan_expr_for_single_use(&ia.index, scan);
            scan.seen_effect = true;
        }
        AstExpr::Call(c) => {
            scan_expr_for_single_use(&c.callee, scan);
            for a in &c.args {
                scan_expr_for_single_use(a, scan);
            }
            scan.seen_effect = true;
        }
        AstExpr::MethodCall(m) => {
            scan_expr_for_single_use(&m.receiver, scan);
            for a in &m.args {
                scan_expr_for_single_use(a, scan);
            }
            scan.seen_effect = true;
        }
        AstExpr::SingleValue(inner) => {
            scan_expr_for_single_use(inner, scan);
        }
        AstExpr::TableConstructor(_)
        | AstExpr::FunctionExpr(_)
        | AstExpr::Vector(_)
        | AstExpr::IfExpr(_) => {
            if expr_mentions_name_ref(expr, scan.target) {
                scan.invalid = true;
            } else {
                scan.seen_effect = true;
            }
        }
    }
}

fn replace_single_use_in_stmt(
    stmt: &mut AstStmt,
    target: &AstNameRef,
    replacement: &mut Option<AstExpr>,
) -> bool {
    match stmt {
        AstStmt::Assign(a) => {
            for t in &mut a.targets {
                match t {
                    AstLValue::Name(_) => {}
                    AstLValue::FieldAccess(f) => {
                        if replace_single_use_in_expr(&mut f.base, target, replacement) {
                            return true;
                        }
                    }
                    AstLValue::IndexAccess(ia) => {
                        if replace_single_use_in_expr(&mut ia.base, target, replacement)
                            || replace_single_use_in_expr(&mut ia.index, target, replacement)
                        {
                            return true;
                        }
                    }
                }
            }
            for v in &mut a.values {
                if replace_single_use_in_expr(v, target, replacement) {
                    return true;
                }
            }
            false
        }
        AstStmt::LocalDecl(d) => {
            for v in &mut d.values {
                if replace_single_use_in_expr(v, target, replacement) {
                    return true;
                }
            }
            false
        }
        AstStmt::CallStmt(c) => match &mut c.call {
            super::common::AstCallKind::Call(call) => {
                if replace_single_use_in_expr(&mut call.callee, target, replacement) {
                    return true;
                }
                for a in &mut call.args {
                    if replace_single_use_in_expr(a, target, replacement) {
                        return true;
                    }
                }
                false
            }
            super::common::AstCallKind::MethodCall(m) => {
                if replace_single_use_in_expr(&mut m.receiver, target, replacement) {
                    return true;
                }
                for a in &mut m.args {
                    if replace_single_use_in_expr(a, target, replacement) {
                        return true;
                    }
                }
                false
            }
        },
        AstStmt::Return(r) => {
            for v in &mut r.values {
                if replace_single_use_in_expr(v, target, replacement) {
                    return true;
                }
            }
            false
        }
        AstStmt::If(i) => replace_single_use_in_expr(&mut i.cond, target, replacement),
        _ => false,
    }
}

fn replace_single_use_in_expr(
    expr: &mut AstExpr,
    target: &AstNameRef,
    replacement: &mut Option<AstExpr>,
) -> bool {
    if matches!(expr, AstExpr::Var(n) if n == target) {
        if let Some(rep) = replacement.take() {
            *expr = rep;
            return true;
        }
        return false;
    }
    match expr {
        AstExpr::Unary(u) => replace_single_use_in_expr(&mut u.expr, target, replacement),
        AstExpr::Binary(b) => {
            replace_single_use_in_expr(&mut b.lhs, target, replacement)
                || replace_single_use_in_expr(&mut b.rhs, target, replacement)
        }
        AstExpr::LogicalAnd(l) | AstExpr::LogicalOr(l) => {
            replace_single_use_in_expr(&mut l.lhs, target, replacement)
        }
        AstExpr::FieldAccess(f) => replace_single_use_in_expr(&mut f.base, target, replacement),
        AstExpr::IndexAccess(ia) => {
            replace_single_use_in_expr(&mut ia.base, target, replacement)
                || replace_single_use_in_expr(&mut ia.index, target, replacement)
        }
        AstExpr::Call(c) => {
            if replace_single_use_in_expr(&mut c.callee, target, replacement) {
                return true;
            }
            for a in &mut c.args {
                if replace_single_use_in_expr(a, target, replacement) {
                    return true;
                }
            }
            false
        }
        AstExpr::MethodCall(m) => {
            if replace_single_use_in_expr(&mut m.receiver, target, replacement) {
                return true;
            }
            for a in &mut m.args {
                if replace_single_use_in_expr(a, target, replacement) {
                    return true;
                }
            }
            false
        }
        AstExpr::SingleValue(inner) => replace_single_use_in_expr(inner, target, replacement),
        _ => false,
    }
}

/// 折叠经典 Lua 短路赋值对：
/// - `local x = a; if not x then x = b end` → `local x = a or b`
/// - `local x = a; if x then x = b end`     → `local x = a and b`
/// - `x = a; if not x then x = b end`       → `x = a or b`
/// - `x = a; if x then x = b end`           → `x = a and b`
fn try_fold_short_circuit_value_pair(
    stmts: &mut Vec<AstStmt>,
    idx: usize,
    captured: &BTreeSet<AstNameRef>,
) -> bool {
    let AstStmt::If(if_stmt) = &stmts[idx + 1] else {
        return false;
    };
    if if_stmt.else_block.is_some() || if_stmt.then_block.stmts.len() != 1 {
        return false;
    }
    let AstStmt::Assign(then_assign) = &if_stmt.then_block.stmts[0] else {
        return false;
    };
    if then_assign.compound_op.is_some()
        || then_assign.targets.len() != 1
        || then_assign.values.len() != 1
    {
        return false;
    }
    let AstLValue::Name(target_name) = &then_assign.targets[0] else {
        return false;
    };
    // 全局变量的写入/回读可触发 `_G` 的 `__newindex`/`__index` 元方法，绝不可折叠为单次短路写入！
    if matches!(target_name, AstNameRef::Global(_) | AstNameRef::Environment) {
        return false;
    }

    // 检查条件是 `x`（and）还是 `not x`（or）
    let is_or = match &if_stmt.cond {
        AstExpr::Var(n) if n == target_name => false,
        AstExpr::Unary(u)
            if u.op == AstUnaryOpKind::Not
                && matches!(&u.expr, AstExpr::Var(n) if n == target_name) =>
        {
            true
        }
        _ => return false,
    };

    // 右侧表达式不能引用尚未完成赋值的 target_name；
    // 若 target_name 为上值或被子闭包按引用捕获且 rhs 含调用/元方法，写回必须先于 rhs 求值，禁止合并！
    if expr_mentions_name_ref(&then_assign.values[0], target_name)
        || ((matches!(target_name, AstNameRef::Upvalue(_)) || captured.contains(target_name))
            && expr_may_invoke_closure(&then_assign.values[0]))
    {
        return false;
    }

    let first_matches = match &stmts[idx] {
        AstStmt::LocalDecl(decl) => {
            decl.bindings.len() == 1
                && decl.bindings[0].attr == AstLocalAttr::None
                && decl.values.len() == 1
                && decl.bindings[0].id.matches_name_ref(target_name)
        }
        AstStmt::Assign(assign) => {
            assign.compound_op.is_none()
                && assign.targets.len() == 1
                && assign.values.len() == 1
                && assign.targets[0] == AstLValue::Name(target_name.clone())
        }
        _ => false,
    };
    if !first_matches {
        return false;
    }

    let AstStmt::If(mut taken_if) = stmts.remove(idx + 1) else {
        unreachable!()
    };
    let AstStmt::Assign(mut taken_then) = taken_if.then_block.stmts.pop().unwrap() else {
        unreachable!()
    };
    let rhs = taken_then.values.pop().unwrap();

    let combine = |lhs: AstExpr, rhs: AstExpr| {
        if is_or {
            AstExpr::LogicalOr(Box::new(AstLogicalExpr { lhs, rhs }))
        } else {
            AstExpr::LogicalAnd(Box::new(AstLogicalExpr { lhs, rhs }))
        }
    };

    match &mut stmts[idx] {
        AstStmt::LocalDecl(decl) => {
            let lhs = decl.values.pop().unwrap();
            decl.values.push(combine(lhs, rhs));
        }
        AstStmt::Assign(assign) => {
            let lhs = assign.values.pop().unwrap();
            assign.values.push(combine(lhs, rhs));
        }
        _ => unreachable!(),
    }
    true
}

fn is_primitive_literal(expr: &AstExpr) -> bool {
    matches!(
        expr,
        AstExpr::Nil
            | AstExpr::Boolean(_)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_)
    )
}

fn is_luau_fresh_const_capture_guard(if_stmt: &super::common::AstIf) -> bool {
    matches!(if_stmt.cond, AstExpr::Boolean(false))
        && if_stmt.else_block.is_none()
        && if_stmt.then_block.stmts.len() == 1
        && matches!(
            &if_stmt.then_block.stmts[0],
            AstStmt::Assign(a)
                if a.compound_op.is_none()
                    && a.targets.len() == 1
                    && a.values.len() == 1
                    && matches!(&a.targets[0], AstLValue::Name(AstNameRef::Local(_)))
                    && matches!(a.values[0], AstExpr::Nil)
        )
}

fn block_contains_any_label(block: &AstBlock) -> bool {
    block.stmts.iter().any(|s| match s {
        AstStmt::Label(_) => true,
        AstStmt::DoBlock(b) => block_contains_any_label(b),
        AstStmt::If(i) => {
            block_contains_any_label(&i.then_block)
                || i.else_block.as_ref().is_some_and(block_contains_any_label)
        }
        AstStmt::While(w) => block_contains_any_label(&w.body),
        AstStmt::Repeat(r) => block_contains_any_label(&r.body),
        AstStmt::NumericFor(nf) => block_contains_any_label(&nf.body),
        AstStmt::GenericFor(gf) => block_contains_any_label(&gf.body),
        _ => false,
    })
}

fn expr_is_guaranteed_boolean(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Boolean(_) => true,
        AstExpr::Unary(u) if u.op == AstUnaryOpKind::Not => true,
        AstExpr::Binary(b)
            if matches!(
                b.op,
                super::common::AstBinaryOpKind::Eq
                    | super::common::AstBinaryOpKind::Lt
                    | super::common::AstBinaryOpKind::Le
                    | super::common::AstBinaryOpKind::Gt
                    | super::common::AstBinaryOpKind::Ge
            ) =>
        {
            true
        }
        AstExpr::LogicalAnd(l) | AstExpr::LogicalOr(l) => {
            expr_is_guaranteed_boolean(&l.lhs) && expr_is_guaranteed_boolean(&l.rhs)
        }
        _ => false,
    }
}

/// 折叠 Luau 布尔预置短路赋值：`[local] r = false; if A then r = B end` → `[local] r = A and B`。
/// 严格要求 `A` 为保证布尔值（避免 `A == nil` 时返回 `nil` 而非 `false`）且 `B` 不引用 `r`。
fn try_fold_bool_init_and_pair(
    stmts: &mut Vec<AstStmt>,
    idx: usize,
    captured: &BTreeSet<AstNameRef>,
) -> bool {
    let AstStmt::If(if_stmt) = &stmts[idx + 1] else {
        return false;
    };
    if if_stmt.else_block.is_some()
        || if_stmt.then_block.stmts.len() != 1
        || !expr_is_guaranteed_boolean(&if_stmt.cond)
    {
        return false;
    }
    let AstStmt::Assign(then_assign) = &if_stmt.then_block.stmts[0] else {
        return false;
    };
    if then_assign.compound_op.is_some()
        || then_assign.targets.len() != 1
        || then_assign.values.len() != 1
    {
        return false;
    }
    let AstLValue::Name(target_name) = &then_assign.targets[0] else {
        return false;
    };
    if matches!(target_name, AstNameRef::Global(_) | AstNameRef::Environment) {
        return false;
    }
    let observable_to_closure =
        matches!(target_name, AstNameRef::Upvalue(_)) || captured.contains(target_name);
    if expr_mentions_name_ref(&if_stmt.cond, target_name)
        || expr_mentions_name_ref(&then_assign.values[0], target_name)
        || (observable_to_closure
            && (expr_may_invoke_closure(&if_stmt.cond)
                || expr_may_invoke_closure(&then_assign.values[0])))
    {
        return false;
    }
    let first_is_false_init = match &stmts[idx] {
        AstStmt::LocalDecl(decl) => {
            decl.bindings.len() == 1
                && decl.bindings[0].attr == AstLocalAttr::None
                && decl.values.len() == 1
                && matches!(decl.values[0], AstExpr::Boolean(false))
                && decl.bindings[0].id.matches_name_ref(target_name)
        }
        AstStmt::Assign(assign) => {
            assign.compound_op.is_none()
                && assign.targets.len() == 1
                && assign.values.len() == 1
                && matches!(assign.values[0], AstExpr::Boolean(false))
                && assign.targets[0] == AstLValue::Name(target_name.clone())
        }
        _ => false,
    };
    if !first_is_false_init {
        return false;
    }
    let AstStmt::If(mut taken_if) = stmts.remove(idx + 1) else {
        unreachable!()
    };
    let AstStmt::Assign(mut taken_then) = taken_if.then_block.stmts.pop().unwrap() else {
        unreachable!()
    };
    let rhs = taken_then.values.pop().unwrap();
    let combined = AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
        lhs: taken_if.cond,
        rhs,
    }));
    match &mut stmts[idx] {
        AstStmt::LocalDecl(decl) => {
            decl.values[0] = combined;
        }
        AstStmt::Assign(assign) => {
            assign.values[0] = combined;
        }
        _ => unreachable!(),
    }
    true
}

/// 折叠纯真值字面量短路桥接：
/// `local t = "one"; x = t or "two"`（`t` 为本块末用、非捕获、非 debug 局部）→ `x = "one"`。
/// 随后外层 `if cond then x = "one" else x = "two" end` 可自然折叠为 `x = cond and "one" or "two"`。
fn try_fold_const_truthy_or_pair(
    stmts: &mut Vec<AstStmt>,
    idx: usize,
    captured: &BTreeSet<AstNameRef>,
) -> bool {
    // 也支持外层已声明的临时赋值：`t = <truthy_lit>; dst = t or ...` → `t = <truthy_lit>; dst = <truthy_lit>`
    // （不删除 `t = <truthy_lit>`，交由外层 `prune_unused_empty_local_decls` 在确认零读后统一清理）
    if let AstStmt::Assign(prev_assign) = &stmts[idx]
        && prev_assign.compound_op.is_none()
        && prev_assign.targets.len() == 1
        && prev_assign.values.len() == 1
        && let AstLValue::Name(temp_name @ AstNameRef::Local(_)) = &prev_assign.targets[0]
        && !captured.contains(temp_name)
        && prev_assign.values[0].is_guaranteed_truthy()
        && !expr_may_invoke_closure(&prev_assign.values[0])
        && let AstStmt::Assign(next_assign) = &stmts[idx + 1]
        && next_assign.compound_op.is_none()
        && next_assign.targets.len() == 1
        && next_assign.values.len() == 1
        && matches!(&next_assign.values[0], AstExpr::LogicalOr(or) if or.lhs == AstExpr::Var(temp_name.clone()))
    {
        // 对纯原始字面量可克隆值协助外层三元折叠；
        // 对表/闭包构造器绝不可克隆（会破坏 `t == OUT` 对象身份），改为等价的 `dst = t`！
        let replacement = if is_primitive_literal(&prev_assign.values[0]) {
            prev_assign.values[0].clone()
        } else {
            AstExpr::Var(temp_name.clone())
        };
        if let AstStmt::Assign(next_assign) = &mut stmts[idx + 1] {
            next_assign.values[0] = replacement;
        }
        return true;
    }

    let AstStmt::LocalDecl(decl) = &stmts[idx] else {
        return false;
    };
    if decl.bindings.len() != 1
        || decl.bindings[0].attr != AstLocalAttr::None
        || decl.bindings[0].is_debug_hinted
        || decl.values.len() != 1
    {
        return false;
    }
    let lit = &decl.values[0];
    if !lit.is_guaranteed_truthy() || expr_may_invoke_closure(lit) {
        return false;
    }
    let temp_name = decl.bindings[0].id.to_name_ref();
    if captured.contains(&temp_name) {
        return false;
    }
    // 确认本块后续语句不再提及该临时局部
    if stmts[idx + 2..]
        .iter()
        .any(|s| stmt_mentions_name_ref(s, &temp_name))
    {
        return false;
    }
    // 情形 A：`local t = <truthy_lit>; x = t or ...` → `x = <truthy_lit>`
    if let AstStmt::Assign(assign) = &stmts[idx + 1]
        && assign.compound_op.is_none()
        && assign.targets.len() == 1
        && assign.values.len() == 1
        && matches!(&assign.values[0], AstExpr::LogicalOr(or) if or.lhs == AstExpr::Var(temp_name.clone()))
    {
        let AstStmt::LocalDecl(mut taken_decl) = stmts.remove(idx) else {
            unreachable!()
        };
        let lit_val = taken_decl.values.pop().unwrap();
        if let AstStmt::Assign(assign) = &mut stmts[idx] {
            assign.values[0] = lit_val;
        }
        return true;
    }
    // 情形 B：`local t = <truthy_lit>; if t then dst = t else <dead> end` → `dst = <truthy_lit>`
    // （Lua 5.1/5.2/5.3 编译 `c1 and "yes" or c2 and "maybe" or "no"` 时对恒真字面量 `"yes"` 仍生成 `TEST + JMP`，
    //  else 臂在语义上永不可达；直接剥除死分支可使嵌套三元在首轮即收敛为人类源码！）
    if let AstStmt::If(if_stmt) = &stmts[idx + 1]
        && if_stmt.cond == AstExpr::Var(temp_name.clone())
        && if_stmt.then_block.stmts.len() == 1
        && let AstStmt::Assign(then_assign) = &if_stmt.then_block.stmts[0]
        && then_assign.compound_op.is_none()
        && then_assign.targets.len() == 1
        && then_assign.values.len() == 1
        && then_assign.values[0] == AstExpr::Var(temp_name.clone())
        && !then_assign.targets.iter().any(|t| match t {
            AstLValue::Name(n) => n == &temp_name,
            AstLValue::FieldAccess(f) => expr_mentions_name_ref(&f.base, &temp_name),
            AstLValue::IndexAccess(ia) => {
                expr_mentions_name_ref(&ia.base, &temp_name)
                    || expr_mentions_name_ref(&ia.index, &temp_name)
            }
        })
    {
        let AstStmt::LocalDecl(mut taken_decl) = stmts.remove(idx) else {
            unreachable!()
        };
        let lit_val = taken_decl.values.pop().unwrap();
        let AstStmt::If(mut taken_if) = stmts.remove(idx) else {
            unreachable!()
        };
        let AstStmt::Assign(mut then_assign) = taken_if.then_block.stmts.pop().unwrap() else {
            unreachable!()
        };
        then_assign.values[0] = lit_val;
        stmts.insert(idx, AstStmt::Assign(then_assign));
        return true;
    }
    false
}

fn stmt_mentions_name_ref(stmt: &AstStmt, target: &AstNameRef) -> bool {
    use super::traverse::traverse_lvalue_children;
    match stmt {
        AstStmt::LocalDecl(d) => d.values.iter().any(|v| expr_mentions_name_ref(v, target)),
        AstStmt::GlobalDecl(d) => d.values.iter().any(|v| expr_mentions_name_ref(v, target)),
        AstStmt::Assign(a) => {
            a.targets.iter().any(|t| {
                let mut found = matches!(t, AstLValue::Name(n) if n == target);
                traverse_lvalue_children!(t, borrow = [&], expr(e) => {
                    if expr_mentions_name_ref(e, target) {
                        found = true;
                    }
                });
                found
            }) || a.values.iter().any(|v| expr_mentions_name_ref(v, target))
        }
        AstStmt::CallStmt(c) => match &c.call {
            super::common::AstCallKind::Call(call) => {
                expr_mentions_name_ref(&call.callee, target)
                    || call.args.iter().any(|a| expr_mentions_name_ref(a, target))
            }
            super::common::AstCallKind::MethodCall(m) => {
                expr_mentions_name_ref(&m.receiver, target)
                    || m.args.iter().any(|a| expr_mentions_name_ref(a, target))
            }
        },
        AstStmt::Return(r) => r.values.iter().any(|v| expr_mentions_name_ref(v, target)),
        AstStmt::If(i) => {
            expr_mentions_name_ref(&i.cond, target)
                || i.then_block.stmts.iter().any(|s| stmt_mentions_name_ref(s, target))
                || i.else_block
                    .as_ref()
                    .is_some_and(|eb| eb.stmts.iter().any(|s| stmt_mentions_name_ref(s, target)))
        }
        AstStmt::While(w) => {
            expr_mentions_name_ref(&w.cond, target)
                || w.body.stmts.iter().any(|s| stmt_mentions_name_ref(s, target))
        }
        AstStmt::Repeat(r) => {
            r.body.stmts.iter().any(|s| stmt_mentions_name_ref(s, target))
                || expr_mentions_name_ref(&r.cond, target)
        }
        AstStmt::NumericFor(nf) => {
            expr_mentions_name_ref(&nf.start, target)
                || expr_mentions_name_ref(&nf.limit, target)
                || expr_mentions_name_ref(&nf.step, target)
                || nf.body.stmts.iter().any(|s| stmt_mentions_name_ref(s, target))
        }
        AstStmt::GenericFor(gf) => {
            gf.iterator.iter().any(|e| expr_mentions_name_ref(e, target))
                || gf.body.stmts.iter().any(|s| stmt_mentions_name_ref(s, target))
        }
        AstStmt::DoBlock(b) => b.stmts.iter().any(|s| stmt_mentions_name_ref(s, target)),
        AstStmt::FunctionDecl(d) => {
            let root = match &d.target {
                AstFunctionName::Plain(p) | AstFunctionName::Method(p, _) => &p.root,
            };
            root == target
                || AstBindingRef::from_name_ref(target)
                    .is_some_and(|b| d.func.captured_bindings.contains(&b))
                || matches!(target, AstNameRef::Param(p) if d.func.captured_params.contains(p))
        }
        AstStmt::LocalFunctionDecl(d) => {
            d.name.matches_name_ref(target)
                || AstBindingRef::from_name_ref(target)
                    .is_some_and(|b| d.func.captured_bindings.contains(&b))
                || matches!(target, AstNameRef::Param(p) if d.func.captured_params.contains(p))
        }
        _ => false,
    }
}

/// 折叠双臂单值赋值 `if cond then x = a else x = b end`：
/// - `if a then x = a else x = b end` → `x = a or b`
/// - `if cond then x = truthy_a else x = b end` → `x = cond and truthy_a or b`（严格检查 `is_guaranteed_truthy`！）
/// - Luau 方言支持 `if cond then a else b` 表达式。
fn try_fold_if_value_assign(stmt: &mut AstStmt, target: AstTargetDialect) -> bool {
    let AstStmt::If(if_stmt) = stmt else {
        return false;
    };
    let Some(else_block) = &if_stmt.else_block else {
        return false;
    };
    if if_stmt.then_block.stmts.len() != 1 || else_block.stmts.len() != 1 {
        return false;
    }
    let (AstStmt::Assign(ta), AstStmt::Assign(ea)) =
        (&if_stmt.then_block.stmts[0], &else_block.stmts[0])
    else {
        return false;
    };
    if ta.compound_op.is_some()
        || ea.compound_op.is_some()
        || ta.targets.len() != 1
        || ea.targets.len() != 1
        || ta.values.len() != 1
        || ea.values.len() != 1
        || ta.targets[0] != ea.targets[0]
    {
        return false;
    }
    // 仅对变量目标折叠，避免重复计算复杂左值下标副作用
    if !matches!(ta.targets[0], AstLValue::Name(_)) {
        return false;
    }

    // 检查是否构成 `a or b` / `a and b` / 布尔赋值 / 安全三元 `cond and a or b`
    // 全局变量读取可触发 `_G.__index` 副作用，因此 kind 1~3 严格限定非全局变量。
    let kind = if is_non_global_var(&if_stmt.cond) && if_stmt.cond == ta.values[0] {
        1 // cond or else_val
    } else if is_non_global_var(&if_stmt.cond) && if_stmt.cond == ea.values[0] {
        2 // cond and then_val
    } else if let AstExpr::Unary(u) = &if_stmt.cond
        && u.op == AstUnaryOpKind::Not
        && is_non_global_var(&u.expr)
        && u.expr == ta.values[0]
    {
        3 // inner and else_val
    } else if matches!(&ta.values[0], AstExpr::Boolean(true))
        && matches!(&ea.values[0], AstExpr::Boolean(false))
        && expr_is_guaranteed_boolean(&if_stmt.cond)
    {
        6 // cond (already guaranteed boolean)
    } else if matches!(&ta.values[0], AstExpr::Boolean(false))
        && matches!(&ea.values[0], AstExpr::Boolean(true))
        && !matches!(
            &if_stmt.cond,
            AstExpr::Unary(u) if u.op == AstUnaryOpKind::Not && !expr_is_guaranteed_boolean(&u.expr)
        )
    {
        7 // not cond (NaN-safe, guaranteed boolean)
    } else if matches!(&ta.values[0], AstExpr::LogicalOr(or_e) if or_e.rhs == ea.values[0]) {
        8 // `if cond then x = E or D else x = D end` → `x = cond and E or D`（无 falsy 陷阱！）
    } else if matches!(&ea.values[0], AstExpr::LogicalOr(or_e) if or_e.rhs == ta.values[0]) {
        9 // `if cond then x = D else x = E or D end` → `x = (not cond) and E or D`（无 falsy 陷阱！）
    } else if let AstExpr::LogicalAnd(and_e) = &if_stmt.cond
        && is_non_global_var(&ta.values[0])
        && and_e.rhs == ta.values[0]
    {
        10 // `if C and v then x = v else x = D end` → `x = C and v or D`（v 为假时走 else，天然无 falsy 陷阱！）
    } else if let AstExpr::LogicalOr(or_e) = &if_stmt.cond
        && is_non_global_var(&ea.values[0])
        && matches!(&or_e.rhs, AstExpr::Unary(u) if u.op == AstUnaryOpKind::Not && u.expr == ea.values[0])
    {
        11 // `if A or not v then x = D else x = v end` → `x = (not A) and v or D`（天然无 falsy 陷阱！）
    } else if ta.values[0].is_guaranteed_truthy() {
        4 // cond and then_val or else_val
    } else if target.caps.if_expr {
        5 // Luau native if-expression
    } else {
        return false;
    };

    let AstStmt::If(mut taken) = std::mem::replace(stmt, AstStmt::Break) else {
        unreachable!()
    };
    let AstStmt::Assign(mut ta) = taken.then_block.stmts.pop().unwrap() else {
        unreachable!()
    };
    let AstStmt::Assign(mut ea) = taken.else_block.unwrap().stmts.pop().unwrap() else {
        unreachable!()
    };
    let lhs_target = ta.targets.pop().unwrap();
    let then_val = ta.values.pop().unwrap();
    let else_val = ea.values.pop().unwrap();

    let combined = match kind {
        1 => AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: taken.cond,
            rhs: else_val,
        })),
        2 => AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
            lhs: taken.cond,
            rhs: then_val,
        })),
        3 => {
            let AstExpr::Unary(u) = taken.cond else {
                unreachable!()
            };
            AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                lhs: u.expr,
                rhs: else_val,
            }))
        }
        4 => AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                lhs: taken.cond,
                rhs: then_val,
            })),
            rhs: else_val,
        })),
        5 => AstExpr::IfExpr(Box::new(super::common::AstIfExpr {
            cond: taken.cond,
            then_expr: then_val,
            else_expr: else_val,
        })),
        6 => taken.cond,
        7 => negate_condition_safe(taken.cond),
        8 => {
            let AstExpr::LogicalOr(or_e) = then_val else {
                unreachable!()
            };
            AstExpr::LogicalOr(Box::new(AstLogicalExpr {
                lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                    lhs: taken.cond,
                    rhs: or_e.lhs,
                })),
                rhs: or_e.rhs,
            }))
        }
        9 => {
            let AstExpr::LogicalOr(or_e) = else_val else {
                unreachable!()
            };
            AstExpr::LogicalOr(Box::new(AstLogicalExpr {
                lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                    lhs: negate_cond_for_logical_and(taken.cond),
                    rhs: or_e.lhs,
                })),
                rhs: or_e.rhs,
            }))
        }
        10 => AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: taken.cond,
            rhs: else_val,
        })),
        11 => {
            let AstExpr::LogicalOr(or_e) = taken.cond else {
                unreachable!()
            };
            AstExpr::LogicalOr(Box::new(AstLogicalExpr {
                lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                    lhs: negate_cond_for_logical_and(or_e.lhs),
                    rhs: else_val,
                })),
                rhs: then_val,
            }))
        }
        _ => unreachable!(),
    };

    *stmt = AstStmt::Assign(Box::new(AstAssign {
        targets: vec![lhs_target],
        values: vec![combined],
        compound_op: None,
    }));
    true
}

/// 折叠对称单值早退：`if cond then return a else return b end` → `return <combined>`。
/// 绝不折叠可能多返回或尾调用的 `Call` / `MethodCall` / `VarArg`（保住尾调用优化与多值返回宽度）。
fn try_fold_if_return(stmt: &mut AstStmt, target: AstTargetDialect) -> bool {
    let AstStmt::If(if_stmt) = stmt else {
        return false;
    };
    let Some(else_block) = &if_stmt.else_block else {
        return false;
    };
    if if_stmt.then_block.stmts.len() != 1 || else_block.stmts.len() != 1 {
        return false;
    }
    let (AstStmt::Return(tr), AstStmt::Return(er)) =
        (&if_stmt.then_block.stmts[0], &else_block.stmts[0])
    else {
        return false;
    };
    if tr.values.len() != 1 || er.values.len() != 1 || tr.values[0] == er.values[0] {
        return false;
    }
    let is_multi_or_tail = |e: &AstExpr| {
        matches!(
            e,
            AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg
        )
    };
    if is_multi_or_tail(&tr.values[0]) || is_multi_or_tail(&er.values[0]) {
        return false;
    }
    let Some(kind) = classify_conditional_value_fold(&if_stmt.cond, &tr.values[0], &er.values[0], target) else {
        return false;
    };
    let AstStmt::If(mut taken) = std::mem::replace(stmt, AstStmt::Break) else {
        unreachable!()
    };
    let AstStmt::Return(mut tr) = taken.then_block.stmts.pop().unwrap() else {
        unreachable!()
    };
    let AstStmt::Return(mut er) = taken.else_block.unwrap().stmts.pop().unwrap() else {
        unreachable!()
    };
    let combined = apply_conditional_value_fold(
        kind,
        taken.cond,
        tr.values.pop().unwrap(),
        er.values.pop().unwrap(),
    );
    *stmt = AstStmt::Return(Box::new(super::common::AstReturn {
        values: vec![combined],
    }));
    true
}

fn classify_conditional_value_fold(
    cond: &AstExpr,
    then_val: &AstExpr,
    else_val: &AstExpr,
    target: AstTargetDialect,
) -> Option<u8> {
    if is_non_global_var(cond) && cond == then_val {
        Some(1)
    } else if is_non_global_var(cond) && cond == else_val {
        Some(2)
    } else if let AstExpr::Unary(u) = cond
        && u.op == AstUnaryOpKind::Not
        && is_non_global_var(&u.expr)
        && u.expr == *then_val
    {
        Some(3)
    } else if matches!(then_val, AstExpr::Boolean(true))
        && matches!(else_val, AstExpr::Boolean(false))
        && expr_is_guaranteed_boolean(cond)
    {
        Some(6)
    } else if matches!(then_val, AstExpr::Boolean(false))
        && matches!(else_val, AstExpr::Boolean(true))
        && !matches!(
            cond,
            AstExpr::Unary(u) if u.op == AstUnaryOpKind::Not && !expr_is_guaranteed_boolean(&u.expr)
        )
    {
        Some(7)
    } else if matches!(then_val, AstExpr::LogicalOr(or_e) if or_e.rhs == *else_val) {
        Some(8)
    } else if matches!(else_val, AstExpr::LogicalOr(or_e) if or_e.rhs == *then_val) {
        Some(9)
    } else if let AstExpr::LogicalAnd(and_e) = cond
        && is_non_global_var(then_val)
        && and_e.rhs == *then_val
    {
        Some(10)
    } else if let AstExpr::LogicalOr(or_e) = cond
        && is_non_global_var(else_val)
        && matches!(&or_e.rhs, AstExpr::Unary(u) if u.op == AstUnaryOpKind::Not && u.expr == *else_val)
    {
        Some(11)
    } else if then_val.is_guaranteed_truthy() {
        Some(4)
    } else if target.caps.if_expr {
        Some(5)
    } else {
        None
    }
}

fn apply_conditional_value_fold(
    kind: u8,
    cond: AstExpr,
    then_val: AstExpr,
    else_val: AstExpr,
) -> AstExpr {
    match kind {
        1 => AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: cond,
            rhs: else_val,
        })),
        2 => AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
            lhs: cond,
            rhs: then_val,
        })),
        3 => {
            let AstExpr::Unary(u) = cond else {
                unreachable!()
            };
            AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                lhs: u.expr,
                rhs: else_val,
            }))
        }
        4 => AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                lhs: cond,
                rhs: then_val,
            })),
            rhs: else_val,
        })),
        5 => AstExpr::IfExpr(Box::new(super::common::AstIfExpr {
            cond,
            then_expr: then_val,
            else_expr: else_val,
        })),
        6 => cond,
        7 => negate_condition_safe(cond),
        8 => {
            let AstExpr::LogicalOr(or_e) = then_val else {
                unreachable!()
            };
            AstExpr::LogicalOr(Box::new(AstLogicalExpr {
                lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                    lhs: cond,
                    rhs: or_e.lhs,
                })),
                rhs: or_e.rhs,
            }))
        }
        9 => {
            let AstExpr::LogicalOr(or_e) = else_val else {
                unreachable!()
            };
            AstExpr::LogicalOr(Box::new(AstLogicalExpr {
                lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                    lhs: negate_condition_safe(cond),
                    rhs: or_e.lhs,
                })),
                rhs: or_e.rhs,
            }))
        }
        10 => AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: cond,
            rhs: else_val,
        })),
        11 => {
            let AstExpr::LogicalOr(or_e) = cond else {
                unreachable!()
            };
            AstExpr::LogicalOr(Box::new(AstLogicalExpr {
                lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                    lhs: negate_condition_safe(or_e.lhs),
                    rhs: else_val,
                })),
                rhs: then_val,
            }))
        }
        _ => unreachable!(),
    }
}

fn is_non_global_var(expr: &AstExpr) -> bool {
    matches!(
        expr,
        AstExpr::Var(
            AstNameRef::Local(_)
                | AstNameRef::Param(_)
                | AstNameRef::Upvalue(_)
                | AstNameRef::SyntheticLocal(_)
        )
    )
}

/// 折叠共享同一块体 `B` 的单臂嵌套 `if` 阶梯（严格单调消除 `else`、零重复代码、保序且 NaN 安全）：
/// 1. `if c1 then if c2 then B end else B end` → `if (not c1) or c2 then B end`
/// 2. `if c1 then B else if c2 then B end end` → `if c1 or c2 then B end`
fn try_flatten_shared_branch_nested_if(if_stmt: &mut super::common::AstIf) -> bool {
    let is_plain_shared_body = |block: &AstBlock| -> bool {
        !block.stmts.is_empty()
            && block.stmts.len() <= 3
            && !block_contains_any_label(block)
            && !block.stmts.iter().any(|s| {
                matches!(
                    s,
                    AstStmt::LocalDecl(_)
                        | AstStmt::LocalFunctionDecl(_)
                        | AstStmt::GlobalDecl(_)
                )
            })
    };

    let Some(else_block) = &if_stmt.else_block else {
        return false;
    };

    // Case 1: `then_block` 是单条无 else 的内层 `if`，且其 `then_block` 与外层 `else_block` 逐位完全相同（含 -0.0/+0.0）
    if if_stmt.then_block.stmts.len() == 1
        && is_plain_shared_body(else_block)
        && let AstStmt::If(inner) = &if_stmt.then_block.stmts[0]
        && inner.else_block.is_none()
        && blocks_bitwise_equal(&inner.then_block, else_block)
    {
        let AstStmt::If(inner) = if_stmt.then_block.stmts.remove(0) else {
            unreachable!()
        };
        let outer_cond = std::mem::replace(&mut if_stmt.cond, AstExpr::Boolean(true));
        if_stmt.cond = AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: negate_cond_for_logical_and(outer_cond),
            rhs: inner.cond,
        }));
        if_stmt.then_block = inner.then_block;
        if_stmt.else_block = None;
        return true;
    }

    // Case 2: `else_block` 是单条无 else 的内层 `if`，且其 `then_block` 与外层 `then_block` 逐位完全相同（含 -0.0/+0.0）
    if else_block.stmts.len() == 1
        && is_plain_shared_body(&if_stmt.then_block)
        && let AstStmt::If(inner) = &else_block.stmts[0]
        && inner.else_block.is_none()
        && blocks_bitwise_equal(&inner.then_block, &if_stmt.then_block)
    {
        let mut eb = if_stmt.else_block.take().unwrap();
        let AstStmt::If(inner) = eb.stmts.remove(0) else {
            unreachable!()
        };
        let outer_cond = std::mem::replace(&mut if_stmt.cond, AstExpr::Boolean(true));
        if_stmt.cond = AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: outer_cond,
            rhs: inner.cond,
        }));
        return true;
    }

    false
}

/// 检查两个代码块结构相等且所有浮点字面量位级相等（严格区分 `-0.0` 与 `+0.0`）。
fn blocks_bitwise_equal(a: &AstBlock, b: &AstBlock) -> bool {
    if a != b {
        return false;
    }
    let mut bits_a = Vec::new();
    let mut bits_b = Vec::new();
    collect_block_float_bits(a, &mut bits_a);
    collect_block_float_bits(b, &mut bits_b);
    bits_a == bits_b
}

fn collect_block_float_bits(block: &AstBlock, out: &mut Vec<u64>) {
    use super::traverse::{traverse_call_children, traverse_lvalue_children, traverse_stmt_children};
    for stmt in &block.stmts {
        traverse_stmt_children!(
            stmt,
            iter = iter,
            opt = as_ref,
            borrow = [&],
            expr(e) => {
                collect_expr_float_bits(e, out);
            },
            lvalue(lv) => {
                traverse_lvalue_children!(lv, borrow = [&], expr(e) => {
                    collect_expr_float_bits(e, out);
                });
            },
            block(b) => {
                collect_block_float_bits(b, out);
            },
            function(f) => {
                collect_block_float_bits(&f.body, out);
            },
            condition(c) => {
                collect_expr_float_bits(c, out);
            },
            call(call) => {
                traverse_call_children!(call, iter = iter, borrow = [&], expr(e) => {
                    collect_expr_float_bits(e, out);
                });
            }
        );
    }
}

fn collect_expr_float_bits(expr: &AstExpr, out: &mut Vec<u64>) {
    for node in expr_nodes(expr) {
        if let ExprNode::Expr(AstExpr::Number(n)) = node {
            out.push(n.to_bits());
        } else if let ExprNode::Function(f) = node {
            collect_block_float_bits(&f.body, out);
        }
    }
}

/// NaN 安全的布尔取反，配合 De Morgan 将 `not a or not b` 展平为 `a and b`，绝不翻转 `<`/`<=`。
fn negate_cond_for_logical_and(expr: AstExpr) -> AstExpr {
    match expr {
        AstExpr::Unary(u) if u.op == AstUnaryOpKind::Not => u.expr,
        AstExpr::LogicalOr(or_e) => AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
            lhs: negate_cond_for_logical_and(or_e.lhs),
            rhs: negate_cond_for_logical_and(or_e.rhs),
        })),
        other => negate_condition_safe(other),
    }
}

/// 线性折叠相邻的短路真值早退返回阶梯：
/// `if c1 then x = b1; if x then return x end end; ...; return rest`
/// → `return c1 and b1 or ... or rest`。
fn try_fold_guarded_truthy_return_chain(
    stmts: &mut Vec<AstStmt>,
    captured: &BTreeSet<AstNameRef>,
    debug_hinted: &BTreeSet<AstNameRef>,
) -> bool {
    if stmts.len() < 2 {
        return false;
    }
    let ret_idx = stmts.len() - 1;
    let AstStmt::Return(ret) = &stmts[ret_idx] else {
        return false;
    };
    if ret.values.len() != 1 {
        return false;
    }
    let rest_expr = &ret.values[0];

    let matches_guard_step = |stmt: &AstStmt| -> Option<AstNameRef> {
        let AstStmt::If(outer) = stmt else {
            return None;
        };
        if outer.else_block.is_some() || outer.then_block.stmts.len() != 2 {
            return None;
        }
        let (x_name, rhs_val) = match &outer.then_block.stmts[0] {
            AstStmt::LocalDecl(d)
                if d.bindings.len() == 1
                    && d.values.len() == 1
                    && d.bindings[0].attr == AstLocalAttr::None
                    && !d.bindings[0].is_debug_hinted =>
            {
                (d.bindings[0].id.to_name_ref(), &d.values[0])
            }
            AstStmt::Assign(a)
                if a.compound_op.is_none()
                    && a.targets.len() == 1
                    && a.values.len() == 1
                    && matches!(
                        &a.targets[0],
                        AstLValue::Name(AstNameRef::Local(_) | AstNameRef::SyntheticLocal(_))
                    ) =>
            {
                let AstLValue::Name(n) = &a.targets[0] else {
                    unreachable!()
                };
                (n.clone(), &a.values[0])
            }
            _ => return None,
        };
        let AstStmt::If(inner) = &outer.then_block.stmts[1] else {
            return None;
        };
        if inner.else_block.is_some()
            || inner.cond != AstExpr::Var(x_name.clone())
            || inner.then_block.stmts.len() != 1
        {
            return None;
        }
        let AstStmt::Return(inner_ret) = &inner.then_block.stmts[0] else {
            return None;
        };
        if inner_ret.values.len() != 1 || inner_ret.values[0] != AstExpr::Var(x_name.clone()) {
            return None;
        }
        if captured.contains(&x_name)
            || debug_hinted.contains(&x_name)
            || expr_mentions_name_ref(rhs_val, &x_name)
            || expr_mentions_name_ref(rest_expr, &x_name)
        {
            return None;
        }
        Some(x_name)
    };

    // 向左收集连续匹配的早退阶梯，确保前面任何一步的临时变量都不会被后续步骤读取
    let mut start = ret_idx;
    let mut collected_vars: Vec<AstNameRef> = Vec::new();
    while start > 0 {
        let Some(x_name) = matches_guard_step(&stmts[start - 1]) else {
            break;
        };
        // 确保 `stmts[start..ret_idx]` 中无步骤在条件或右值中读取 `x_name`
        let used_later = stmts[start..ret_idx].iter().any(|s| {
            if let AstStmt::If(outer) = s {
                let rhs_mentions = match &outer.then_block.stmts[0] {
                    AstStmt::LocalDecl(d) => expr_mentions_name_ref(&d.values[0], &x_name),
                    AstStmt::Assign(a) => expr_mentions_name_ref(&a.values[0], &x_name),
                    _ => true,
                };
                expr_mentions_name_ref(&outer.cond, &x_name) || rhs_mentions
            } else {
                true
            }
        });
        if used_later {
            break;
        }
        collected_vars.push(x_name);
        start -= 1;
    }
    if start == ret_idx {
        return false;
    }
    let _ = collected_vars;

    let mut drained: Vec<AstStmt> = stmts.drain(start..=ret_idx).collect();
    let AstStmt::Return(mut tail_ret) = drained.pop().unwrap() else {
        unreachable!()
    };
    let rest = tail_ret.values.pop().unwrap();

    let mut acc: Option<AstExpr> = None;
    for stmt in drained {
        let AstStmt::If(mut outer) = stmt else {
            unreachable!()
        };
        let b_expr = match outer.then_block.stmts.remove(0) {
            AstStmt::LocalDecl(mut d) => d.values.pop().unwrap(),
            AstStmt::Assign(mut a) => a.values.pop().unwrap(),
            _ => unreachable!(),
        };
        let pair = AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
            lhs: outer.cond,
            rhs: b_expr,
        }));
        acc = Some(match acc {
            None => pair,
            Some(prev) => AstExpr::LogicalOr(Box::new(AstLogicalExpr {
                lhs: prev,
                rhs: pair,
            })),
        });
    }
    let final_expr = AstExpr::LogicalOr(Box::new(AstLogicalExpr {
        lhs: acc.unwrap(),
        rhs: rest,
    }));
    stmts.push(AstStmt::Return(Box::new(super::common::AstReturn {
        values: vec![final_expr],
    })));
    true
}

fn lvalue_to_function_name(lv: &AstLValue) -> Option<AstFunctionName> {
    match lv {
        AstLValue::Name(AstNameRef::Global(g)) => Some(AstFunctionName::Plain(AstNamePath {
            root: AstNameRef::Global(g.clone()),
            fields: Vec::new(),
        })),
        AstLValue::FieldAccess(fa) => {
            let mut fields = vec![fa.field.clone()];
            let mut cur = &fa.base;
            while let AstExpr::FieldAccess(inner) = cur {
                fields.push(inner.field.clone());
                cur = &inner.base;
            }
            let AstExpr::Var(root) = cur else {
                return None;
            };
            fields.reverse();
            Some(AstFunctionName::Plain(AstNamePath {
                root: root.clone(),
                fields,
            }))
        }
        _ => None,
    }
}

fn expr_mentions_name_ref(expr: &AstExpr, target: &AstNameRef) -> bool {
    for node in expr_nodes(expr) {
        if let ExprNode::Expr(AstExpr::Var(n)) = node
            && n == target
        {
            return true;
        }
    }
    false
}

/// 检查表达式是否可能调用闭包或触发元方法（用于保护被捕获变量的写后读顺序）。
fn expr_may_invoke_closure(expr: &AstExpr) -> bool {
    for node in expr_nodes(expr) {
        if let ExprNode::Expr(e) = node {
            match e {
                AstExpr::Call(_)
                | AstExpr::MethodCall(_)
                | AstExpr::FieldAccess(_)
                | AstExpr::IndexAccess(_)
                | AstExpr::Binary(_) => return true,
                AstExpr::Unary(u) if u.op != AstUnaryOpKind::Not => return true,
                _ => {}
            }
        }
    }
    false
}

/// 当 `goto` 向前跳入某个 `local` 作用域时，将该 `local` 拆分为块首前向声明 + 原位赋值，
/// 自动修复 Lua 5.2+ / LuaJIT 语法合法性。
fn hoist_binding_above_goto(block: &mut AstBlock, target: AstBindingRef) -> bool {
    // 若当前块含该声明，将其拆分并将前向声明移至块首（最早 goto 之前）
    for idx in 0..block.stmts.len() {
        let contains = match &block.stmts[idx] {
            // `<const>` 与 `<close>` 声明绝不可拆分为无初值前向声明 + 延迟赋值（会产生非法语法）。
            AstStmt::LocalDecl(decl) => {
                decl.bindings.iter().any(|b| b.id == target)
                    && decl.bindings.iter().all(|b| b.attr == AstLocalAttr::None)
            }
            AstStmt::LocalFunctionDecl(decl) => decl.name == target,
            _ => false,
        };
        if !contains {
            continue;
        }
        if idx == 0 {
            return false;
        }
        match std::mem::replace(&mut block.stmts[idx], AstStmt::Break) {
            AstStmt::LocalDecl(decl) => {
                let empty_decl = AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: decl.bindings.clone(),
                    values: Vec::new(),
                }));
                if decl.values.is_empty() {
                    block.stmts.remove(idx);
                } else {
                    block.stmts[idx] = AstStmt::Assign(Box::new(AstAssign {
                        targets: decl
                            .bindings
                            .into_iter()
                            .map(|b| AstLValue::Name(b.id.to_name_ref()))
                            .collect(),
                        values: decl.values,
                        compound_op: None,
                    }));
                }
                block.stmts.insert(0, empty_decl);
                return true;
            }
            AstStmt::LocalFunctionDecl(decl) => {
                let empty_decl = AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: decl.name,
                        attr: AstLocalAttr::None,
                        is_debug_hinted: false,
                    }],
                    values: Vec::new(),
                }));
                block.stmts[idx] = AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(decl.name.to_name_ref())],
                    values: vec![AstExpr::FunctionExpr(Box::new(decl.func))],
                    compound_op: None,
                }));
                block.stmts.insert(0, empty_decl);
                return true;
            }
            other => {
                block.stmts[idx] = other;
            }
        }
    }

    for stmt in &mut block.stmts {
        let fixed = match stmt {
            AstStmt::If(if_stmt) => {
                hoist_binding_above_goto(&mut if_stmt.then_block, target)
                    || if_stmt
                        .else_block
                        .as_mut()
                        .is_some_and(|b| hoist_binding_above_goto(b, target))
            }
            AstStmt::While(w) => hoist_binding_above_goto(&mut w.body, target),
            AstStmt::Repeat(r) => hoist_binding_above_goto(&mut r.body, target),
            AstStmt::NumericFor(nf) => hoist_binding_above_goto(&mut nf.body, target),
            AstStmt::GenericFor(gf) => hoist_binding_above_goto(&mut gf.body, target),
            AstStmt::DoBlock(b) => hoist_binding_above_goto(b, target),
            AstStmt::FunctionDecl(d) => hoist_binding_above_goto(&mut d.func.body, target),
            AstStmt::LocalFunctionDecl(d) => hoist_binding_above_goto(&mut d.func.body, target),
            _ => false,
        };
        if fixed {
            return true;
        }
    }
    false
}

/// 还原 Luau `-O2` 内联的无参递归闭包工厂调用：
/// 当存在不可变无参局部函数 `local function F() return function(...) ... F() ... end end` 且后续作用域
/// 出现与其返回值完全 α-等价（且全部自由变量/上值解析到同一外层绑定）的内联闭包副本时，折叠回 `F()`，
/// 避免重编译时 Luau `-O2` 每轮递归再多展开一层导致永不收敛。
fn fold_inlined_recursive_closure_factories(
    block: &mut AstBlock,
    current_proto: ProtoId,
    protos: &[AstProtoMeta],
    debug_hinted: &BTreeSet<AstNameRef>,
) -> bool {
    let mut changed = false;

    // 先收集当前块中全部满足条件的不可变 0 参递归闭包工厂
    let mut factories: Vec<(usize, AstBindingRef, AstFunctionExpr)> = Vec::new();
    for (idx, stmt) in block.stmts.iter().enumerate() {
        let AstStmt::LocalFunctionDecl(lfd) = stmt else {
            continue;
        };
        if !lfd.func.params.is_empty()
            || lfd.func.is_vararg
            || lfd.func.named_vararg.is_some()
            || lfd.func.body.stmts.len() != 1
        {
            continue;
        }
        let AstStmt::Return(ret) = &lfd.func.body.stmts[0] else {
            continue;
        };
        if ret.values.len() != 1 {
            continue;
        }
        let AstExpr::FunctionExpr(template_fn) = &ret.values[0] else {
            continue;
        };
        let factory_binding = lfd.name;
        let factory_name = factory_binding.to_name_ref();
        if block.stmts[idx + 1..]
            .iter()
            .any(|s| stmt_writes_name_ref(s, &factory_name))
        {
            continue;
        }
        if is_binding_captured_by_ref(protos, current_proto, factory_binding) {
            continue;
        }
        let Some(target_resolved) =
            resolve_name_in_target(protos, current_proto, &factory_name, current_proto)
        else {
            continue;
        };
        if !block_references_resolved_name(
            &template_fn.body,
            template_fn.function,
            current_proto,
            protos,
            &target_resolved,
        ) {
            continue;
        }
        factories.push((idx, factory_binding, (**template_fn).clone()));
    }

    for (decl_idx, factory_binding, template_fn) in &factories {
        let factory_name = factory_binding.to_name_ref();
        for stmt in &mut block.stmts[decl_idx + 1..] {
            changed |= replace_matching_closure_in_stmt(
                stmt,
                template_fn,
                &factory_name,
                current_proto,
                protos,
                debug_hinted,
            );
        }
    }

    // 递归处理子块与嵌套函数体
    for stmt in &mut block.stmts {
        match stmt {
            AstStmt::If(i) => {
                changed |= fold_inlined_recursive_closure_factories(
                    &mut i.then_block,
                    current_proto,
                    protos,
                    debug_hinted,
                );
                if let Some(eb) = &mut i.else_block {
                    changed |= fold_inlined_recursive_closure_factories(
                        eb,
                        current_proto,
                        protos,
                        debug_hinted,
                    );
                }
            }
            AstStmt::While(w) => {
                changed |= fold_inlined_recursive_closure_factories(
                    &mut w.body,
                    current_proto,
                    protos,
                    debug_hinted,
                );
            }
            AstStmt::Repeat(r) => {
                changed |= fold_inlined_recursive_closure_factories(
                    &mut r.body,
                    current_proto,
                    protos,
                    debug_hinted,
                );
            }
            AstStmt::NumericFor(nf) => {
                changed |= fold_inlined_recursive_closure_factories(
                    &mut nf.body,
                    current_proto,
                    protos,
                    debug_hinted,
                );
            }
            AstStmt::GenericFor(gf) => {
                changed |= fold_inlined_recursive_closure_factories(
                    &mut gf.body,
                    current_proto,
                    protos,
                    debug_hinted,
                );
            }
            AstStmt::DoBlock(b) => {
                changed |= fold_inlined_recursive_closure_factories(
                    b,
                    current_proto,
                    protos,
                    debug_hinted,
                );
            }
            AstStmt::FunctionDecl(d) => {
                let child_dbg = collect_debug_hinted_names_in_block(&d.func.body);
                changed |= fold_inlined_recursive_closure_factories(
                    &mut d.func.body,
                    d.func.function,
                    protos,
                    &child_dbg,
                );
            }
            AstStmt::LocalFunctionDecl(d) => {
                let child_dbg = collect_debug_hinted_names_in_block(&d.func.body);
                changed |= fold_inlined_recursive_closure_factories(
                    &mut d.func.body,
                    d.func.function,
                    protos,
                    &child_dbg,
                );
            }
            _ => {}
        }
    }

    changed
}

fn is_binding_captured_by_ref(
    protos: &[AstProtoMeta],
    owner: ProtoId,
    binding: AstBindingRef,
) -> bool {
    let target_cap = match binding {
        AstBindingRef::Local(l) => AstCaptureBinding::Local(l),
        AstBindingRef::SyntheticLocal(s) => AstCaptureBinding::SyntheticLocal(s),
    };
    protos.iter().any(|p| {
        p.parent_captures.as_ref().is_some_and(|(parent, caps)| {
            *parent == owner
                && caps
                    .iter()
                    .any(|c| c.mode == AstCaptureMode::ByReference && c.binding == target_cap)
        })
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ResolvedOuterName {
    Global(String),
    Environment,
    Target(AstCaptureBinding),
}

fn resolve_name_in_target(
    protos: &[AstProtoMeta],
    from_proto: ProtoId,
    name: &AstNameRef,
    target_proto: ProtoId,
) -> Option<ResolvedOuterName> {
    match name {
        AstNameRef::Global(g) => Some(ResolvedOuterName::Global(g.text.clone())),
        AstNameRef::Environment => Some(ResolvedOuterName::Environment),
        AstNameRef::Local(l) => (from_proto == target_proto)
            .then_some(ResolvedOuterName::Target(AstCaptureBinding::Local(*l))),
        AstNameRef::Param(p) => (from_proto == target_proto)
            .then_some(ResolvedOuterName::Target(AstCaptureBinding::Param(*p))),
        AstNameRef::SyntheticLocal(s) => (from_proto == target_proto).then_some(
            ResolvedOuterName::Target(AstCaptureBinding::SyntheticLocal(*s)),
        ),
        AstNameRef::Upvalue(u) => {
            let mut cur_proto = from_proto;
            let mut cur_upval = *u;
            for _ in 0..64 {
                if cur_proto == target_proto {
                    return Some(ResolvedOuterName::Target(AstCaptureBinding::Upvalue(
                        cur_upval,
                    )));
                }
                let (parent, caps) = protos.get(cur_proto.index())?.parent_captures.as_ref()?;
                let cap = caps.get(cur_upval.index())?;
                if *parent == target_proto {
                    return Some(ResolvedOuterName::Target(cap.binding));
                }
                match cap.binding {
                    AstCaptureBinding::Upvalue(parent_u) => {
                        cur_proto = *parent;
                        cur_upval = parent_u;
                    }
                    _ => return None,
                }
            }
            None
        }
    }
}

fn block_references_resolved_name(
    block: &AstBlock,
    from_proto: ProtoId,
    target_proto: ProtoId,
    protos: &[AstProtoMeta],
    target: &ResolvedOuterName,
) -> bool {
    let check_expr = |e: &AstExpr| -> bool {
        for node in expr_nodes(e) {
            if let ExprNode::Expr(AstExpr::Var(n)) = node
                && resolve_name_in_target(protos, from_proto, n, target_proto).as_ref()
                    == Some(target)
            {
                return true;
            }
        }
        false
    };
    block.stmts.iter().any(|stmt| match stmt {
        AstStmt::LocalDecl(d) => d.values.iter().any(check_expr),
        AstStmt::Assign(a) => a.values.iter().any(check_expr),
        AstStmt::CallStmt(c) => match &c.call {
            AstCallKind::Call(call) => check_expr(&call.callee) || call.args.iter().any(check_expr),
            AstCallKind::MethodCall(m) => {
                check_expr(&m.receiver) || m.args.iter().any(check_expr)
            }
        },
        AstStmt::Return(r) => r.values.iter().any(check_expr),
        AstStmt::If(i) => {
            check_expr(&i.cond)
                || block_references_resolved_name(&i.then_block, from_proto, target_proto, protos, target)
                || i.else_block.as_ref().is_some_and(|eb| {
                    block_references_resolved_name(eb, from_proto, target_proto, protos, target)
                })
        }
        AstStmt::While(w) => {
            check_expr(&w.cond)
                || block_references_resolved_name(&w.body, from_proto, target_proto, protos, target)
        }
        AstStmt::Repeat(r) => {
            block_references_resolved_name(&r.body, from_proto, target_proto, protos, target)
                || check_expr(&r.cond)
        }
        AstStmt::DoBlock(b) => {
            block_references_resolved_name(b, from_proto, target_proto, protos, target)
        }
        _ => false,
    })
}

fn replace_matching_closure_in_stmt(
    stmt: &mut AstStmt,
    template_fn: &AstFunctionExpr,
    factory_name: &AstNameRef,
    current_proto: ProtoId,
    protos: &[AstProtoMeta],
    debug_hinted: &BTreeSet<AstNameRef>,
) -> bool {
    if let AstStmt::LocalFunctionDecl(d) = stmt
        && functions_alpha_equiv(template_fn, &d.func, current_proto, protos)
    {
        let binding_id = d.name;
        *stmt = AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: binding_id,
                attr: AstLocalAttr::None,
                is_debug_hinted: debug_hinted.contains(&binding_id.to_name_ref()),
            }],
            values: vec![AstExpr::Call(Box::new(AstCallExpr {
                callee: AstExpr::Var(factory_name.clone()),
                args: Vec::new(),
            }))],
        }));
        return true;
    }

    let mut changed = false;
    match stmt {
        AstStmt::LocalDecl(d) => {
            for v in &mut d.values {
                changed |= replace_matching_closure_in_expr(
                    v,
                    template_fn,
                    factory_name,
                    current_proto,
                    protos,
                );
            }
        }
        AstStmt::Assign(a) => {
            for v in &mut a.values {
                changed |= replace_matching_closure_in_expr(
                    v,
                    template_fn,
                    factory_name,
                    current_proto,
                    protos,
                );
            }
        }
        AstStmt::Return(r) => {
            for v in &mut r.values {
                changed |= replace_matching_closure_in_expr(
                    v,
                    template_fn,
                    factory_name,
                    current_proto,
                    protos,
                );
            }
        }
        AstStmt::CallStmt(c) => match &mut c.call {
            AstCallKind::Call(call) => {
                changed |= replace_matching_closure_in_expr(
                    &mut call.callee,
                    template_fn,
                    factory_name,
                    current_proto,
                    protos,
                );
                for a in &mut call.args {
                    changed |= replace_matching_closure_in_expr(
                        a,
                        template_fn,
                        factory_name,
                        current_proto,
                        protos,
                    );
                }
            }
            AstCallKind::MethodCall(m) => {
                changed |= replace_matching_closure_in_expr(
                    &mut m.receiver,
                    template_fn,
                    factory_name,
                    current_proto,
                    protos,
                );
                for a in &mut m.args {
                    changed |= replace_matching_closure_in_expr(
                        a,
                        template_fn,
                        factory_name,
                        current_proto,
                        protos,
                    );
                }
            }
        },
        AstStmt::If(i) => {
            for s in &mut i.then_block.stmts {
                changed |= replace_matching_closure_in_stmt(
                    s,
                    template_fn,
                    factory_name,
                    current_proto,
                    protos,
                    debug_hinted,
                );
            }
            if let Some(eb) = &mut i.else_block {
                for s in &mut eb.stmts {
                    changed |= replace_matching_closure_in_stmt(
                        s,
                        template_fn,
                        factory_name,
                        current_proto,
                        protos,
                        debug_hinted,
                    );
                }
            }
        }
        AstStmt::DoBlock(b) => {
            for s in &mut b.stmts {
                changed |= replace_matching_closure_in_stmt(
                    s,
                    template_fn,
                    factory_name,
                    current_proto,
                    protos,
                    debug_hinted,
                );
            }
        }
        _ => {}
    }
    changed
}

fn replace_matching_closure_in_expr(
    expr: &mut AstExpr,
    template_fn: &AstFunctionExpr,
    factory_name: &AstNameRef,
    current_proto: ProtoId,
    protos: &[AstProtoMeta],
) -> bool {
    if let AstExpr::FunctionExpr(site_fn) = expr
        && functions_alpha_equiv(template_fn, site_fn, current_proto, protos)
    {
        *expr = AstExpr::Call(Box::new(AstCallExpr {
            callee: AstExpr::Var(factory_name.clone()),
            args: Vec::new(),
        }));
        return true;
    }
    match expr {
        AstExpr::SingleValue(inner) => replace_matching_closure_in_expr(
            inner,
            template_fn,
            factory_name,
            current_proto,
            protos,
        ),
        AstExpr::Binary(b) => {
            let mut ch = replace_matching_closure_in_expr(
                &mut b.lhs,
                template_fn,
                factory_name,
                current_proto,
                protos,
            );
            ch |= replace_matching_closure_in_expr(
                &mut b.rhs,
                template_fn,
                factory_name,
                current_proto,
                protos,
            );
            ch
        }
        AstExpr::Call(c) => {
            let mut ch = replace_matching_closure_in_expr(
                &mut c.callee,
                template_fn,
                factory_name,
                current_proto,
                protos,
            );
            for a in &mut c.args {
                ch |= replace_matching_closure_in_expr(
                    a,
                    template_fn,
                    factory_name,
                    current_proto,
                    protos,
                );
            }
            ch
        }
        AstExpr::MethodCall(m) => {
            let mut ch = replace_matching_closure_in_expr(
                &mut m.receiver,
                template_fn,
                factory_name,
                current_proto,
                protos,
            );
            for a in &mut m.args {
                ch |= replace_matching_closure_in_expr(
                    a,
                    template_fn,
                    factory_name,
                    current_proto,
                    protos,
                );
            }
            ch
        }
        _ => false,
    }
}

struct AlphaEnv<'a> {
    map: BTreeMap<AstNameRef, AstNameRef>,
    image: BTreeSet<AstNameRef>,
    proto_a: ProtoId,
    proto_b: ProtoId,
    target_proto: ProtoId,
    protos: &'a [AstProtoMeta],
}

impl AlphaEnv<'_> {
    fn bind(&mut self, a: AstNameRef, b: AstNameRef) {
        self.map.insert(a, b.clone());
        self.image.insert(b);
    }

    fn names_equiv(&self, a: &AstNameRef, b: &AstNameRef) -> bool {
        if let Some(mapped) = self.map.get(a) {
            return mapped == b;
        }
        if self.image.contains(b) {
            return false;
        }
        let ra = resolve_name_in_target(self.protos, self.proto_a, a, self.target_proto);
        let rb = resolve_name_in_target(self.protos, self.proto_b, b, self.target_proto);
        ra.is_some() && ra == rb
    }
}

fn functions_alpha_equiv(
    a: &AstFunctionExpr,
    b: &AstFunctionExpr,
    target_proto: ProtoId,
    protos: &[AstProtoMeta],
) -> bool {
    // 严格要求两处闭包源自同一底层字节码 `RawProto`（Luau `-O2` 内联会复用同一个 `Proto*`），
    // 绝不把源码中独立书写的两个等价闭包字面量合并为同一个工厂调用（会改变 `factory() == other` 闭包身份）！
    let origin_a = protos.get(a.function.index()).and_then(|p| p.source_origin);
    let origin_b = protos.get(b.function.index()).and_then(|p| p.source_origin);
    if origin_a.is_none() || origin_a != origin_b {
        return false;
    }
    if a.params.len() != b.params.len()
        || a.is_vararg != b.is_vararg
        || a.named_vararg.is_some() != b.named_vararg.is_some()
    {
        return false;
    }
    let mut env = AlphaEnv {
        map: BTreeMap::new(),
        image: BTreeSet::new(),
        proto_a: a.function,
        proto_b: b.function,
        target_proto,
        protos,
    };
    for (&pa, &pb) in a.params.iter().zip(&b.params) {
        env.bind(AstNameRef::Param(pa), AstNameRef::Param(pb));
    }
    if let (Some(va), Some(vb)) = (a.named_vararg, b.named_vararg) {
        env.bind(va.to_name_ref(), vb.to_name_ref());
    }
    blocks_alpha_equiv(&a.body, &b.body, &mut env)
}

fn blocks_alpha_equiv(a: &AstBlock, b: &AstBlock, env: &mut AlphaEnv<'_>) -> bool {
    if a.stmts.len() != b.stmts.len() {
        return false;
    }
    a.stmts
        .iter()
        .zip(&b.stmts)
        .all(|(sa, sb)| stmts_alpha_equiv(sa, sb, env))
}

fn stmts_alpha_equiv(a: &AstStmt, b: &AstStmt, env: &mut AlphaEnv<'_>) -> bool {
    match (a, b) {
        (AstStmt::LocalDecl(da), AstStmt::LocalDecl(db)) => {
            if da.bindings.len() != db.bindings.len() || da.values.len() != db.values.len() {
                return false;
            }
            if !da
                .values
                .iter()
                .zip(&db.values)
                .all(|(va, vb)| exprs_alpha_equiv(va, vb, env))
            {
                return false;
            }
            for (ba, bb) in da.bindings.iter().zip(&db.bindings) {
                if ba.attr != bb.attr {
                    return false;
                }
                env.bind(ba.id.to_name_ref(), bb.id.to_name_ref());
            }
            true
        }
        (AstStmt::Assign(aa), AstStmt::Assign(ab)) => {
            aa.compound_op == ab.compound_op
                && aa.targets.len() == ab.targets.len()
                && aa.values.len() == ab.values.len()
                && aa
                    .targets
                    .iter()
                    .zip(&ab.targets)
                    .all(|(ta, tb)| lvalues_alpha_equiv(ta, tb, env))
                && aa
                    .values
                    .iter()
                    .zip(&ab.values)
                    .all(|(va, vb)| exprs_alpha_equiv(va, vb, env))
        }
        (AstStmt::CallStmt(ca), AstStmt::CallStmt(cb)) => match (&ca.call, &cb.call) {
            (AstCallKind::Call(a), AstCallKind::Call(b)) => {
                exprs_alpha_equiv(&a.callee, &b.callee, env)
                    && a.args.len() == b.args.len()
                    && a.args
                        .iter()
                        .zip(&b.args)
                        .all(|(xa, xb)| exprs_alpha_equiv(xa, xb, env))
            }
            (AstCallKind::MethodCall(a), AstCallKind::MethodCall(b)) => {
                a.method == b.method
                    && exprs_alpha_equiv(&a.receiver, &b.receiver, env)
                    && a.args.len() == b.args.len()
                    && a.args
                        .iter()
                        .zip(&b.args)
                        .all(|(xa, xb)| exprs_alpha_equiv(xa, xb, env))
            }
            _ => false,
        },
        (AstStmt::Return(ra), AstStmt::Return(rb)) => {
            ra.values.len() == rb.values.len()
                && ra
                    .values
                    .iter()
                    .zip(&rb.values)
                    .all(|(va, vb)| exprs_alpha_equiv(va, vb, env))
        }
        (AstStmt::If(ia), AstStmt::If(ib)) => {
            exprs_alpha_equiv(&ia.cond, &ib.cond, env)
                && blocks_alpha_equiv(&ia.then_block, &ib.then_block, env)
                && match (&ia.else_block, &ib.else_block) {
                    (Some(ea), Some(eb)) => blocks_alpha_equiv(ea, eb, env),
                    (None, None) => true,
                    _ => false,
                }
        }
        (AstStmt::While(wa), AstStmt::While(wb)) => {
            exprs_alpha_equiv(&wa.cond, &wb.cond, env) && blocks_alpha_equiv(&wa.body, &wb.body, env)
        }
        (AstStmt::Repeat(ra), AstStmt::Repeat(rb)) => {
            blocks_alpha_equiv(&ra.body, &rb.body, env) && exprs_alpha_equiv(&ra.cond, &rb.cond, env)
        }
        (AstStmt::DoBlock(da), AstStmt::DoBlock(db)) => blocks_alpha_equiv(da, db, env),
        (AstStmt::Break, AstStmt::Break) | (AstStmt::Continue, AstStmt::Continue) => true,
        _ => false,
    }
}

fn lvalues_alpha_equiv(a: &AstLValue, b: &AstLValue, env: &AlphaEnv<'_>) -> bool {
    match (a, b) {
        (AstLValue::Name(na), AstLValue::Name(nb)) => env.names_equiv(na, nb),
        (AstLValue::FieldAccess(fa), AstLValue::FieldAccess(fb)) => {
            fa.field == fb.field && exprs_alpha_equiv(&fa.base, &fb.base, env)
        }
        (AstLValue::IndexAccess(ia), AstLValue::IndexAccess(ib)) => {
            exprs_alpha_equiv(&ia.base, &ib.base, env)
                && exprs_alpha_equiv(&ia.index, &ib.index, env)
        }
        _ => false,
    }
}

fn exprs_alpha_equiv(a: &AstExpr, b: &AstExpr, env: &AlphaEnv<'_>) -> bool {
    match (a, b) {
        (AstExpr::Nil, AstExpr::Nil) | (AstExpr::VarArg, AstExpr::VarArg) => true,
        (AstExpr::Boolean(x), AstExpr::Boolean(y)) => x == y,
        (AstExpr::Integer(x), AstExpr::Integer(y)) => x == y,
        (AstExpr::Number(x), AstExpr::Number(y)) => x.to_bits() == y.to_bits(),
        (AstExpr::String(x), AstExpr::String(y)) => x == y,
        (AstExpr::Var(na), AstExpr::Var(nb)) => env.names_equiv(na, nb),
        (AstExpr::Unary(ua), AstExpr::Unary(ub)) => {
            ua.op == ub.op && exprs_alpha_equiv(&ua.expr, &ub.expr, env)
        }
        (AstExpr::Binary(ba), AstExpr::Binary(bb)) => {
            ba.op == bb.op
                && exprs_alpha_equiv(&ba.lhs, &bb.lhs, env)
                && exprs_alpha_equiv(&ba.rhs, &bb.rhs, env)
        }
        (AstExpr::LogicalAnd(la), AstExpr::LogicalAnd(lb))
        | (AstExpr::LogicalOr(la), AstExpr::LogicalOr(lb)) => {
            exprs_alpha_equiv(&la.lhs, &lb.lhs, env) && exprs_alpha_equiv(&la.rhs, &lb.rhs, env)
        }
        (AstExpr::FieldAccess(fa), AstExpr::FieldAccess(fb)) => {
            fa.field == fb.field && exprs_alpha_equiv(&fa.base, &fb.base, env)
        }
        (AstExpr::IndexAccess(ia), AstExpr::IndexAccess(ib)) => {
            exprs_alpha_equiv(&ia.base, &ib.base, env)
                && exprs_alpha_equiv(&ia.index, &ib.index, env)
        }
        (AstExpr::Call(ca), AstExpr::Call(cb)) => {
            exprs_alpha_equiv(&ca.callee, &cb.callee, env)
                && ca.args.len() == cb.args.len()
                && ca
                    .args
                    .iter()
                    .zip(&cb.args)
                    .all(|(xa, xb)| exprs_alpha_equiv(xa, xb, env))
        }
        (AstExpr::MethodCall(ma), AstExpr::MethodCall(mb)) => {
            ma.method == mb.method
                && exprs_alpha_equiv(&ma.receiver, &mb.receiver, env)
                && ma.args.len() == mb.args.len()
                && ma
                    .args
                    .iter()
                    .zip(&mb.args)
                    .all(|(xa, xb)| exprs_alpha_equiv(xa, xb, env))
        }
        (AstExpr::SingleValue(sa), AstExpr::SingleValue(sb)) => exprs_alpha_equiv(sa, sb, env),
        (AstExpr::IfExpr(ia), AstExpr::IfExpr(ib)) => {
            exprs_alpha_equiv(&ia.cond, &ib.cond, env)
                && exprs_alpha_equiv(&ia.then_expr, &ib.then_expr, env)
                && exprs_alpha_equiv(&ia.else_expr, &ib.else_expr, env)
        }
        _ => false,
    }
}
