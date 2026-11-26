//! 最窄支配块局部声明插入（LCA Scope Placement）。
//!
//! 将需要物化的 `LocalId` 自动声明在支配其全部出现位置的最深词法块中，
//! 正确处理 `repeat ... until` 条件处于 body 作用域内的 Lua 特例，
//! 并将首次赋值就地合并为 `local x = init`，同时避免大函数将所有 local 堆到顶层撑爆 200 槽上限。

use std::collections::{BTreeMap, BTreeSet};

use super::super::common::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstLValue, AstLocalAttr, AstLocalBinding,
    AstLocalDecl, AstNameRef, AstStmt, LocalId,
};
use super::super::traverse::{traverse_call_children, traverse_lvalue_children};
use super::super::visit::{ExprNode, expr_nodes};
use super::expr_mentions_name;

/// 块路径：从根块（空路径）沿语句下标与子块编号定位任意嵌套词法块。
/// 每级元素为 `(stmt_index_in_parent_block, subblock_slot, is_loop_body)`。
type BlockPath = Vec<(usize, u8, bool)>;

#[derive(Clone, Debug)]
struct DeclaredScope {
    /// 声明生效的词法块路径（`for` 头绑定为其 body 块路径，`LocalDecl`/`LocalFunctionDecl` 为所在块路径，函数入口为 `[]`）。
    path: BlockPath,
    /// 在 `path` 中开始生效的语句下标（`0` 表示块内所有语句，普通 `local` 为 `decl_idx + 1`，`local function` 为 `decl_idx`）。
    start_stmt_idx: usize,
}

impl DeclaredScope {
    fn covers(&self, site_path: &BlockPath, site_idx: usize) -> bool {
        if site_path.len() < self.path.len() || !site_path.starts_with(&self.path) {
            return false;
        }
        if site_path.len() == self.path.len() {
            site_idx >= self.start_stmt_idx
        } else {
            site_path[self.path.len()].0 >= self.start_stmt_idx
        }
    }
}

#[derive(Default)]
struct LocalOccurrence {
    /// 每个 `LocalId` 已被词法声明覆盖的作用域列表（按作用域精确判定，绝不让嵌套 `for`/`do` 声明掩盖外层引用！）。
    declared_scopes: BTreeMap<LocalId, Vec<DeclaredScope>>,
    /// 每个 `LocalId` 出现的所有 `(block_path, stmt_index_in_that_block)`。
    sites: BTreeMap<LocalId, Vec<(BlockPath, usize)>>,
}

/// 为当前函数体插入所有缺失的 `local` 声明，并将首次顶层赋值合并为初始化声明。
pub(super) fn insert_local_declarations(
    body: &mut AstBlock,
    tbc_locals: &BTreeSet<LocalId>,
    debug_hinted_locals: &BTreeSet<LocalId>,
    vararg_param_local: Option<LocalId>,
    loop_shared_capture_locals: &BTreeSet<LocalId>,
    predeclared_locals: &BTreeSet<LocalId>,
) {
    let mut occ = LocalOccurrence::default();
    if let Some(vr) = vararg_param_local {
        occ.declared_scopes.entry(vr).or_default().push(DeclaredScope {
            path: Vec::new(),
            start_stmt_idx: 0,
        });
    }
    for &pre in predeclared_locals {
        occ.declared_scopes.entry(pre).or_default().push(DeclaredScope {
            path: Vec::new(),
            start_stmt_idx: 0,
        });
    }

    let mut path = Vec::new();
    collect_block(body, &mut path, &mut occ);

    // 为每个存在未覆盖出现点的 LocalId 计算最深公共祖先块（LCA）及该块内最早出现位置
    let mut placements: BTreeMap<BlockPath, Vec<(usize, LocalId)>> = BTreeMap::new();
    for (local, sites) in occ.sites {
        let scopes = occ.declared_scopes.get(&local);
        let uncovered: Vec<&(BlockPath, usize)> = sites
            .iter()
            .filter(|(p, idx)| {
                !scopes.is_some_and(|list| list.iter().any(|s| s.covers(p, *idx)))
            })
            .collect();
        if uncovered.is_empty() {
            continue;
        }
        let mut lca_path = uncovered[0].0.clone();
        for (p, _) in uncovered.iter().skip(1) {
            let common_len = lca_path
                .iter()
                .zip(p.iter())
                .take_while(|(a, b)| a == b)
                .count();
            lca_path.truncate(common_len);
        }

        // 若该变量在循环内被按引用捕获但循环体内没有显式 CLOSE，
        // 绝不能下沉进任何循环体内部（否则每轮迭代会各自创建新 upvalue cell！）
        if loop_shared_capture_locals.contains(&local)
            && let Some(first_loop_depth) = lca_path.iter().position(|&(_, _, is_loop)| is_loop)
        {
            lca_path.truncate(first_loop_depth);
        }

        // 若该变量在 LCA 所在循环体内存在“先读后写”（跨迭代携带状态的循环变量，
        // 如 Lua 5.1 省略 LOADNIL 的 `local prev; for ... do if prev then ... end; prev = cur end`），
        // 绝不能将 `local` 声明下沉到该循环体内，否则每轮迭代都会被重置为 `nil`！
        while let Some(loop_depth) = lca_path.iter().rposition(|&(_, _, is_loop)| is_loop) {
            if let Some(loop_body) = block_at_path(body, &lca_path[..=loop_depth])
                && block_reads_local_before_def(loop_body, local)
            {
                lca_path.truncate(loop_depth);
            } else {
                break;
            }
        }

        // 在 lca_path 中找到覆盖所有未覆盖出现点的最早语句下标
        let mut min_stmt_idx = usize::MAX;
        for (p, stmt_idx) in &uncovered {
            let idx_in_lca = if p.len() == lca_path.len() {
                *stmt_idx
            } else {
                p[lca_path.len()].0
            };
            min_stmt_idx = min_stmt_idx.min(idx_in_lca);
        }
        if min_stmt_idx != usize::MAX {
            placements
                .entry(lca_path)
                .or_default()
                .push((min_stmt_idx, local));
        }
    }

    // 应用声明插入（先按路径由深到浅、块内由后向前插入，不破坏同块前序下标）
    let mut path_buf = Vec::new();
    apply_placements(
        body,
        &mut path_buf,
        &placements,
        tbc_locals,
        debug_hinted_locals,
    );
}

fn collect_block(block: &AstBlock, path: &mut BlockPath, occ: &mut LocalOccurrence) {
    for (idx, stmt) in block.stmts.iter().enumerate() {
        collect_stmt(stmt, idx, path, occ);
    }
}

fn collect_stmt(stmt: &AstStmt, idx: usize, path: &mut BlockPath, occ: &mut LocalOccurrence) {
    match stmt {
        AstStmt::LocalDecl(decl) => {
            for v in &decl.values {
                collect_expr(v, idx, path, occ);
            }
            for b in &decl.bindings {
                if let AstBindingRef::Local(l) = b.id {
                    occ.declared_scopes
                        .entry(l)
                        .or_default()
                        .push(DeclaredScope {
                            path: path.clone(),
                            start_stmt_idx: idx + 1,
                        });
                }
            }
        }
        AstStmt::GlobalDecl(decl) => {
            for v in &decl.values {
                collect_expr(v, idx, path, occ);
            }
        }
        AstStmt::Assign(assign) => {
            for t in &assign.targets {
                collect_lvalue(t, idx, path, occ);
            }
            for v in &assign.values {
                collect_expr(v, idx, path, occ);
            }
        }
        AstStmt::CallStmt(call) => collect_call(&call.call, idx, path, occ),
        AstStmt::Return(ret) => {
            for v in &ret.values {
                collect_expr(v, idx, path, occ);
            }
        }
        AstStmt::If(if_stmt) => {
            collect_expr(&if_stmt.cond, idx, path, occ);
            path.push((idx, 0, false));
            collect_block(&if_stmt.then_block, path, occ);
            path.pop();
            if let Some(else_block) = &if_stmt.else_block {
                path.push((idx, 1, false));
                collect_block(else_block, path, occ);
                path.pop();
            }
        }
        AstStmt::While(w) => {
            collect_expr(&w.cond, idx, path, occ);
            path.push((idx, 0, true));
            collect_block(&w.body, path, occ);
            path.pop();
        }
        AstStmt::Repeat(r) => {
            // Lua 规则：`repeat ... until cond` 的 cond 位于 body 词法作用域末尾！
            path.push((idx, 0, true));
            collect_block(&r.body, path, occ);
            let cond_site_idx = r.body.stmts.len();
            collect_expr(&r.cond, cond_site_idx, path, occ);
            path.pop();
        }
        AstStmt::NumericFor(nf) => {
            collect_expr(&nf.start, idx, path, occ);
            collect_expr(&nf.limit, idx, path, occ);
            collect_expr(&nf.step, idx, path, occ);
            path.push((idx, 0, true));
            if let AstBindingRef::Local(l) = nf.binding {
                occ.declared_scopes
                    .entry(l)
                    .or_default()
                    .push(DeclaredScope {
                        path: path.clone(),
                        start_stmt_idx: 0,
                    });
            }
            collect_block(&nf.body, path, occ);
            path.pop();
        }
        AstStmt::GenericFor(gf) => {
            for e in &gf.iterator {
                collect_expr(e, idx, path, occ);
            }
            path.push((idx, 0, true));
            for &b in &gf.bindings {
                if let AstBindingRef::Local(l) = b {
                    occ.declared_scopes
                        .entry(l)
                        .or_default()
                        .push(DeclaredScope {
                            path: path.clone(),
                            start_stmt_idx: 0,
                        });
                }
            }
            collect_block(&gf.body, path, occ);
            path.pop();
        }
        AstStmt::DoBlock(b) => {
            path.push((idx, 0, false));
            collect_block(b, path, occ);
            path.pop();
        }
        AstStmt::FunctionDecl(decl) => {
            let root = match &decl.target {
                super::super::common::AstFunctionName::Plain(p)
                | super::super::common::AstFunctionName::Method(p, _) => &p.root,
            };
            record_name(root, idx, path, occ);
            record_captures(&decl.func.captured_bindings, idx, path, occ);
        }
        AstStmt::LocalFunctionDecl(decl) => {
            if let AstBindingRef::Local(l) = decl.name {
                occ.declared_scopes
                    .entry(l)
                    .or_default()
                    .push(DeclaredScope {
                        path: path.clone(),
                        start_stmt_idx: idx,
                    });
            }
            record_captures(&decl.func.captured_bindings, idx, path, occ);
        }
        AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Label(_) | AstStmt::Error(_) => {}
    }
}

fn collect_lvalue(lv: &AstLValue, idx: usize, path: &BlockPath, occ: &mut LocalOccurrence) {
    if let AstLValue::Name(name) = lv {
        record_name(name, idx, path, occ);
    }
    traverse_lvalue_children!(lv, borrow = [&], expr(e) => {
        collect_expr(e, idx, path, occ);
    });
}

fn collect_call(call: &AstCallKind, idx: usize, path: &BlockPath, occ: &mut LocalOccurrence) {
    traverse_call_children!(call, iter = iter, borrow = [&], expr(e) => {
        collect_expr(e, idx, path, occ);
    });
}

fn collect_expr(expr: &AstExpr, idx: usize, path: &BlockPath, occ: &mut LocalOccurrence) {
    for node in expr_nodes(expr) {
        match node {
            ExprNode::Expr(AstExpr::Var(name)) => record_name(name, idx, path, occ),
            ExprNode::Function(func) => {
                // 不进入子函数 body（独立作用域），但子函数捕获的父 local 视为在闭包点使用！
                record_captures(&func.captured_bindings, idx, path, occ);
            }
            _ => {}
        }
    }
}

fn record_name(name: &AstNameRef, idx: usize, path: &BlockPath, occ: &mut LocalOccurrence) {
    if let AstNameRef::Local(local) = name {
        occ.sites
            .entry(*local)
            .or_default()
            .push((path.clone(), idx));
    }
}

fn record_captures(
    captures: &BTreeSet<AstBindingRef>,
    idx: usize,
    path: &BlockPath,
    occ: &mut LocalOccurrence,
) {
    for &b in captures {
        if let AstBindingRef::Local(local) = b {
            occ.sites
                .entry(local)
                .or_default()
                .push((path.clone(), idx));
        }
    }
}

fn apply_placements(
    block: &mut AstBlock,
    path: &mut BlockPath,
    placements: &BTreeMap<BlockPath, Vec<(usize, LocalId)>>,
    tbc_locals: &BTreeSet<LocalId>,
    debug_hinted_locals: &BTreeSet<LocalId>,
) {
    // 1. 先递归处理所有子块（此时当前块的语句下标尚未因插入偏移）
    for (idx, stmt) in block.stmts.iter_mut().enumerate() {
        match stmt {
            AstStmt::If(if_stmt) => {
                path.push((idx, 0, false));
                apply_placements(
                    &mut if_stmt.then_block,
                    path,
                    placements,
                    tbc_locals,
                    debug_hinted_locals,
                );
                path.pop();
                if let Some(else_block) = &mut if_stmt.else_block {
                    path.push((idx, 1, false));
                    apply_placements(else_block, path, placements, tbc_locals, debug_hinted_locals);
                    path.pop();
                }
            }
            AstStmt::While(w) => {
                path.push((idx, 0, true));
                apply_placements(&mut w.body, path, placements, tbc_locals, debug_hinted_locals);
                path.pop();
            }
            AstStmt::Repeat(r) => {
                path.push((idx, 0, true));
                apply_placements(&mut r.body, path, placements, tbc_locals, debug_hinted_locals);
                path.pop();
            }
            AstStmt::NumericFor(nf) => {
                path.push((idx, 0, true));
                apply_placements(&mut nf.body, path, placements, tbc_locals, debug_hinted_locals);
                path.pop();
            }
            AstStmt::GenericFor(gf) => {
                path.push((idx, 0, true));
                apply_placements(&mut gf.body, path, placements, tbc_locals, debug_hinted_locals);
                path.pop();
            }
            AstStmt::DoBlock(b) => {
                path.push((idx, 0, false));
                apply_placements(b, path, placements, tbc_locals, debug_hinted_locals);
                path.pop();
            }
            _ => {}
        }
    }

    // 2. 在当前块按语句下标倒序应用声明（就地合并 `x = init` → `local x = init`）
    let Some(mut entries) = placements.get(path).cloned() else {
        return;
    };
    // 按 (stmt_idx 降序, LocalId 升序) 分组
    let mut by_idx: BTreeMap<usize, Vec<LocalId>> = BTreeMap::new();
    for (idx, local) in entries.drain(..) {
        by_idx.entry(idx).or_default().push(local);
    }

    for (stmt_idx, mut locals) in by_idx.into_iter().rev() {
        locals.sort();
        locals.dedup();
        let make_binding = |local: LocalId| AstLocalBinding {
            id: AstBindingRef::Local(local),
            attr: if tbc_locals.contains(&local) {
                AstLocalAttr::Close
            } else {
                AstLocalAttr::None
            },
            is_debug_hinted: debug_hinted_locals.contains(&local),
        };

        // 尝试就地合并多赋值或单赋值：`a, b = f()` → `local a, b = f()`
        if let Some(AstStmt::Assign(assign)) = block.stmts.get(stmt_idx)
            && assign.compound_op.is_none()
            && !assign.targets.is_empty()
            && assign.targets.iter().all(|t| matches!(t, AstLValue::Name(AstNameRef::Local(l)) if locals.contains(l)))
            && assign.targets.len() == locals.len()
        {
            let target_locals: Vec<LocalId> = assign
                .targets
                .iter()
                .map(|t| match t {
                    AstLValue::Name(AstNameRef::Local(l)) => *l,
                    _ => unreachable!(),
                })
                .collect();
            let unique_targets: BTreeSet<LocalId> = target_locals.iter().copied().collect();
            let rhs_mentions_any = target_locals.iter().any(|&l| {
                let name = AstNameRef::Local(l);
                assign.values.iter().any(|v| expr_mentions_name(v, &name))
                    || assign.values.iter().any(|v| expr_captures_local(v, l))
            });
            if unique_targets.len() == target_locals.len() && !rhs_mentions_any {
                let values = match &mut block.stmts[stmt_idx] {
                    AstStmt::Assign(a) => std::mem::take(&mut a.values),
                    _ => unreachable!(),
                };
                block.stmts[stmt_idx] = AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: target_locals.into_iter().map(make_binding).collect(),
                    values,
                }));
                continue;
            }
        }

        // 否则在首次出现之前插入前向声明 `local x`
        let insert_at = stmt_idx.min(block.stmts.len());
        let bindings = locals.into_iter().map(make_binding).collect();
        block.stmts.insert(
            insert_at,
            AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings,
                values: Vec::new(),
            })),
        );
    }
}

fn expr_captures_local(expr: &AstExpr, local: LocalId) -> bool {
    let target = AstBindingRef::Local(local);
    for node in expr_nodes(expr) {
        if let ExprNode::Function(func) = node
            && func.captured_bindings.contains(&target)
        {
            return true;
        }
    }
    false
}

fn expr_reads_local(expr: &AstExpr, local: LocalId) -> bool {
    let name = AstNameRef::Local(local);
    expr_mentions_name(expr, &name) || expr_captures_local(expr, local)
}

fn block_at_path<'a>(root: &'a AstBlock, path: &[(usize, u8, bool)]) -> Option<&'a AstBlock> {
    let mut cur = root;
    for &(stmt_idx, slot, _) in path {
        let stmt = cur.stmts.get(stmt_idx)?;
        cur = match (stmt, slot) {
            (AstStmt::If(i), 0) => &i.then_block,
            (AstStmt::If(i), 1) => i.else_block.as_ref()?,
            (AstStmt::While(w), 0) => &w.body,
            (AstStmt::Repeat(r), 0) => &r.body,
            (AstStmt::NumericFor(nf), 0) => &nf.body,
            (AstStmt::GenericFor(gf), 0) => &gf.body,
            (AstStmt::DoBlock(b), 0) => b,
            _ => return None,
        };
    }
    Some(cur)
}

/// 检查代码块在无条件写回 `local` 之前是否可能先读取或捕获 `local`（用于识别跨循环迭代携带状态的局部变量）。
fn block_reads_local_before_def(block: &AstBlock, local: LocalId) -> bool {
    let target_name = AstNameRef::Local(local);
    for stmt in &block.stmts {
        match stmt {
            AstStmt::Assign(a) => {
                let lvalue_reads = a.targets.iter().any(|t| match t {
                    AstLValue::Name(n) => a.compound_op.is_some() && *n == target_name,
                    AstLValue::FieldAccess(f) => expr_reads_local(&f.base, local),
                    AstLValue::IndexAccess(ia) => {
                        expr_reads_local(&ia.base, local) || expr_reads_local(&ia.index, local)
                    }
                });
                if lvalue_reads || a.values.iter().any(|v| expr_reads_local(v, local)) {
                    return true;
                }
                if a.compound_op.is_none()
                    && a.targets
                        .iter()
                        .any(|t| matches!(t, AstLValue::Name(n) if *n == target_name))
                {
                    return false;
                }
            }
            AstStmt::LocalDecl(d) => {
                if d.values.iter().any(|v| expr_reads_local(v, local)) {
                    return true;
                }
                if d.bindings
                    .iter()
                    .any(|b| b.id == AstBindingRef::Local(local))
                {
                    return false;
                }
            }
            AstStmt::GlobalDecl(d) => {
                if d.values.iter().any(|v| expr_reads_local(v, local)) {
                    return true;
                }
            }
            AstStmt::Return(r) => {
                return r.values.iter().any(|v| expr_reads_local(v, local));
            }
            AstStmt::CallStmt(c) => {
                let reads = match &c.call {
                    AstCallKind::Call(call) => {
                        expr_reads_local(&call.callee, local)
                            || call.args.iter().any(|a| expr_reads_local(a, local))
                    }
                    AstCallKind::MethodCall(m) => {
                        expr_reads_local(&m.receiver, local)
                            || m.args.iter().any(|a| expr_reads_local(a, local))
                    }
                };
                if reads {
                    return true;
                }
            }
            AstStmt::If(i) => {
                if expr_reads_local(&i.cond, local)
                    || block_reads_local_before_def(&i.then_block, local)
                    || i.else_block
                        .as_ref()
                        .is_some_and(|eb| block_reads_local_before_def(eb, local))
                {
                    return true;
                }
                // 若 `then` 与 `else` 两臂均必然无条件定值 `local`（如三元分支赋值），
                // 则该 `if` 之后不再构成“先读后写”，避免把循环内局部误上提到循环外！
                if block_definitely_assigns_local(&i.then_block, local)
                    && i.else_block
                        .as_ref()
                        .is_some_and(|eb| block_definitely_assigns_local(eb, local))
                {
                    return false;
                }
            }
            AstStmt::While(w) => {
                if expr_reads_local(&w.cond, local) || block_reads_local_before_def(&w.body, local)
                {
                    return true;
                }
            }
            AstStmt::Repeat(r) => {
                if block_reads_local_before_def(&r.body, local)
                    || (!block_definitely_assigns_local(&r.body, local)
                        && expr_reads_local(&r.cond, local))
                {
                    return true;
                }
            }
            AstStmt::NumericFor(nf) => {
                if expr_reads_local(&nf.start, local)
                    || expr_reads_local(&nf.limit, local)
                    || expr_reads_local(&nf.step, local)
                    || block_reads_local_before_def(&nf.body, local)
                {
                    return true;
                }
            }
            AstStmt::GenericFor(gf) => {
                if gf.iterator.iter().any(|e| expr_reads_local(e, local))
                    || block_reads_local_before_def(&gf.body, local)
                {
                    return true;
                }
            }
            AstStmt::DoBlock(b) => {
                if block_reads_local_before_def(b, local) {
                    return true;
                }
                if block_definitely_assigns_local(b, local) {
                    return false;
                }
            }
            AstStmt::FunctionDecl(d) => {
                if d.func.captured_bindings.contains(&AstBindingRef::Local(local)) {
                    return true;
                }
            }
            AstStmt::LocalFunctionDecl(d) => {
                if d.func.captured_bindings.contains(&AstBindingRef::Local(local)) {
                    return true;
                }
            }
            AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) => return false,
            AstStmt::Label(_) | AstStmt::Error(_) => {}
        }
    }
    false
}

fn block_definitely_assigns_local(block: &AstBlock, local: LocalId) -> bool {
    let target_name = AstNameRef::Local(local);
    for stmt in &block.stmts {
        match stmt {
            AstStmt::Assign(a)
                if a.compound_op.is_none()
                    && a.targets
                        .iter()
                        .any(|t| matches!(t, AstLValue::Name(n) if *n == target_name)) =>
            {
                return true;
            }
            AstStmt::If(i)
                if block_definitely_assigns_local(&i.then_block, local)
                    && i.else_block
                        .as_ref()
                        .is_some_and(|eb| block_definitely_assigns_local(eb, local)) =>
            {
                return true;
            }
            AstStmt::DoBlock(b) if block_definitely_assigns_local(b, local) => return true,
            AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) | AstStmt::Return(_) => {
                return false;
            }
            _ => {}
        }
    }
    false
}
