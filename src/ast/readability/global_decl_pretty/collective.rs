//! 这个子模块负责把“缺失 global 声明”收成最小 collective gate。
//!
//! 在 Lua 5.5 里，stripped chunk 常常只能证明“这里必须重新打开某种 global gate 才能
//! 重新编译”，却未必能证明源码是逐名 `global a, b` 还是 collective `global *`。
//! 这里的 owner 只处理这种 AST 级 canonical 选择：
//! - 优先把终端语句尾巴收成最小 `do + global *` / `global<const> *`
//! - 它不会去猜 block 外是否也存在同一批 global
//! - 也不会跨越 label/goto 之类高风险控制流去硬包一层 `do`
//!
//! 例子：
//! - `local ok = ...; local left = math.max(...); return left`
//!   会被收成 `local ok = ...; do global<const> *; local left = ...; return left end`

use std::collections::BTreeSet;

use crate::ast::common::{
    AstBlock, AstExpr, AstFunctionExpr, AstGlobalAttr, AstLValue, AstLocalAttr, AstLocalBinding,
    AstLocalFunctionDecl, AstLocalOrigin, AstNameRef, AstStmt,
};

use super::super::binding_flow::{BindingRefSet, stmt_references_binding_set};
use super::super::visit::{self, AstVisitor};
use super::super::walk::BlockKind;
use super::facts::MissingGlobals;
use super::insert::build_wildcard_global_decl;

pub(super) fn try_wrap_missing_collective_suffix(
    block: &mut AstBlock,
    kind: BlockKind,
    missing: &MissingGlobals,
) -> bool {
    if matches!(kind, BlockKind::ModuleBody) {
        return false;
    }

    let Some((attr, names)) = collective_candidate(missing) else {
        return false;
    };
    let start = block
        .stmts
        .iter()
        .position(|stmt| stmt_mentions_any_missing_global(stmt, &names));
    let Some(start) = start else {
        return false;
    };
    let end = block
        .stmts
        .iter()
        .rposition(|stmt| stmt_mentions_any_missing_global(stmt, &names));
    let Some(mut end) = end else {
        return false;
    };

    loop {
        let bindings = collect_declared_bindings(&block.stmts[start..=end]);
        let binding_refs = BindingRefSet::from_bindings(&bindings);
        let Some(next_offset) = block.stmts[(end + 1)..]
            .iter()
            .position(|stmt| stmt_references_binding_set(stmt, &binding_refs))
        else {
            break;
        };
        end += next_offset + 1;
    }

    if end + 1 != block.stmts.len() {
        // 候选拒绝[SemanticBarrier:Scope]：非终端区间包进 `do` 会让其中 local 在后续语句前离开作用域；例如后缀外 `use(local_from_range)` 将失去绑定。
        return false;
    }
    if !suffix_is_safe_to_wrap(&block.stmts[start..]) {
        return false;
    }

    let suffix = block.stmts.split_off(start);
    let mut inner_stmts = Vec::with_capacity(suffix.len() + 1);
    inner_stmts.push(build_wildcard_global_decl(attr));
    inner_stmts.extend(suffix);
    block
        .stmts
        .push(AstStmt::DoBlock(Box::new(AstBlock { stmts: inner_stmts })));
    true
}

fn collective_candidate(missing: &MissingGlobals) -> Option<(AstGlobalAttr, BTreeSet<String>)> {
    match (missing.none.is_empty(), missing.const_.is_empty()) {
        (true, false) => Some((
            AstGlobalAttr::Const,
            missing.const_.iter().cloned().collect(),
        )),
        (false, true) => Some((AstGlobalAttr::None, missing.none.iter().cloned().collect())),
        _ => {
            // 候选拒绝[ProofIncomplete]：可写与 const 缺失名混合时，一个 wildcard gate 无法表达两种属性；尚未实现双层最小 gate/逐名声明的 canonical 代价证明。
            None
        }
    }
}

fn suffix_is_safe_to_wrap(stmts: &[AstStmt]) -> bool {
    if stmts
        .iter()
        .any(|stmt| matches!(stmt, AstStmt::Goto(_) | AstStmt::Label(_)))
    {
        // 候选拒绝[SemanticBarrier:ControlFlow]：外部 goto 可能跳入新增 global gate/local 作用域，或 suffix 内跳转跨越新边界；没有全 block 跳转配对证明时不能包 `do`。
        return false;
    }
    if stmts
        .iter()
        .any(|stmt| matches!(stmt, AstStmt::Break | AstStmt::Continue))
    {
        // 候选拒绝[ProofIncomplete]：`do` 本身不拥有 loop-control，直接 break/continue 很可能可保留；当前缺少 goto-syntax-safety/owner 联合证明，整类保守拒绝。
        return false;
    }
    true
}

fn collect_declared_bindings(stmts: &[AstStmt]) -> Vec<AstLocalBinding> {
    let mut bindings = Vec::new();
    for stmt in stmts {
        match stmt {
            AstStmt::LocalDecl(local_decl) => bindings.extend(local_decl.bindings.iter().cloned()),
            AstStmt::LocalFunctionDecl(function_decl) => {
                bindings.push(synthetic_binding_for_local_function(function_decl.as_ref()));
            }
            AstStmt::Assign(_)
            | AstStmt::CallStmt(_)
            | AstStmt::Return(_)
            | AstStmt::GlobalDecl(_)
            | AstStmt::If(_)
            | AstStmt::While(_)
            | AstStmt::Repeat(_)
            | AstStmt::NumericFor(_)
            | AstStmt::GenericFor(_)
            | AstStmt::DoBlock(_)
            | AstStmt::FunctionDecl(_)
            | AstStmt::Break
            | AstStmt::Continue
            | AstStmt::Goto(_)
            | AstStmt::Label(_)
            | AstStmt::Error(_) => {}
        }
    }
    bindings
}

fn synthetic_binding_for_local_function(function_decl: &AstLocalFunctionDecl) -> AstLocalBinding {
    AstLocalBinding {
        id: function_decl.name,
        attr: AstLocalAttr::None,
        origin: AstLocalOrigin::Recovered,
    }
}

fn stmt_mentions_any_missing_global(stmt: &AstStmt, names: &BTreeSet<String>) -> bool {
    let mut visitor = MissingGlobalStmtVisitor {
        names,
        found: false,
    };
    visit::visit_stmt(stmt, &mut visitor);
    visitor.found
}

struct MissingGlobalStmtVisitor<'a> {
    names: &'a BTreeSet<String>,
    found: bool,
}

impl AstVisitor for MissingGlobalStmtVisitor<'_> {
    fn visit_expr(&mut self, expr: &AstExpr) {
        if let AstExpr::Var(AstNameRef::Global(global)) = expr
            && self.names.contains(&global.text)
        {
            self.found = true;
        }
    }

    fn visit_lvalue(&mut self, lvalue: &AstLValue) {
        if let AstLValue::Name(AstNameRef::Global(global)) = lvalue
            && self.names.contains(&global.text)
        {
            self.found = true;
        }
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}
