//! 根据小型标准库签名表为实参提供命名提示。只消费直接调用及当前 AST 的显式写入，
//! 不追踪库别名，不把标准库拼写当作函数身份或运行语义证明。

use std::collections::BTreeSet;

use crate::ast::visit::{AstVisitor, visit_block};
use crate::ast::{
    AstCallExpr, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstGlobalBindingTarget,
    AstLValue, AstModule, AstNameRef, AstStmt,
};
use crate::hir::HirProtoRef;

use super::{
    FunctionHints, NameSource, final_binding_from_name_ref, register_binding_hint,
    register_param_hint,
};

struct Signature {
    root: &'static str,
    member: &'static str,
    required: usize,
    params: &'static [&'static str],
}

impl Signature {
    const fn new(
        root: &'static str,
        member: &'static str,
        required: usize,
        params: &'static [&'static str],
    ) -> Self {
        Self {
            root,
            member,
            required,
            params,
        }
    }
}

// 参数位置来自 Lua reference manual 的 Standard Libraries；名称展开缩写以便阅读。
// https://www.lua.org/manual/5.4/manual.html#6
// 这里只列各受支持方言共有的稳定形状。可选尾参数用 required 表示，中间可选参数
// 必须拆成不相交的 arity 条目，不能把 table.insert(list, value) 的 value 命名为 position。
const SIGNATURES: &[Signature] = &[
    Signature::new("os", "date", 0, &["format", "time"]),
    Signature::new("os", "difftime", 2, &["end_time", "start_time"]),
    Signature::new("string", "sub", 2, &["text", "start_index", "end_index"]),
    Signature::new("string", "byte", 1, &["text", "start_index", "end_index"]),
    Signature::new(
        "string",
        "find",
        2,
        &["text", "pattern", "start_index", "plain"],
    ),
    Signature::new("string", "match", 2, &["text", "pattern", "start_index"]),
    Signature::new(
        "string",
        "gsub",
        3,
        &["text", "pattern", "replacement", "limit"],
    ),
    Signature::new(
        "table",
        "concat",
        1,
        &["list", "separator", "start_index", "end_index"],
    ),
    Signature::new("table", "insert", 2, &["list", "value"]),
    Signature::new("table", "insert", 3, &["list", "position", "value"]),
    Signature::new("table", "remove", 1, &["list", "position"]),
    Signature::new("table", "sort", 1, &["list", "compare"]),
    Signature::new("math", "random", 1, &["upper"]),
    Signature::new("math", "random", 2, &["lower", "upper"]),
    Signature::new("tonumber", "", 1, &["value", "base"]),
    Signature::new("rawget", "", 2, &["tbl", "key"]),
    Signature::new("rawset", "", 3, &["tbl", "key", "value"]),
    Signature::new("pairs", "", 1, &["tbl"]),
    Signature::new("ipairs", "", 1, &["list"]),
];

pub(super) fn collect_hints(module: &AstModule, hints: &mut [FunctionHints]) {
    let mut writes = LibraryWrites::default();
    visit_block(&module.body, &mut writes);
    let mut collector = SignatureHints {
        hints,
        writes: &writes,
        functions: vec![module.entry_function],
    };
    visit_block(&module.body, &mut collector);
}

// 只做一次模块级写入收集。命名无需证明调用顺序；出现显式替换就放弃该库提示，
// 包括子函数里的写入。别名写入、宿主注入等动态行为不在这份只读语法事实的能力内。
#[derive(Default)]
struct LibraryWrites(BTreeSet<String>);

impl LibraryWrites {
    fn record(&mut self, name: &AstNameRef) {
        if let AstNameRef::Global(global) = name {
            self.0.insert(global.text.clone());
        }
    }
}

impl AstVisitor for LibraryWrites {
    fn visit_lvalue(&mut self, target: &AstLValue) {
        match target {
            AstLValue::Name(name) => self.record(name),
            AstLValue::FieldAccess(access) => {
                if let Some(name) = direct_global(&access.base) {
                    self.record(name);
                }
            }
            AstLValue::IndexAccess(access) => {
                if let Some(name) = direct_global(&access.base) {
                    self.record(name);
                }
            }
        }
    }

    fn visit_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::FunctionDecl(decl) => {
                let (AstFunctionName::Plain(path) | AstFunctionName::Method(path, _)) =
                    &decl.target;
                self.record(&path.root);
            }
            AstStmt::GlobalDecl(decl) if !decl.values.is_empty() => {
                for binding in &decl.bindings {
                    if let AstGlobalBindingTarget::Name(name) = &binding.target {
                        self.0.insert(name.text.clone());
                    }
                }
            }
            _ => {}
        }
    }
}

fn direct_global(expr: &AstExpr) -> Option<&AstNameRef> {
    match expr {
        AstExpr::Var(name @ AstNameRef::Global(_)) => Some(name),
        _ => None,
    }
}

struct SignatureHints<'a> {
    hints: &'a mut [FunctionHints],
    writes: &'a LibraryWrites,
    functions: Vec<HirProtoRef>,
}

impl SignatureHints<'_> {
    fn call(&mut self, call: &AstCallExpr) {
        if call.method_key.is_some()
            || matches!(
                call.args.last(),
                Some(AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg)
            )
        {
            // 开放尾包宽度未知，不能据 AST operand 数判断重载；也不把 colon 的接收者算成普通实参。
            return;
        }
        let Some((root, member)) = direct_call_path(&call.callee) else {
            return;
        };
        if self.writes.0.contains(root) {
            return;
        }
        let Some(signature) = SIGNATURES.iter().find(|signature| {
            signature.root == root
                && signature.member == member
                && (signature.required..=signature.params.len()).contains(&call.args.len())
        }) else {
            return;
        };
        let function = *self
            .functions
            .last()
            .expect("entry function is always present");
        for (arg, name) in call.args.iter().zip(signature.params) {
            let AstExpr::Var(binding) = arg else {
                continue;
            };
            if let AstNameRef::Param(param) = binding {
                register_param_hint(
                    function,
                    *param,
                    name,
                    NameSource::LibrarySignature,
                    self.hints,
                );
            } else if let Some(binding) = final_binding_from_name_ref(binding) {
                register_binding_hint(
                    function,
                    binding,
                    (*name).to_owned(),
                    NameSource::LibrarySignature,
                    self.hints,
                );
            }
        }
    }
}

impl AstVisitor for SignatureHints<'_> {
    fn visit_expr(&mut self, expr: &AstExpr) {
        if let AstExpr::Call(call) = expr {
            self.call(call);
        }
    }

    fn visit_call(&mut self, call: &AstCallKind) {
        if let AstCallKind::Call(call) = call {
            self.call(call);
        }
    }

    fn visit_function_expr(&mut self, function: &AstFunctionExpr) -> bool {
        self.functions.push(function.function);
        true
    }

    fn leave_function_expr(&mut self, _function: &AstFunctionExpr) {
        self.functions.pop();
    }
}

fn direct_call_path(callee: &AstExpr) -> Option<(&str, &str)> {
    let (root, member) = match callee {
        AstExpr::Var(AstNameRef::Global(name)) => return Some((&name.text, "")),
        AstExpr::FieldAccess(access) => (&access.base, access.field.as_str()),
        AstExpr::IndexAccess(access) => {
            let AstExpr::String(member) = &access.index else {
                return None;
            };
            (&access.base, member.as_utf8()?)
        }
        _ => return None,
    };
    let AstExpr::Var(AstNameRef::Global(root)) = root else {
        return None;
    };
    Some((&root.text, member))
}
