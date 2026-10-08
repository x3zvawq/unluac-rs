//! 验证外围源码在 Luau O2 下保留原调用和运算。
//! 每个函数单独收集写入身份，动态算术与 builtin 折叠证明共用同一作用域事实。

use super::*;

pub(super) struct PlainExpressions<'a> {
    callees: &'a BTreeMap<crate::hir::LocalId, crate::hir::HirProtoRef>,
    nonconstant: BTreeSet<AstNameRef>,
    stable_loops: BTreeSet<AstBindingRef>,
    runtime_body: bool,
}

impl<'a> PlainExpressions<'a> {
    pub(super) fn new(callees: &'a BTreeMap<crate::hir::LocalId, crate::hir::HirProtoRef>) -> Self {
        Self {
            callees,
            nonconstant: BTreeSet::new(),
            stable_loops: BTreeSet::new(),
            runtime_body: false,
        }
    }
    pub(super) fn expr(&self, expr: &AstExpr) -> bool {
        match expr {
            AstExpr::Nil
            | AstExpr::Boolean(_)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_) => true,
            AstExpr::Var(AstNameRef::Global(name))
                if matches!(name.text.as_str(), "print" | "assert" | "table" | "error") =>
            {
                // error 作为元方法值只保留原全局读取，getFunctionExpr 不解析全局函数体。
                true
            }
            AstExpr::Var(AstNameRef::Local(local)) => !self.callees.contains_key(local),
            AstExpr::Var(AstNameRef::SyntheticLocal(_)) => true,
            AstExpr::Var(AstNameRef::Param(_) | AstNameRef::Upvalue(_)) => true,
            AstExpr::Call(call) => {
                if matches!(&call.callee, AstExpr::FieldAccess(field)
                if field.field == "floor" && matches!(&field.base,
                    AstExpr::Var(AstNameRef::Global(name)) if name.text == "math"))
                {
                    return self.runtime_arithmetic(expr);
                }
                // pinned Luau 的 select("#", ...) 对当前变参直接计数，对固定值保留 CALL；
                // 两者都不参与函数解析或参数常量折叠，开放尾部仍由 plain_values 拒绝。
                if matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "select")
                {
                    return call.required_luau_inlining.is_none()
                        && call.method_key.is_none()
                        && matches!(call.args.as_slice(), [AstExpr::String(marker), value]
                        if marker.as_utf8() == Some("#")
                            && (matches!(value, AstExpr::VarArg)
                                || self.expr(value) && open_tail_unchanged(value)));
                }
                // pcall 不参与 getFunctionExpr；作为其首实参传递的函数值不会额外内联。
                if matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "pcall")
                {
                    return call.required_luau_inlining.is_none()
                        && call.method_key.is_none()
                        && matches!(call.args.first(), Some(AstExpr::Var(AstNameRef::Local(_))))
                        && self.values(&call.args[1..], false);
                }
                call.required_luau_inlining.is_none()
                    && call.method_key.is_none()
                    && (opaque_callee(call)
                    || matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name))
                        if matches!(name.text.as_str(), "getmetatable" | "setmetatable" | "type" | "tostring"))
                    // rawequal/rawset 不参加 BuiltinFolding；限定各自固定参数数目。
                    || matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name))
                        if (name.text == "rawequal" && call.args.len() == 2 || name.text == "rawset" && call.args.len() == 3))
                    // max 只在所有参数均为数值常量时折叠；不透明索引调用排除此条件。
                    || (matches!(&call.callee, AstExpr::FieldAccess(field)
                        if field.field == "max" && matches!(&field.base,
                            AstExpr::Var(AstNameRef::Global(name)) if name.text == "math"))
                        && call.args.iter().any(|arg| matches!(arg, AstExpr::Call(inner)
                            if matches!(inner.callee, AstExpr::IndexAccess(_))))))
                    && (!matches!(call.callee, AstExpr::IndexAccess(_)) || self.expr(&call.callee))
                    && self.values(&call.args, false)
            }
            AstExpr::FunctionExpr(function) => self.function(function),
            AstExpr::SingleValue(value) => self.expr(value),
            AstExpr::FieldAccess(field) => self.expr(&field.base),
            AstExpr::IndexAccess(index) => self.expr(&index.base) && self.expr(&index.index),
            AstExpr::Unary(unary) => {
                matches!(unary.op, AstUnaryOpKind::Length | AstUnaryOpKind::Not)
                    && self.expr(&unary.expr)
            }
            AstExpr::Binary(binary)
                if matches!(
                    binary.op,
                    AstBinaryOpKind::Sub | AstBinaryOpKind::Mul | AstBinaryOpKind::Div
                ) || binary.op == AstBinaryOpKind::Mod
                    && !matches!(binary.lhs, AstExpr::Var(AstNameRef::Local(_)))
                    || binary.op == AstBinaryOpKind::Add
                        && !matches!(binary.rhs, AstExpr::Integer(_) | AstExpr::Number(_)) =>
            {
                self.runtime_arithmetic(expr)
            }
            AstExpr::Binary(binary) => {
                (matches!(
                    binary.op,
                    AstBinaryOpKind::Eq
                        | AstBinaryOpKind::Lt
                        | AstBinaryOpKind::Le
                        | AstBinaryOpKind::Gt
                        | AstBinaryOpKind::Ge
                        | AstBinaryOpKind::Concat
                ) || (binary.op == AstBinaryOpKind::Add
                    && matches!(binary.rhs, AstExpr::Integer(_) | AstExpr::Number(_)))
                    || binary.op == AstBinaryOpKind::Mod
                        && matches!(binary.lhs, AstExpr::Var(AstNameRef::Local(_)))
                        && matches!(binary.rhs, AstExpr::Integer(_) | AstExpr::Number(_)))
                    && self.expr(&binary.lhs)
                    && self.expr(&binary.rhs)
            }
            AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
                self.expr(&logical.lhs) && self.expr(&logical.rhs)
            }
            AstExpr::TableConstructor(table) => {
                table
                .fields
                .iter()
                .enumerate()
                .all(|(index, field)| match field {
                    AstTableField::Array(value) => {
                        // getFunctionExpr 不解析表内函数值；后续索引调用仍保留原 CALL。
                        (matches!(value, AstExpr::Var(AstNameRef::Local(local)) if self.callees.contains_key(local))
                            || self.expr(value))
                            && (index + 1 < table.fields.len() || open_tail_unchanged(value))
                    }
                    AstTableField::Record(record) => {
                        (match &record.key {
                            AstTableKey::Name(_) => true,
                            AstTableKey::Expr(key) => self.expr(key),
                        }) && self.expr(&record.value)
                    }
                })
            }
            _ => false,
        }
    }

    pub(super) fn values(&self, values: &[AstExpr], fixed_one: bool) -> bool {
        values.iter().enumerate().all(|(index, value)| {
            self.expr(value)
                && (fixed_one || index + 1 < values.len() || open_tail_unchanged(value))
        })
    }

    pub(super) fn assign(&self, assign: &AstAssign) -> bool {
        // 原位更新使该 local 在 pinned ConstantFolding 中保持非恒定；floor 不能被编译期求值。
        if let ([AstLValue::Name(AstNameRef::Local(target))], [AstExpr::Call(call)]) =
            (assign.targets.as_slice(), assign.values.as_slice())
            && call.required_luau_inlining.is_none()
            && call.method_key.is_none()
            && matches!(&call.callee, AstExpr::FieldAccess(field)
            if field.field == "floor" && matches!(&field.base, AstExpr::Var(AstNameRef::Global(name)) if name.text == "math"))
            && matches!(call.args.as_slice(), [AstExpr::Binary(binary)] if binary.op == AstBinaryOpKind::Div
            && binary.lhs == AstExpr::Var(AstNameRef::Local(*target))
            && matches!(binary.rhs, AstExpr::Integer(_) | AstExpr::Number(_)))
            && !self.callees.contains_key(target)
        {
            return true;
        }
        assign.targets.iter().all(|target| match target {
            AstLValue::Name(name) => self.expr(&AstExpr::Var(name.clone())),
            AstLValue::FieldAccess(field) => self.expr(&field.base),
            AstLValue::IndexAccess(index) => self.expr(&index.base) && self.expr(&index.index),
        }) && self.values(&assign.values, assign.targets.len() == assign.values.len())
    }

    pub(super) fn function(&self, function: &AstFunctionExpr) -> bool {
        if function.is_vararg
        || function.named_vararg.is_some()
        || function.captured_bindings.iter().any(
            |binding| matches!(binding, AstBindingRef::Local(local) if self.callees.contains_key(local)),
        )
    {
        return false;
    }
        // LocalId 属于 child 自身；进入函数前已排除 required callee 的跨层捕获。
        let locals = BTreeMap::new();
        let mut scope = PlainExpressions::new(&locals);
        scope.nonconstant = crate::ast::written_names(&function.body);
        // 独立函数体的参数在运行时入口写入；外围调用是否再次内联由调用点合同另证。
        scope
            .nonconstant
            .extend(function.params.iter().copied().map(AstNameRef::Param));
        if let Some((_, loops)) = constant_control::CostAnalysis::new(function).runtime_summary() {
            scope.stable_loops = loops;
            scope.runtime_body = true;
        }
        scope.block(&function.body)
    }

    pub(super) fn field_function(&self, decl: &AstFunctionDecl) -> bool {
        let path = match &decl.target {
            AstFunctionName::Plain(path)
                if !path.fields.is_empty() || matches!(path.root, AstNameRef::Global(_)) =>
            {
                path
            }
            AstFunctionName::Method(path, _) => path,
            _ => return false,
        };
        self.expr(&AstExpr::Var(path.root.clone())) && self.function(&decl.func)
    }

    pub(super) fn block(&self, block: &AstBlock) -> bool {
        block.stmts.iter().all(|stmt| match stmt {
            AstStmt::LocalDecl(decl) => {
                self.values(&decl.values, decl.bindings.len() == decl.values.len())
            }
            AstStmt::Assign(assign) => self.assign(assign),
            AstStmt::Return(ret) => self.values(&ret.values, false),
            AstStmt::CallStmt(stmt) => matches!(&stmt.call, AstCallKind::Call(call)
            if call.required_luau_inlining.is_none() && call.method_key.is_none()
                // table.insert 的丢弃结果调用不参与 O2 常量折叠或函数解析；
                // 限定固定双实参，不能把它加入允许开放返回的 opaque callee 集合。
                && (opaque_callee(call) || (table_callee(call, "insert") && call.args.len() == 2)
                    || matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name))
                    if name.text == "assert" || name.text == "print" || name.text == "rawset" && call.args.len() == 3))
                && self.values(&call.args, false)),
            AstStmt::Repeat(loop_) => {
                (matches!(loop_.cond, AstExpr::Var(AstNameRef::Param(_)))
                    || self.runtime_body && self.expr(&loop_.cond)) && self.block(&loop_.body)
            }
            AstStmt::While(loop_) => self.runtime_body && self.expr(&loop_.cond) && self.block(&loop_.body),
            AstStmt::NumericFor(loop_) => self.stable_loops.contains(&loop_.binding)
                && self.expr(&loop_.start) && self.expr(&loop_.limit) && self.expr(&loop_.step)
                && self.block(&loop_.body),
            AstStmt::GenericFor(loop_) => {
                matches!(
                    loop_.iterator.as_slice(),
                    [AstExpr::Var(AstNameRef::Local(_) | AstNameRef::Param(_))]
                ) && self.block(&loop_.body)
            }
            AstStmt::Break | AstStmt::Continue => true,
            AstStmt::LocalFunctionDecl(decl) => self.function(&decl.func),
            AstStmt::FunctionDecl(decl) => self.field_function(decl),
            AstStmt::If(branch) => {
                self.expr(&branch.cond)
                    && self.block(&branch.then_block)
                    && branch
                        .else_block
                        .as_ref()
                        .is_none_or(|block| self.block(block))
            }
            _ => false,
        })
    }

    fn runtime_arithmetic(&self, expr: &AstExpr) -> bool {
        // 只在完整算术子树的入口检查一次；失败后不对各后缀重复扫描。
        // 未证明的名字可以是常量操作数，但每个算术节点均须依赖参数或运行时写入。
        runtime_arithmetic(expr, &|name| match name {
            AstNameRef::Local(local) if self.callees.contains_key(local) => None,
            AstNameRef::Local(_) | AstNameRef::Param(_) | AstNameRef::Upvalue(_) => {
                Some(self.nonconstant.contains(name))
            }
            _ => None,
        }) == Some(true)
    }
}
