//! 恢复建表安装方法、返回递归闭包或按值捕获参数的 Luau 工厂展开体。
//!
//! 以原闭包模板、创建方式、捕获绑定及连续写入配对现存工厂；结果 COPY 与高槽根
//! 随整个后缀一起重放，不能只因两个函数体看起来相同就替换闭包对象。

use super::*;
use crate::hir::common::{HirClosureCreation, HirClosureExpr, HirOperationSources, HirTableAccess};

mod nested;

#[derive(Clone)]
pub(super) enum Factory {
    Snapshot(snapshots::Factory),
    Table {
        table: Box<HirTableConstructor>,
        method: crate::LuaString,
        shared: usize,
    },
    Recursive {
        shared: usize,
    },
    NestedValue {
        intermediate: usize,
        result: usize,
        inner: LocalId,
    },
}

impl Factory {
    pub(super) fn key(&self) -> (HirLuauInliningBody, crate::LuaString) {
        match self {
            Self::Snapshot(factory) => (
                HirLuauInliningBody::SnapshotClosureFactory {
                    template: factory.template,
                },
                "".into(),
            ),
            Self::Table { method, shared, .. } => (
                HirLuauInliningBody::TableFactory { shared: *shared },
                method.clone(),
            ),
            Self::Recursive { shared } => (
                HirLuauInliningBody::ClosureFactory { shared: *shared },
                "".into(),
            ),
            Self::NestedValue {
                intermediate,
                result,
                ..
            } => (
                HirLuauInliningBody::NestedValueClosureFactory {
                    intermediate: *intermediate,
                    result: *result,
                },
                "".into(),
            ),
        }
    }
    pub(super) fn nested_inner(&self) -> Option<LocalId> {
        match self {
            Self::NestedValue { inner, .. } => Some(*inner),
            _ => None,
        }
    }
}

pub(super) use nested::restore_body as restore_nested_body;

fn installation(stmt: &HirStmt) -> Option<(&HirTableAccess, &HirExpr)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([HirLValue::TableAccess(access)], [value], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    Some((access, value))
}

fn shared(closure: &HirClosureExpr) -> Option<usize> {
    let Some(HirClosureCreation::MayReuse { template }) = closure.creation else {
        return None;
    };
    closure.captures.is_empty().then_some(template)
}

fn same_fields(left: &HirTableConstructor, right: &HirTableConstructor) -> bool {
    left.fields.len() == right.fields.len()
        && left.fields.iter().zip(&right.fields).all(|(left, right)| {
            let (
                crate::hir::common::HirTableField::Record(left),
                crate::hir::common::HirTableField::Record(right),
            ) = (left, right)
            else {
                return false;
            };
            left.key == right.key
                && match (&left.value, &right.value) {
                    (HirExpr::Number(left), HirExpr::Number(right)) => {
                        left.to_bits() == right.to_bits()
                    }
                    (left, right) => left == right,
                }
        })
}

pub(super) fn body(
    proto: &HirProto,
    promotion: &[ProtoPromotionFacts],
    protos: &[HirProto],
) -> Option<Factory> {
    let facts = &promotion[proto.id.index()];
    if let Some(factory) = snapshots::body(proto, facts, protos) {
        return Some(Factory::Snapshot(factory));
    }
    if let Some(factory) = nested::body(proto, promotion, protos) {
        return Some(factory);
    }
    if !proto.signature.is_vararg
        && proto.params.is_empty()
        && proto.upvalues.len() == 1
        && proto.children.len() == 1
        && let [HirStmt::Return(ret)] = proto.body.stmts.as_slice()
        && let ([HirExpr::Closure(closure)], None) = (ret.values.fixed.as_slice(), &ret.values.tail)
        && matches!(closure.captures.as_slice(), [capture] if capture.mode == HirCaptureMode::ByReference && capture.binding == HirBinding::Upvalue(crate::hir::UpvalueId(0)))
        && let Some(HirClosureCreation::MayReuse { template }) = closure.creation
        && recursive_child(&protos[closure.proto.index()])
        && facts.operation_result_home(closure.source_site?) == Some(HomeSlotKey::new(0, 0))
        && matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(range) if range.start.index()==0 && range.len==1)
    {
        return Some(Factory::Recursive { shared: template });
    }
    if proto.signature.is_vararg
        || !proto.params.is_empty()
        || !proto.upvalues.is_empty()
        || proto.children.len() != 1
        || proto.failure.is_some()
    {
        return None;
    }
    let [initial, install, HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let (local, HirExpr::TableConstructor(table)) = scalar_local(initial)? else {
        return None;
    };
    let (access, HirExpr::Closure(closure)) = installation(install)? else {
        return None;
    };
    let HirExpr::String(method) = &access.key else {
        return None;
    };
    let layout = facts.native_table_write_layout(access)?;
    if !matches!(initial, HirStmt::LocalDecl(_))
        || !matches!(table.allocation, HirTableAllocation::LuauTemplate { .. })
        || table.fields.len() > 4 || table.trailing_multivalue.is_some()
        || table.fields.iter().any(|field| !matches!(field,
            crate::hir::common::HirTableField::Record(record)
                if matches!(record.value, HirExpr::Nil | HirExpr::Boolean(_) | HirExpr::Integer(_) | HirExpr::Number(_) | HirExpr::String(_))))
        || facts.allocation_result_home(table) != Some(HomeSlotKey::new(0,0))
        || access.base != HirExpr::LocalRef(local)
        || facts.operation_result_home(closure.source_site?) != Some(HomeSlotKey::new(1,0))
        || layout.base != HomeSlotKey::new(0,0) || layout.value != Some(HomeSlotKey::new(1,0))
        || layout.key.is_some()
        || !method_child(&protos[closure.proto.index()])
        || ret.values.fixed != [HirExpr::LocalRef(local)] || ret.values.tail.is_some()
        || !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(range) if range.start.index()==0 && range.len==1)
    { return None; }
    Some(Factory::Table {
        table: table.clone(),
        method: method.clone(),
        shared: shared(closure)?,
    })
}

fn method_child(proto: &HirProto) -> bool {
    if proto.signature.is_vararg
        || proto.params.len() != 2
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
    {
        return false;
    }
    let [assign, HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return false;
    };
    let Some((target, HirExpr::Binary(add))) = installation(assign) else {
        return false;
    };
    let HirExpr::TableAccess(read) = &add.lhs else {
        return false;
    };
    let receiver = HirExpr::ParamRef(proto.params[0]);
    matches!(target.key, HirExpr::String(_))
        && target.base == receiver
        && read.base == receiver
        && read.key == target.key
        && add.op == crate::hir::HirBinaryOpKind::Add
        && add.rhs == HirExpr::ParamRef(proto.params[1])
        && ret.values.fixed == [receiver]
        && ret.values.tail.is_none()
}

fn recursive_child(proto: &HirProto) -> bool {
    if proto.signature.is_vararg
        || proto.params.len() != 1
        || proto.upvalues.len() != 1
        || !proto.children.is_empty()
    {
        return false;
    }
    let Some((HirStmt::Return(ret), prefix)) = proto.body.stmts.split_last() else {
        return false;
    };
    let Some(tail) = &ret.values.tail else {
        return false;
    };
    let HirExpr::Call(call) = tail.as_expr() else {
        return false;
    };
    !call.is_method() && call.args.is_empty() && ret.values.fixed.is_empty()
        && call.callee == HirExpr::UpvalueRef(crate::hir::UpvalueId(0))
        && prefix.iter().all(|stmt| matches!(stmt, HirStmt::CallStmt(stmt)
            if matches!(&stmt.call.callee, HirExpr::GlobalRef(global) if global.key.as_utf8()==Some("assert"))
            && matches!(stmt.call.args.fixed.as_slice(), [HirExpr::Binary(binary)]
                if matches!(binary.op, crate::hir::HirBinaryOpKind::Eq | crate::hir::HirBinaryOpKind::Lt | crate::hir::HirBinaryOpKind::Le | crate::hir::HirBinaryOpKind::Gt | crate::hir::HirBinaryOpKind::Ge)
                && matches!(binary.lhs, HirExpr::ParamRef(_) | HirExpr::Integer(_) | HirExpr::Number(_))
                && matches!(binary.rhs, HirExpr::ParamRef(_) | HirExpr::Integer(_) | HirExpr::Number(_)))
            && stmt.call.args.tail.is_none()))
}

/// 直接返回新闭包的函数只执行一次创建；参数按值捕获，不存在 cell 写入。
pub(super) fn value_body_key(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    protos: &[HirProto],
) -> Option<(HirLuauInliningBody, crate::LuaString)> {
    if proto.signature.is_vararg
        || proto.params.len() != 1
        || !proto.upvalues.is_empty()
        || proto.children.len() != 1
        || proto.failure.is_some()
    {
        return None;
    }
    let [HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let ([HirExpr::Closure(closure)], None) = (ret.values.fixed.as_slice(), &ret.values.tail)
    else {
        return None;
    };
    let Some(HirClosureCreation::Fresh { template }) = closure.creation else {
        return None;
    };
    if !matches!(closure.captures.as_slice(), [capture] if capture.mode == HirCaptureMode::ByValue
        && capture.binding == HirBinding::Param(proto.params[0]))
        || !value_result_body(&protos[closure.proto.index()])
        || facts.operation_result_home(closure.source_site?) != Some(HomeSlotKey::new(1, 0))
        || !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(range) if range.start.index() == 1 && range.len == 1)
    {
        return None;
    }
    Some((
        HirLuauInliningBody::ValueClosureFactory { template },
        "".into(),
    ))
}

fn value_result_body(proto: &HirProto) -> bool {
    fn expression(value: &HirExpr) -> bool {
        match value {
            HirExpr::ParamRef(_) | HirExpr::UpvalueRef(_) => true,
            HirExpr::Unary(unary) => expression(&unary.expr),
            HirExpr::Binary(binary) => expression(&binary.lhs) && expression(&binary.rhs),
            _ => false,
        }
    }
    // 编译要求作用于整个 chunk；子函数中的额外 CALL 或常量计算可能在 O2 再次
    // 内联/折叠，不能仅凭工厂的返回形状签证。运行时参数/捕获值的运算保持原位。
    !proto.signature.is_vararg
        && proto.children.is_empty()
        && proto.mutable_upvalues.is_empty()
        && matches!(proto.body.stmts.as_slice(), [HirStmt::Return(ret)]
            if matches!((ret.values.fixed.as_slice(), &ret.values.tail), ([value], None) if expression(value)))
}

/// 常量实参内联后由 compileExprFunction 在结果槽之上准备一次 CAPTURE VAL。
/// 只消费闭包的独占捕获读；原同槽其它写、debug 身份和引用捕获不随调用退休。
fn value_plans(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let mut reads = BTreeMap::<LocalId, usize>::new();
    let mut writes = BTreeMap::<LocalId, usize>::new();
    visit_stmts(
        &context.proto.body.stmts,
        &mut (
            BindingReadCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    *reads.entry(local).or_default() += 1;
                }
            }),
            BindingWriteCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    *writes.entry(local).or_default() += 1;
                }
            }),
        ),
    );
    let mut plans = Vec::new();
    for (start, window) in context.proto.body.stmts.windows(2).enumerate() {
        let candidate = (|| {
            let (input, value @ HirExpr::Integer(number)) = scalar_local(&window[0])? else {
                return None;
            };
            let (result, HirExpr::Closure(closure)) = scalar_local(&window[1])? else {
                return None;
            };
            let Some(HirClosureCreation::Fresh { template }) = closure.creation else {
                return None;
            };
            let callee = context.expanded_callees?.get(&(
                HirLuauInliningBody::ValueClosureFactory { template },
                "".into(),
            ))?;
            let base = facts.trusted_local_home_slot(result)?;
            let source = closure.source_site?;
            let input_home = HomeSlotKey::new(base.slot() + 1, 0);
            if !(-32768..=32767).contains(number)
                || callee.declaration >= start
                || callee.creation.proto != source.proto
                || !matches!(window[0], HirStmt::LocalDecl(_))
                || !matches!(window[1], HirStmt::LocalDecl(_))
                || reads.get(&input) != Some(&1)
                || writes.get(&input) != Some(&1)
                || context.proto.local_debug_hints[input.index()].is_some()
                || context.proto.local_debug_scopes[input.index()].is_some()
                || context
                    .proto
                    .inline_dispositions
                    .local(input)
                    .must_preserve()
                || !matches!(closure.captures.as_slice(), [capture] if capture.mode == HirCaptureMode::ByValue && capture.binding == HirBinding::Local(input))
                || facts.trusted_local_home_slot(input) != Some(input_home)
                || !facts
                    .complete_local_definition_write_homes(input)
                    .iter()
                    .copied()
                    .eq([input_home])
                || facts.operation_result_home(source) != Some(base)
                || context.closed.contains(&input_home)
                || context.closed.contains(&base)
            {
                return None;
            }
            let mut plan = invocation(callee, source, base, result, start, start + 1);
            let HirExpr::Call(call) = &mut plan.values.fixed[0] else {
                unreachable!()
            };
            call.args.fixed.push(value.clone());
            Some(plan)
        })();
        plans.extend(candidate);
    }
    plans
}

pub(super) fn plans(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let mut plans = value_plans(context, facts);
    plans.extend(nested::plans(context, facts));
    for (index, stmt) in context.proto.body.stmts.iter().enumerate() {
        let candidate = (|| {
            let (result, HirExpr::Closure(closure)) = scalar_local(stmt)? else {
                return None;
            };
            let Some(HirClosureCreation::MayReuse { template }) = closure.creation else {
                return None;
            };
            let callee = context.expanded_callees?.get(&(
                HirLuauInliningBody::ClosureFactory { shared: template },
                "".into(),
            ))?;
            let base = facts.trusted_local_home_slot(result)?;
            let source = closure.source_site?;
            if callee.declaration >= index
                || callee.creation.proto != source.proto
                || !matches!(stmt, HirStmt::LocalDecl(_))
                || !matches!(closure.captures.as_slice(), [capture] if capture.mode==HirCaptureMode::ByValue && capture.binding==HirBinding::Local(callee.local))
                || facts.operation_result_home(source) != Some(base)
            {
                return None;
            }
            Some(invocation(callee, source, base, result, index, index))
        })();
        plans.extend(candidate);
    }
    for start in 0..context.proto.body.stmts.len() {
        let window = &context.proto.body.stmts[start..];
        let candidate = (|| {
            let (object, HirExpr::TableConstructor(table)) = scalar_local(&window[0])? else {
                return None;
            };
            let (closure, access, copy_index) = if let Some((function, HirExpr::Closure(closure))) =
                window.get(1).and_then(scalar_local)
            {
                let (access, value) = installation(window.get(2)?)?;
                if *value != HirExpr::LocalRef(function) {
                    return None;
                }
                (closure, access, 3)
            } else {
                let (access, HirExpr::Closure(closure)) = installation(window.get(1)?)? else {
                    return None;
                };
                (closure, access, 2)
            };
            let (result, copy) = scalar_local(window.get(copy_index)?)?;
            let HirExpr::String(method) = &access.key else {
                return None;
            };
            let key = (
                HirLuauInliningBody::TableFactory {
                    shared: shared(closure)?,
                },
                method.clone(),
            );
            let callee = context.expanded_callees?.get(&key)?;
            let Factory::Table { table: factory, .. } = callee.factory.as_ref()? else {
                return None;
            };
            let base = facts.trusted_local_home_slot(result)?;
            let object_home = HomeSlotKey::new(base.slot() + 1, 0);
            let function_home = HomeSlotKey::new(base.slot() + 2, 0);
            let HirOperationSources::Single(source) = table.sources else {
                return None;
            };
            let HirOperationSources::Single(write) = access.sources else {
                return None;
            };
            let layout = facts.native_table_write_layout(access)?;
            let debug_object = context.proto.local_debug_scopes[object.index()]
                .and_then(|scope| context.proto.debug_scopes[scope].as_ref())
                .is_some_and(|scope| {
                    context.proto.local_debug_hints[object.index()] == callee.result_name
                        && callee.result_name.is_some()
                        && scope.initializer_temp == facts.operation_result_temp(source)
                        && scope.initializer_end_instr == Some(source.instr)
                        && scope
                            .end_instr
                            .is_some_and(|end| end.index() == write.instr.index() + 2)
                });
            if callee.declaration >= start
                || callee.creation.proto != source.proto
                || !same_fields(table, factory)
                || table.allocation != factory.allocation
                || table.trailing_multivalue.is_some()
                || !table.implicit_template_fields.is_empty()
                || access.base != HirExpr::LocalRef(object)
                || *copy != HirExpr::LocalRef(object)
                || facts.allocation_result_home(table) != Some(object_home)
                || facts.trusted_local_home_slot(object) != Some(object_home)
                || facts.operation_result_home(closure.source_site?) != Some(function_home)
                || closure.source_site?.instr.index() != source.instr.index() + 1
                || write.instr.index() != source.instr.index() + 2
                || layout.base != object_home
                || layout.value != Some(function_home)
                || layout.key.is_some()
                || (base.slot()..=function_home.slot()).any(|slot| {
                    (context.barred.contains(&HomeSlotKey::new(slot, 0))
                        && !(debug_object && slot == object_home.slot()))
                        || context.closed.contains(&HomeSlotKey::new(slot, 0))
                })
            {
                return None;
            }
            // 返回 COPY 位于字段写之后，不属于 allocation 的紧邻 MOVE 链；
            // 当前无改写的对象 binding 与两个可信 home 保留此独立写回。
            if !(matches!(&window[copy_index], HirStmt::Assign(assign) if !assign.is_phi_transfer && assign.initializer_merge_transaction.is_none())
                || matches!(&window[copy_index], HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_none()))
            {
                return None;
            }
            Some(invocation(
                callee,
                source,
                base,
                result,
                start,
                start + copy_index,
            ))
        })();
        plans.extend(candidate);
    }
    plans
}

pub(super) fn invocation(
    callee: &Callee,
    source: crate::hir::HirSourceSite,
    base: HomeSlotKey,
    result: LocalId,
    start: usize,
    sink: usize,
) -> Plan {
    Plan {
        start,
        sink,
        base,
        values: vec![factory_call(
            callee.local,
            Some(source),
            HirValuePack::default(),
        )]
        .into(),
        result_locals: vec![result],
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: (start..sink).collect(),
    }
}

pub(super) fn factory_call(
    callee: LocalId,
    source: Option<crate::hir::HirSourceSite>,
    args: HirValuePack,
) -> HirExpr {
    HirExpr::Call(Box::new(HirCallExpr {
        source_site: None,
        required_luau_inlining: source,
        callee: HirExpr::LocalRef(callee),
        args,
        method: HirMethodCall::None,
        fastcall: None,
        method_key: None,
        argument_roots: Vec::new(),
        frame_root_ends: Vec::new(),
        callee_root_handoff: None,
        method_rewrite_transaction: None,
        plain_method_syntax: false,
        boolean_prewrite_arguments: Vec::new(),
    }))
}
