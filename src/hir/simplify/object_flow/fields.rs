//! 新建表的确定字段身份与原物理根窗口投影。
//!
//! 字段读取只消费当前未逃逸 allocation 的确定写入；它不是 may-contents 的反向推断。
//! 例如 `t={nodes={4,9}}; return t.nodes[2]` 只向出口传递数字，不暴露 nodes。
//! 构造器吸收独立producer前，要求allocation到原同home精确终点（无证书时到函数出口）
//! 从未逃逸或持有未知资源。字段清除不能撤回历史；终点RHS事件也属于窗口。当前只
//! 分析函数直线前缀；遇到控制流时仅接受此前已结束的原根窗口，不把前缀末尾当物理
//! 根终点，也不撤销未吸收 owner 的原结束事实。完整函数才能使用自然出口作终点。

use super::*;
use crate::hir::common::{HirBinaryOpKind, HirUnaryOpKind};
use crate::hir::promotion::ProtoPromotionFacts;
use crate::hir::simplify::root_lifetimes::{
    RootLifetimeFacts, RootOverwritePolicy, collect_call_root_lifetimes,
};
use crate::hir::value_facts::value_facts_with;
use crate::value_semantics::results::LuaValueFacts;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) enum FieldKey {
    Boolean(bool),
    Integer(i64),
    String(crate::LuaString),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum KnownValue {
    Key(FieldKey),
    Scalar(LuaValueFacts),
    Table(ObjectId),
}

impl KnownValue {
    pub(super) fn object(&self) -> Option<ObjectId> {
        match self {
            Self::Table(object) => Some(*object),
            _ => None,
        }
    }

    fn facts(&self) -> LuaValueFacts {
        match self {
            Self::Key(FieldKey::Boolean(value)) => LuaValueFacts::boolean(*value),
            Self::Key(FieldKey::Integer(_)) => LuaValueFacts::NUMERIC,
            Self::Key(FieldKey::String(_)) => LuaValueFacts::STRING,
            Self::Scalar(facts) => *facts,
            Self::Table(_) => LuaValueFacts::RESOURCE,
        }
    }
}

#[derive(Clone, Default)]
pub(super) struct FieldFacts {
    bindings: BTreeMap<HirBinding, (KnownValue, usize)>,
    reference_captured: BTreeSet<HirBinding>,
    values: BTreeMap<ObjectId, BTreeMap<FieldKey, KnownValue>>,
    observed_at: BTreeMap<ObjectId, usize>,
    parents: BTreeMap<ObjectId, BTreeSet<ObjectId>>,
    statement_index: usize,
    observation_epoch: usize,
}

impl FieldFacts {
    pub(super) fn mark_observed(&mut self, object: ObjectId) {
        let mut pending = vec![object];
        while let Some(object) = pending.pop() {
            if let std::collections::btree_map::Entry::Vacant(entry) =
                self.observed_at.entry(object)
            {
                entry.insert(self.statement_index);
                if let Some(parents) = self.parents.get(&object) {
                    pending.extend(parents);
                }
            }
        }
    }

    pub(super) fn record_contents(&mut self, owner: ObjectId, children: &BTreeSet<ObjectId>) {
        let mut observed = false;
        for &child in children {
            self.parents.entry(child).or_default().insert(owner);
            observed |= self.observed_at.contains_key(&child);
        }
        // 已公开对象被更晚写入新容器时，容器从当前store起可观察，不能回溯到child的旧时间。
        if observed {
            self.mark_observed(owner);
        }
    }

    fn unobserved_through(&self, object: ObjectId, end: usize) -> bool {
        self.observed_at
            .get(&object)
            .is_none_or(|index| *index > end)
    }
    pub(super) fn publishes_binding(&self, binding: HirBinding) -> bool {
        self.reference_captured.contains(&binding)
    }
    pub(super) fn observation_epoch(&self) -> usize {
        self.observation_epoch
    }
    pub(super) fn observe(&mut self) {
        self.observation_epoch += 1;
    }
    pub(super) fn invalidate_values(&mut self) {
        self.values.clear();
    }
    pub(super) fn install(&mut self, binding: HirBinding, value: Option<KnownValue>) {
        if let Some(value) = value {
            self.bindings
                .insert(binding, (value, self.observation_epoch));
        } else {
            self.bindings.remove(&binding);
        }
    }
}

fn atom(expr: &HirExpr, state: &RootState) -> Option<KnownValue> {
    let fields = state.fields.as_ref()?;
    if let Some(binding) = HirBinding::from_expr(expr) {
        let (value, epoch) = fields.bindings.get(&binding)?;
        return (!(fields.reference_captured.contains(&binding)
            || matches!(binding, HirBinding::Upvalue(_)))
            || *epoch == fields.observation_epoch)
            .then(|| value.clone());
    }
    Some(match expr {
        HirExpr::Boolean(value) => KnownValue::Key(FieldKey::Boolean(*value)),
        HirExpr::Integer(value) => KnownValue::Key(FieldKey::Integer(*value)),
        HirExpr::Number(value) => KnownValue::Key(FieldKey::Integer(
            crate::value_semantics::table::integer_table_key(*value)?,
        )),
        HirExpr::String(value) => KnownValue::Key(FieldKey::String(value.clone())),
        HirExpr::TableConstructor(table) => KnownValue::Table(ObjectId::table(table)),
        HirExpr::TableAccess(access) => {
            let KnownValue::Table(object) = known_value(&access.base, state)? else {
                return None;
            };
            if state.escaped.contains(&object) {
                return None;
            }
            let KnownValue::Key(key) = known_value(&access.key, state)? else {
                return None;
            };
            fields.values.get(&object)?.get(&key)?.clone()
        }
        HirExpr::Unary(unary)
            if unary.op == HirUnaryOpKind::Length
                && matches!(known_value(&unary.expr, state), Some(KnownValue::Table(object))
                if !state.escaped.contains(&object)) =>
        {
            KnownValue::Scalar(LuaValueFacts::NUMERIC)
        }
        _ => return None,
    })
}

pub(super) fn known_value(expr: &HirExpr, state: &RootState) -> Option<KnownValue> {
    state.fields.as_ref()?;
    atom(expr, state).or_else(|| {
        let facts = value_facts_with(expr, &|expr| atom(expr, state).map(|value| value.facts()));
        facts.is_gc_inert().then_some(KnownValue::Scalar(facts))
    })
}

pub(super) fn operator_is_plain(expr: &HirExpr, state: &RootState) -> bool {
    match expr {
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Length => {
            matches!(known_value(&unary.expr, state), Some(KnownValue::Table(object))
                if !state.escaped.contains(&object))
        }
        HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq => {
            [&binary.lhs, &binary.rhs].into_iter().all(|operand| {
                known_value(operand, state).is_some_and(|value| match value {
                    KnownValue::Table(object) => !state.escaped.contains(&object),
                    KnownValue::Key(_) => true,
                    KnownValue::Scalar(facts) => matches!(
                        facts,
                        LuaValueFacts::NIL
                            | LuaValueFacts::BOOLEAN
                            | LuaValueFacts::NUMERIC
                            | LuaValueFacts::STRING
                    ),
                })
            })
        }
        _ => false,
    }
}

pub(super) fn store(
    tables: &BTreeSet<ObjectId>,
    key: Option<&HirExpr>,
    value: Option<&HirExpr>,
    state: &mut RootState,
) {
    if state.fields.is_none() {
        return;
    }
    let key = key.and_then(|key| known_value(key, state));
    let value = value.map_or(Some(KnownValue::Scalar(LuaValueFacts::NIL)), |value| {
        known_value(value, state)
    });
    let fields = state.fields.as_mut().expect("field projection enabled");
    for &table in tables {
        if key.is_none() || value.is_none() {
            fields.mark_observed(table);
        }
        let values = fields.values.entry(table).or_default();
        if tables.len() == 1
            && let Some(KnownValue::Key(key)) = &key
        {
            if let Some(value) = &value {
                values.insert(key.clone(), value.clone());
            } else {
                values.remove(key);
            }
        } else {
            values.clear();
        }
    }
}

pub(super) fn construct(table: &HirTableConstructor, state: &mut RootState, stable: bool) {
    if state.fields.is_none() {
        return;
    }
    let object = ObjectId::table(table);
    let mut values = BTreeMap::new();
    let mut tainted = table.trailing_multivalue.is_some();
    let mut array_index = 0;
    let mut has_array = false;
    let mut has_record = false;
    let mut exact_keys = true;
    for field in &table.fields {
        let (key, value) = match field {
            HirTableField::Array(value) => {
                array_index += 1;
                has_array = true;
                (Some(KnownValue::Key(FieldKey::Integer(array_index))), value)
            }
            HirTableField::Record(record) => {
                has_record = true;
                (known_value(&record.key, state), &record.value)
            }
        };
        let value = known_value(value, state);
        tainted |= key.is_none() || value.is_none();
        exact_keys &= matches!(key, Some(KnownValue::Key(_)));
        if let (Some(KnownValue::Key(key)), Some(value)) = (key, value) {
            values.insert(key, value);
        }
    }
    // 混合 constructor 的 array 存储由延后 SETLIST 决定，不能按表面字段顺序签确定值。
    if has_array && has_record || table.trailing_multivalue.is_some() || !stable || !exact_keys {
        values.clear();
    }
    let fields = state.fields.as_mut().expect("field projection enabled");
    fields.values.insert(object, values);
    if tainted || !stable {
        fields.mark_observed(object);
    }
}

/// allocation许可携带HIR binding身份；同binding的每次allocation都须通过其原根窗口。
/// Local赋值许可另绑定原stmt快照，消费前立即投影为block稳定id；不跨改写保留地址。
/// 一次流式状态转移同时服务所有候选，最后沿 may-containment 的反向边传播拒绝；
/// may 边只扩大拒绝集，绝不签发强字段持有证书。
#[derive(Default)]
pub(in crate::hir::simplify) struct PrivateAllocationFacts {
    bindings: BTreeSet<HirBinding>,
    overwrites: BTreeSet<usize>,
}

impl PrivateAllocationFacts {
    pub(in crate::hir::simplify) fn analyze(
        block: &HirBlock,
        context: RootAnalysisContext<'_>,
        promotion: &ProtoPromotionFacts,
    ) -> Self {
        let prefix_end = block
            .stmts
            .iter()
            .position(|stmt| {
                !matches!(
                    stmt,
                    HirStmt::LocalDecl(_)
                        | HirStmt::Assign(_)
                        | HirStmt::GlobalDecl(_)
                        | HirStmt::LocalRootRelease(_)
                        | HirStmt::CallStmt(_)
                        | HirStmt::TableSetList(_)
                        | HirStmt::Return(_)
                        | HirStmt::ErrNil(_)
                )
            })
            .unwrap_or(block.stmts.len());
        let complete = prefix_end == block.stmts.len();
        let stmts = &block.stmts[..prefix_end];
        // 私有性只用于把独立分配收进另一个 seed。单 seed 的数组批次没有此需求，
        // 不为其每个元素建立字段身份（大型 EXTRAARG 数组也走普通批次恢复）。
        if stmts
            .iter()
            .filter(|stmt| match stmt {
                HirStmt::LocalDecl(decl) => decl
                    .values
                    .fixed
                    .iter()
                    .any(|value| matches!(value, HirExpr::TableConstructor(_))),
                HirStmt::Assign(assign) => assign
                    .values
                    .fixed
                    .iter()
                    .any(|value| matches!(value, HirExpr::TableConstructor(_))),
                _ => false,
            })
            .take(2)
            .count()
            < 2
        {
            return Self::default();
        }
        let captures = closure_captures_in_block(block);
        let mut state = RootState {
            fields: Some(FieldFacts {
                reference_captured: captures
                    .values()
                    .flat_map(|captures| captures.iter())
                    .filter(|capture| capture.mode == HirCaptureMode::ByReference)
                    .map(|capture| capture.binding)
                    .collect(),
                ..FieldFacts::default()
            }),
            ..RootState::default()
        };
        let root_ends = collect_call_root_lifetimes(
            &RootLifetimeFacts::new(stmts, promotion, context.safety),
            promotion,
            context.safety,
            true,
            |_| true,
            |_| RootOverwritePolicy::Reuse,
        );
        let mut ends_by_producer = BTreeMap::<usize, Option<usize>>::new();
        for index in 0..stmts.len() {
            for owner in root_ends.owner_overwrites(index) {
                let Some(HirStmt::Assign(assign)) = block.stmts.get(owner.root_index()) else {
                    continue;
                };
                let [HirLValue::Temp(temp)] = assign.targets.as_slice() else {
                    continue;
                };
                if !matches!(
                    assign.values.fixed.as_slice(),
                    [HirExpr::TableConstructor(_)]
                ) || promotion.trusted_temp_home_slot(*temp) != Some(owner.home())
                {
                    continue;
                }
                ends_by_producer
                    .entry(owner.root_index())
                    .and_modify(|end| {
                        if *end != Some(index) {
                            *end = None;
                        }
                    })
                    .or_insert(Some(index));
            }
        }
        let mut owners = BTreeMap::<HirBinding, Vec<(ObjectId, Option<usize>)>>::new();
        let mut overwrites = Vec::new();
        for (index, stmt) in stmts.iter().enumerate() {
            state
                .fields
                .as_mut()
                .expect("field projection enabled")
                .statement_index = index;
            // 覆盖前读取旧值身份，最后与整个窗口的bad集核对。仅凭“新RHS是fresh table”
            // 不能把旧资源根的释放提前到父initializer（尤其是相邻调用/GC观察）。
            if let HirStmt::Assign(assign) = stmt
                && let [HirLValue::Local(local)] = assign.targets.as_slice()
                && matches!(
                    assign.values.fixed.as_slice(),
                    [HirExpr::TableConstructor(_)]
                )
                && assign.values.tail.is_none()
                && let Some(old) = known_value(&HirExpr::LocalRef(*local), &state)
            {
                overwrites.push((std::ptr::from_ref(stmt).addr(), old.object()));
            }
            update_state_for_stmt(stmt, &mut state, &captures, context.effects, context.safety);
            let mut record = |binding, value: Option<&HirExpr>| {
                // 已物化 local 的同 binding 写是 HIR 中显式保留的值终点，不反推
                // 原寄存器。写入 RHS 的观察已计入当前 index，未知后缀不提供许可。
                if matches!(binding, HirBinding::Local(_))
                    && let Some(previous) = owners
                        .get_mut(&binding)
                        .and_then(|values| values.last_mut())
                    && previous.1.is_none()
                {
                    previous.1 = Some(index);
                }
                if let Some(HirExpr::TableConstructor(table)) = value {
                    owners.entry(binding).or_default().push((
                        ObjectId::table(table),
                        ends_by_producer.get(&index).copied().flatten(),
                    ));
                }
            };
            match stmt {
                HirStmt::LocalDecl(decl) => {
                    for (i, &local) in decl.bindings.iter().enumerate() {
                        record(HirBinding::Local(local), decl.values.result_source(i));
                    }
                }
                HirStmt::Assign(assign) => {
                    for (i, target) in assign.targets.iter().enumerate() {
                        if let Some(binding) = HirBinding::from_lvalue(target) {
                            record(binding, assign.values.result_source(i));
                        }
                    }
                }
                _ => {}
            }
        }
        let fields = state.fields.as_ref().expect("field projection enabled");
        Self {
            bindings: owners
                .into_iter()
                .filter_map(|(binding, objects)| {
                    objects
                        .iter()
                        .all(|(object, end)| {
                            end.or(complete.then_some(prefix_end))
                                .is_some_and(|end| fields.unobserved_through(*object, end))
                        })
                        .then_some(binding)
                })
                .collect(),
            overwrites: overwrites
                .into_iter()
                .filter_map(|(stmt, old)| {
                    old.is_none_or(|object| {
                        complete && fields.unobserved_through(object, prefix_end)
                    })
                    .then_some(stmt)
                })
                .collect(),
        }
    }

    pub(in crate::hir::simplify) fn contains(&self, binding: HirBinding) -> bool {
        self.bindings.contains(&binding)
    }

    pub(in crate::hir::simplify) fn permits_initializer_overwrite(&self, stmt: &HirStmt) -> bool {
        self.overwrites.contains(&std::ptr::from_ref(stmt).addr())
    }
}
