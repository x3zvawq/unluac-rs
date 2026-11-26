//! 顺序消费表达式栈、条件树提升、$O(N)$ 表构造器聚合、方法调用与多值包恢复。

use crate::LuaString;
use crate::analysis::{BlockId, EffectClass, ValueId};
use crate::parser::RawLiteralConst;
use crate::transformer::{
    AccessBase, AccessKey, BranchCond, BranchPredicate, BranchSubject, CallInstr, CallKind,
    CondOperand, ConstRef, GetTableKind, InstrRef, LowInstr, Reg, ResultPack, TableAllocation,
    TailCallInstr, UpvalueOperand, ValueOperand, ValuePack,
};

use super::super::common::{
    AstAssign, AstBinaryExpr, AstBinaryOpKind, AstCallExpr, AstCallKind, AstCallStmt, AstExpr,
    AstFieldAccess, AstGlobalName, AstIndexAccess, AstLValue, AstLogicalExpr, AstMethodCallExpr,
    AstNameRef, AstRecordField, AstStmt, AstTableConstructor, AstTableField, AstTableKey,
    AstUnaryExpr, AstUnaryOpKind, UpvalueId,
};
use super::super::structure::CondExpr;
use super::{ProtoLifter, expr_mentions_name, wrap_single_value_if_needed};

/// 挂起在当前基本块中的未冲刷表达式项。
#[derive(Debug, Clone)]
pub(super) struct PendingExpr {
    pub reg: Reg,
    pub val: Option<ValueId>,
    pub anchor: InstrRef,
    pub expr: AstExpr,
    pub effect: EffectClass,
    /// 该项被压入 pending 栈时的单调递增求值序号。
    pub order: usize,
    pub is_building_table: bool,
    /// 该表构造器是否允许吸收紧随的 `SetTable`（非纯空 PUC `{}`）。
    pub accepts_set_table: bool,
    /// 是否为 Luau `DUPTABLE` 预填键模板（允许按同名键就地替换 0 占位，禁止追加模板外新键）。
    pub is_luau_template: bool,
    /// Luau `NEWTABLE` 预分配字段容量上限（`array_capacity + hash_capacity`）；超出后停止吸收以保留原 rehash / `pairs()` 次序。
    pub luau_max_fields: Option<usize>,
    /// Luau 纯哈希 `NEWTABLE`（`array_capacity == 0 && hash_capacity > 0`）强制使用显式 `["k"] = v` 键，
    /// 防止重编译退化为 `DUPTABLE` 或激活顺序整数数组预分配。
    pub luau_force_index_keys: bool,
    /// 是否为 LuaJIT `TNEW`（连续 1..N 整数键吸收为列表字段，保持数组容量语义）。
    pub is_luajit_indexed: bool,
    /// 是否为 LuaJIT `TDUP` 模板表（允许用后续运行期值原地填充模板中的 nil 占位）。
    pub is_luajit_template: bool,
    /// 已吸收过 `SetList`（数组部分）的表禁止继续吸收后续 `SetTable`，防止重编译时键赋值被排到数组批写之前。
    pub table_sealed_by_setlist: bool,
    /// O(1) 追踪正在构造的表已有多少个 `AstTableField::Array` 项，避免 262k 元素超大表出现 O(N^2) 扫描。
    pub array_field_count: usize,
    /// 与正在构造的 `TableConstructor.fields` 一一对应的求值序号（用于还原交错列表/记录构造器顺序）。
    pub field_orders: Vec<usize>,
    pub open_producer: Option<InstrRef>,
    /// 该项源自 `GetTableKind::Method`（保留接收者寄存器与方法名便于恢复 `obj:m()`）。
    pub method_lookup: Option<(Reg, LuaString)>,
}

impl<'a> ProtoLifter<'a> {
    /// 冲刷全部挂起表达式为显式赋值语句（保证跨控制流/跨副作用顺序 100% 精确）。
    pub(super) fn flush_all_pending(&mut self, out: &mut Vec<AstStmt>) {
        let items = std::mem::take(&mut self.pending);
        for item in items {
            let target = self.name_for_pending(&item);
            out.push(AstStmt::Assign(Box::new(AstAssign {
                targets: vec![AstLValue::Name(target)],
                values: vec![item.expr],
                compound_op: None,
            })));
        }
    }

    /// 冲刷影响或位于指定寄存器之前的挂起表达式。
    pub(super) fn flush_pending_for_reg(&mut self, reg: Reg, out: &mut Vec<AstStmt>) {
        if let Some(pos) = self.pending.iter().rposition(|p| p.reg == reg) {
            let drain_count = pos + 1;
            let flushed: Vec<PendingExpr> = self.pending.drain(..drain_count).collect();
            for item in flushed {
                let target = self.name_for_pending(&item);
                out.push(AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(target)],
                    values: vec![item.expr],
                    compound_op: None,
                })));
            }
        }
    }

    /// 写入某个寄存器前，若挂起栈中存在读取该寄存器的延迟表达式（或同槽旧未消费项），先行冲刷。
    pub(super) fn flush_before_reg_write(&mut self, iref: InstrRef, dst: Reg, out: &mut Vec<AstStmt>) {
        if self.pending.is_empty() {
            return;
        }
        let target_name = self.existing_name_for_def_at(iref, dst);
        if let Some(pos) = self.pending.iter().rposition(|p| {
            p.reg == dst
                || target_name
                    .as_ref()
                    .is_some_and(|name| expr_mentions_name(&p.expr, name))
        }) {
            let flushed: Vec<PendingExpr> = self.pending.drain(..=pos).collect();
            for item in flushed {
                let name = self.name_for_pending(&item);
                out.push(AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(name)],
                    values: vec![item.expr],
                    compound_op: None,
                })));
            }
        }
    }

    /// 单结果定值：可内联则压入顺序消费栈，否则直接落地为赋值语句。
    pub(super) fn emit_single_def(
        &mut self,
        iref: InstrRef,
        dst: Reg,
        expr: AstExpr,
        out: &mut Vec<AstStmt>,
    ) {
        let val = self.analysis.ssa.instr_def_value(iref, dst);
        let instr_effect = self.analysis.dataflow.effects[iref.index()];
        let expr_has_effect = super::expr_may_have_side_effect(&expr);
        let effect = if expr_has_effect {
            EffectClass::MayObserveOrWrite
        } else {
            instr_effect
        };
        let is_method_load = matches!(
            &self.proto.instrs[iref.index()],
            LowInstr::GetTable(gt) if gt.kind == GetTableKind::Method
        );

        // 表达式嵌套深度护栏：超过安全深度（64 层）时自动将中间结果落地为局部，
        // 避免对抗性超长链（如数千连环 `a()()...` / `a+a+...`）引发 Rust 递归栈溢出或触发 Lua `LUAI_MAXCCALLS` 解析上限！
        const MAX_PENDING_EXPR_DEPTH: usize = 64;
        let must_materialize = val.is_none_or(|v| {
            self.materialized_values.contains(&v) || self.analysis.ssa.use_count(v) == 0
        }) || expr_depth_exceeds(&expr, MAX_PENDING_EXPR_DEPTH);

        // 写寄存器前冲刷同槽冲突
        self.flush_before_reg_write(iref, dst, out);

        if must_materialize {
            let is_unused = val.is_some_and(|v| {
                self.analysis.ssa.use_count(v) == 0 && !self.materialized_values.contains(&v)
            });
            if is_unused {
                // 纯无用死常量/死读取直接跳过；若表达式是 Call/MethodCall（例如 `x = f(); x = g()` 的第一句），
                // 必须保留为独立 CallStmt，绝不丢弃副作用也不制造多余 local！
                if !expr_has_effect && effect == EffectClass::Pure {
                    return;
                }
                if matches!(expr, AstExpr::Call(_) | AstExpr::MethodCall(_)) {
                    self.flush_all_pending(out);
                    out.push(AstStmt::CallStmt(Box::new(AstCallStmt {
                        call: expr_to_call_kind(expr),
                    })));
                    return;
                }
            }
            self.flush_all_pending(out);
            let target = self.name_for_def_at(iref, dst);
            out.push(AstStmt::Assign(Box::new(AstAssign {
                targets: vec![AstLValue::Name(target)],
                values: vec![expr],
                compound_op: None,
            })));
            return;
        }

        let method_lookup = if is_method_load
            && let LowInstr::GetTable(gt) = &self.proto.instrs[iref.index()]
            && let AccessBase::Reg(self_reg) = gt.base
        {
            match &expr {
                AstExpr::FieldAccess(fa) => Some((self_reg, LuaString::from(fa.field.as_str()))),
                AstExpr::IndexAccess(ia) if matches!(ia.index, AstExpr::String(_)) => {
                    let AstExpr::String(key) = &ia.index else {
                        unreachable!()
                    };
                    Some((self_reg, key.clone()))
                }
                _ => None,
            }
        } else {
            None
        };

        let order = self.alloc_eval_order();
        self.pending.push(PendingExpr {
            reg: dst,
            val,
            anchor: iref,
            expr,
            effect,
            order,
            is_building_table: false,
            accepts_set_table: false,
            is_luau_template: false,
            luau_max_fields: None,
            luau_force_index_keys: false,
            is_luajit_indexed: false,
            is_luajit_template: false,
            table_sealed_by_setlist: false,
            array_field_count: 0,
            field_orders: Vec::new(),
            open_producer: None,
            method_lookup,
        });
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_new_table_def(
        &mut self,
        iref: InstrRef,
        dst: Reg,
        table_expr: AstExpr,
        accepts_set_table: bool,
        is_luau_template: bool,
        luau_max_fields: Option<usize>,
        luau_force_index_keys: bool,
        is_luajit_indexed: bool,
        is_luajit_template: bool,
        out: &mut Vec<AstStmt>,
    ) {
        let val = self.analysis.ssa.instr_def_value(iref, dst);
        self.flush_before_reg_write(iref, dst, out);
        let (init_len, init_array_count) = match &table_expr {
            AstExpr::TableConstructor(c) => (
                c.fields.len(),
                c.fields
                    .iter()
                    .filter(|f| matches!(f, AstTableField::Array(_)))
                    .count(),
            ),
            _ => (0, 0),
        };
        let order = self.alloc_eval_order();
        // 即使 NewTable 的结果后续要落为 local，也先留在 pending 栈顶让连续 SetTable/SetList 线性吸收！
        self.pending.push(PendingExpr {
            reg: dst,
            val,
            anchor: iref,
            expr: table_expr,
            effect: EffectClass::Pure,
            order,
            is_building_table: true,
            accepts_set_table,
            is_luau_template,
            luau_max_fields,
            luau_force_index_keys,
            is_luajit_indexed,
            is_luajit_template,
            table_sealed_by_setlist: false,
            array_field_count: init_array_count,
            field_orders: vec![0; init_len],
            open_producer: None,
            method_lookup: None,
        });
    }

    /// 判断表达式在外部副作用（如 `GETTABLE` / `CALL`）面前是否完全不可变：
    /// 纯字面量，以及未被闭包按引用捕获的局部/形参读取绝不会被外部调用或元方法篡改。
    fn expr_is_invariant_across_effects(&self, expr: &AstExpr) -> bool {
        if expr_is_pure_literal(expr) {
            return true;
        }
        match expr {
            AstExpr::Var(AstNameRef::Param(pid)) => {
                let reg = Reg(pid.index());
                !self
                    .analysis
                    .ssa
                    .ref_captured_slots
                    .iter()
                    .any(|s| s.reg == reg)
            }
            AstExpr::Var(AstNameRef::Local(lid)) => self
                .local_slots
                .get(lid.index())
                .and_then(|s| *s)
                .is_none_or(|slot| !self.analysis.ssa.ref_captured_slots.contains(&slot)),
            _ => false,
        }
    }

    /// 尝试从挂起栈中弹出某个寄存器的延迟表达式；如果中间阻隔了不可越过的副作用项
    /// 或者该表构造器需要物化给后续多次引用，则先行冲刷再返回变量引用。
    pub(super) fn resolve_reg_expr(
        &mut self,
        iref: InstrRef,
        reg: Reg,
        out: &mut Vec<AstStmt>,
    ) -> AstExpr {
        if let Some(pos) = self.pending.iter().rposition(|p| p.reg == reg) {
            let must_keep_var = self.pending[pos].is_building_table
                && self.pending[pos]
                    .val
                    .is_some_and(|v| self.materialized_values.contains(&v));
            if !must_keep_var {
                // 若该项恰在栈顶，直接 O(1) 弹出！
                if pos + 1 == self.pending.len() {
                    let item = self.pending.pop().unwrap();
                    return item.expr;
                }
                // 若该项之上的挂起项不会与本项发生求值/写后读冲突，可安全抽离；
                // - 若本项可能写状态（`MayObserveOrWrite`），它仅能跨过纯不可变字面量，防止跨越变量读取；
                // - 若本项本身是纯表达式/纯表构造（`Pure`），可安全跨过上方其它纯表构造或纯表达式，
                //   彻底避免 `local t1 = {...}; ...; local t6 = {...}; return t1..t6` 每轮重编译只剥离 1 层的慢收敛！
                let item_may_write = self.pending[pos].effect == EffectClass::MayObserveOrWrite;
                let above_safe = self.pending[pos + 1..].iter().all(|p| {
                    if item_may_write {
                        !p.is_building_table && self.expr_is_invariant_across_effects(&p.expr)
                    } else {
                        p.effect == EffectClass::Pure
                    }
                });
                if above_safe {
                    let item = self.pending.remove(pos);
                    return item.expr;
                }
            }
            // 需要物化（多用表）或被上方有副作用项阻隔：按序冲刷到 pos，再读变量名
            let flushed: Vec<PendingExpr> = self.pending.drain(..=pos).collect();
            for item in flushed {
                let name = self.name_for_pending(&item);
                out.push(AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(name)],
                    values: vec![item.expr],
                    compound_op: None,
                })));
            }
        }
        AstExpr::Var(self.name_for_use_at(iref, reg))
    }

    /// 按从左到右求值顺序解析一组寄存器（例如函数参数、Concat、多返回）。
    ///
    /// 从右向左检查挂起栈顶：若最右侧操作数连续匹配挂起栈顶，则整体按原求值顺序一次性弹出，
    /// 实现 `f(a(), b(), c())` 零中转变量且 100% 保持从左到右副作用顺序！
    pub(super) fn resolve_reg_sequence(
        &mut self,
        iref: InstrRef,
        regs: &[Reg],
        out: &mut Vec<AstStmt>,
    ) -> Vec<AstExpr> {
        // 先检查待解析寄存器在 pending 栈中的顺序是否与从左到右求值顺序发生副作用冲突：
        // 仅当逆序对中至少一方可能写状态（`MayObserveOrWrite` / 正在构造的表）时才需冲刷；
        // 无副作用的只读对（例如 Luau `MOVE r_arg, k; GETIMPORT r_fn, math.floor`）绝不会互相干扰！
        let mut max_flush_pos: Option<usize> = None;
        let mut last_write_pos: Option<usize> = None;
        let mut last_any_non_literal_pos: Option<usize> = None;
        for &reg in regs {
            if let Some(pos) = self.pending.iter().rposition(|p| p.reg == reg) {
                let item = &self.pending[pos];
                let may_write =
                    item.effect == EffectClass::MayObserveOrWrite || item.is_building_table;
                let non_literal =
                    may_write || !self.expr_is_invariant_across_effects(&item.expr);
                if let Some(wpos) = last_write_pos
                    && pos < wpos
                    && non_literal
                {
                    max_flush_pos = Some(max_flush_pos.map_or(pos, |m| m.max(pos)));
                }
                if may_write
                    && let Some(prev_pos) = last_any_non_literal_pos
                    && pos < prev_pos
                {
                    max_flush_pos = Some(max_flush_pos.map_or(pos, |m| m.max(pos)));
                }
                if may_write {
                    last_write_pos = Some(last_write_pos.map_or(pos, |m| m.max(pos)));
                }
                if non_literal {
                    last_any_non_literal_pos =
                        Some(last_any_non_literal_pos.map_or(pos, |m| m.max(pos)));
                }
            }
        }
        if let Some(flush_to) = max_flush_pos {
            let flushed: Vec<PendingExpr> = self.pending.drain(..=flush_to).collect();
            for item in flushed {
                let name = self.name_for_pending(&item);
                out.push(AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(name)],
                    values: vec![item.expr],
                    compound_op: None,
                })));
            }
        }

        let mut results: Vec<Option<AstExpr>> = vec![None; regs.len()];

        // 从右向左连续匹配挂起栈顶：一旦右侧出现无法直接从栈顶弹出的项，立即停止以免跳过它误弹下方项。
        for i in (0..regs.len()).rev() {
            let reg = regs[i];
            if let Some(top) = self.pending.last()
                && top.reg == reg
                && top.open_producer.is_none()
                && !(top.is_building_table
                    && top.val.is_some_and(|v| self.materialized_values.contains(&v)))
            {
                let item = self.pending.pop().unwrap();
                results[i] = Some(item.expr);
            } else if self.pending.iter().any(|p| p.reg == reg) {
                break;
            }
        }

        // 剩余未匹配的操作数按从左到右解析
        for i in 0..regs.len() {
            if results[i].is_none() {
                results[i] = Some(self.resolve_reg_expr(iref, regs[i], out));
            }
        }

        results.into_iter().map(Option::unwrap).collect()
    }

    pub(super) fn resolve_value_operand(
        &mut self,
        iref: InstrRef,
        op: ValueOperand,
        out: &mut Vec<AstStmt>,
    ) -> AstExpr {
        match op {
            ValueOperand::Reg(r) => self.resolve_reg_expr(iref, r, out),
            ValueOperand::Const(c) => self.const_to_expr(c),
            ValueOperand::Integer(v) => AstExpr::Integer(v),
            ValueOperand::Nil => AstExpr::Nil,
            ValueOperand::Boolean(b) => AstExpr::Boolean(b),
        }
    }

    pub(super) fn resolve_binary_operands(
        &mut self,
        iref: InstrRef,
        lhs: ValueOperand,
        rhs: ValueOperand,
        out: &mut Vec<AstStmt>,
    ) -> (AstExpr, AstExpr) {
        if let (ValueOperand::Reg(lr), ValueOperand::Reg(rr)) = (lhs, rhs) {
            let mut seq = self.resolve_reg_sequence(iref, &[lr, rr], out);
            let r = seq.pop().unwrap();
            let l = seq.pop().unwrap();
            return (l, r);
        }
        // 右操作数若为寄存器且位于栈顶先弹出，不破坏左操作数顺序
        match (lhs, rhs) {
            (ValueOperand::Reg(lr), other) => {
                let l = self.resolve_reg_expr(iref, lr, out);
                let r = self.resolve_value_operand(iref, other, out);
                (l, r)
            }
            (other, ValueOperand::Reg(rr)) => {
                let l = self.resolve_value_operand(iref, other, out);
                let r = self.resolve_reg_expr(iref, rr, out);
                (l, r)
            }
            (l, r) => (
                self.resolve_value_operand(iref, l, out),
                self.resolve_value_operand(iref, r, out),
            ),
        }
    }

    pub(super) fn resolve_value_pack(
        &mut self,
        iref: InstrRef,
        pack: ValuePack,
        out: &mut Vec<AstStmt>,
    ) -> Vec<AstExpr> {
        match pack {
            ValuePack::Fixed(range) => {
                let regs: Vec<Reg> = (0..range.len)
                    .map(|off| Reg(range.start.index() + off))
                    .collect();
                let mut exprs = self.resolve_reg_sequence(iref, &regs, out);
                // 固定包最后一个位置若是单结果调用/变参，必须包裹 `(expr)` 防止被 Lua 展开为多值！
                if let Some(last) = exprs.last_mut() {
                    let owned = std::mem::replace(last, AstExpr::Nil);
                    *last = wrap_single_value_if_needed(owned);
                }
                exprs
            }
            ValuePack::Open(consume_start) => {
                // 消费开放多值包：前面固定槽 + 末尾开放 producer（不加 SingleValue 括号！）
                if let Some(link) = self.analysis.dataflow.open_pack_by_consumer.get(&iref).copied()
                {
                    let open_expr = if let Some(pos) = self
                        .pending
                        .iter()
                        .rposition(|p| p.open_producer == Some(link.producer))
                    {
                        self.pending.remove(pos).expr
                    } else {
                        AstExpr::Var(self.name_for_use_at(iref, link.start))
                    };
                    let fixed_len = link.start.index().saturating_sub(consume_start.index());
                    let fixed_regs: Vec<Reg> = (0..fixed_len)
                        .map(|off| Reg(consume_start.index() + off))
                        .collect();
                    let mut exprs = self.resolve_reg_sequence(iref, &fixed_regs, out);
                    exprs.push(open_expr);
                    exprs
                } else {
                    vec![self.resolve_reg_expr(iref, consume_start, out)]
                }
            }
        }
    }

    // ── 条件表达式提升 ───────────────────────────────────────

    pub(super) fn lift_cond_expr(&mut self, cond: &CondExpr, out: &mut Vec<AstStmt>) -> AstExpr {
        match cond {
            CondExpr::True => AstExpr::Boolean(true),
            CondExpr::False => AstExpr::Boolean(false),
            CondExpr::Not(inner) => {
                let e = self.lift_cond_expr(inner, out);
                AstExpr::Unary(Box::new(AstUnaryExpr {
                    op: AstUnaryOpKind::Not,
                    expr: e,
                }))
            }
            CondExpr::And(lhs, rhs) => {
                let l = self.lift_cond_expr(lhs, out);
                // 右侧原子可能包含只属于右侧短路路径的前置求值指令，必须在独立局部栈中求值
                let r = self.lift_short_circuit_rhs(rhs);
                AstExpr::LogicalAnd(Box::new(AstLogicalExpr { lhs: l, rhs: r }))
            }
            CondExpr::Or(lhs, rhs) => {
                let l = self.lift_cond_expr(lhs, out);
                let r = self.lift_short_circuit_rhs(rhs);
                AstExpr::LogicalOr(Box::new(AstLogicalExpr { lhs: l, rhs: r }))
            }
            CondExpr::Atom { block, cond } => {
                // 若该条件块自身为纯条件步（尚未发射过前缀），在此把它的前置表达式指令压入 pending
                self.eval_pure_cond_block_prefix(*block, out);
                let iref = self.analysis.cfg.blocks[block.index()]
                    .instrs
                    .last()
                    .unwrap_or(InstrRef(0));
                self.lift_branch_cond(iref, *cond, out)
            }
        }
    }

    fn lift_short_circuit_rhs(&mut self, rhs: &CondExpr) -> AstExpr {
        let saved_pending = std::mem::take(&mut self.pending);
        let mut dummy_out = Vec::new();
        let expr = self.lift_cond_expr(rhs, &mut dummy_out);
        self.pending = saved_pending;
        expr
    }

    fn eval_pure_cond_block_prefix(&mut self, block: BlockId, out: &mut Vec<AstStmt>) {
        // 如果结构化器已经对首块单独发射过 BlockPrefix（说明该块含非条件语句），
        // 则其非条件前缀已发射；若本块是纯条件步，直接在这里求值其纯临时指令供条件消费！
        if super::super::structure::cond_fold::is_pure_condition_continuation(
            self.proto,
            self.analysis,
            block,
        ) {
            let range = self.analysis.cfg.blocks[block.index()].instrs;
            let last = range.last();
            for iref in range.iter() {
                if Some(iref) == last {
                    break;
                }
                self.lift_instr(iref, out);
            }
        }
    }

    fn lift_branch_cond(
        &mut self,
        iref: InstrRef,
        cond: BranchCond,
        out: &mut Vec<AstStmt>,
    ) -> AstExpr {
        let base = match cond.subject {
            BranchSubject::Truthy(op) => self.resolve_cond_operand(iref, op, out),
            BranchSubject::Compare {
                predicate,
                lhs,
                rhs,
            } => {
                // Lua 编译器把 `a > b` / `a >= b` 编码为 `LT b, a` / `LE b, a`（`a` 先于 `b` 求值压栈）。
                // 若 `rhs` 在 pending 栈中位于 `lhs` 之前，反向弹出并还原为 `Gt`/`Ge`，
                // 既消除多余快照变量、又严格保留源求值序与 `__lt`/`__le` 元方法参数顺序！
                if matches!(predicate, BranchPredicate::Lt | BranchPredicate::Le)
                    && let (CondOperand::Reg(lr), CondOperand::Reg(rr)) = (lhs, rhs)
                    && let (Some(lpos), Some(rpos)) = (
                        self.pending.iter().rposition(|p| p.reg == lr),
                        self.pending.iter().rposition(|p| p.reg == rr),
                    )
                    && rpos < lpos
                {
                    let mut seq = self.resolve_reg_sequence(iref, &[rr, lr], out);
                    let r_expr = seq.pop().unwrap();
                    let l_expr = seq.pop().unwrap();
                    let op = match predicate {
                        BranchPredicate::Lt => AstBinaryOpKind::Gt,
                        BranchPredicate::Le => AstBinaryOpKind::Ge,
                        BranchPredicate::Eq => unreachable!(),
                    };
                    AstExpr::Binary(Box::new(AstBinaryExpr {
                        op,
                        lhs: l_expr,
                        rhs: r_expr,
                    }))
                } else {
                    let (l, r) = self.resolve_cond_pair(iref, lhs, rhs, out);
                    let op = match predicate {
                        BranchPredicate::Eq => AstBinaryOpKind::Eq,
                        BranchPredicate::Lt => AstBinaryOpKind::Lt,
                        BranchPredicate::Le => AstBinaryOpKind::Le,
                    };
                    AstExpr::Binary(Box::new(AstBinaryExpr { op, lhs: l, rhs: r }))
                }
            }
        };
        if cond.negated {
            AstExpr::Unary(Box::new(AstUnaryExpr {
                op: AstUnaryOpKind::Not,
                expr: base,
            }))
        } else {
            base
        }
    }

    fn resolve_cond_operand(
        &mut self,
        iref: InstrRef,
        op: CondOperand,
        out: &mut Vec<AstStmt>,
    ) -> AstExpr {
        match op {
            CondOperand::Reg(r) => self.resolve_reg_expr(iref, r, out),
            CondOperand::Const(c) => self.const_to_expr(c),
            CondOperand::Nil => AstExpr::Nil,
            CondOperand::Boolean(b) => AstExpr::Boolean(b),
            CondOperand::Integer(v) => AstExpr::Integer(v),
            CondOperand::Number(n) => AstExpr::Number(n.to_f64()),
        }
    }

    fn resolve_cond_pair(
        &mut self,
        iref: InstrRef,
        lhs: CondOperand,
        rhs: CondOperand,
        out: &mut Vec<AstStmt>,
    ) -> (AstExpr, AstExpr) {
        if let (CondOperand::Reg(lr), CondOperand::Reg(rr)) = (lhs, rhs) {
            let mut seq = self.resolve_reg_sequence(iref, &[lr, rr], out);
            let r = seq.pop().unwrap();
            let l = seq.pop().unwrap();
            return (l, r);
        }
        let l = self.resolve_cond_operand(iref, lhs, out);
        let r = self.resolve_cond_operand(iref, rhs, out);
        (l, r)
    }

    // ── 表读写与 O(N) 构造器聚合 ─────────────────────────────

    pub(super) fn build_new_table_expr(&self, alloc: &TableAllocation) -> AstExpr {
        let mut fields = Vec::new();
        let is_puc_batched = matches!(alloc, TableAllocation::PucBatched(_));

        match alloc {
            TableAllocation::PucBatched(_)
            | TableAllocation::Luau(_)
            | TableAllocation::Indexed { .. } => {}
            TableAllocation::LuauTemplate(entries) => {
                for &(key_ref, val_ref) in entries {
                    let key = self.table_key_from_const(key_ref);
                    let value = val_ref
                        .map(|vr| self.const_to_expr(vr))
                        .unwrap_or(AstExpr::Integer(0));
                    fields.push(AstTableField::Record(AstRecordField { key, value }));
                }
            }
            TableAllocation::Template(tpl) => {
                // LuaJIT 模板数组索引 0 若非 nil 需显式 `[0] = ...`
                if let Some(&first) = tpl.array.first() {
                    let v0 = self.const_to_expr(first);
                    if !matches!(v0, AstExpr::Nil) {
                        fields.push(AstTableField::Record(AstRecordField {
                            key: AstTableKey::Expr(AstExpr::Integer(0)),
                            value: v0,
                        }));
                    }
                }
                for &elem in tpl.array.iter().skip(1) {
                    fields.push(AstTableField::Array(self.const_to_expr(elem)));
                }
                // LuaJIT TDUP 模板哈希槽顺序依赖编译器内部哈希表布局，纯编译期常量键无求值副作用：
                // 按（非 nil 常量优先、键稳定字典序）规范化排序，确保跨重编译输出稳定收敛。
                let mut hash_fields: Vec<AstRecordField> = tpl
                    .hash
                    .iter()
                    .map(|&(k, v)| AstRecordField {
                        key: self.table_key_from_const(k),
                        value: self.const_to_expr(v),
                    })
                    .collect();
                hash_fields.sort_by_key(|rec| {
                    (
                        matches!(rec.value, AstExpr::Nil),
                        table_key_sort_key(&rec.key),
                    )
                });
                for rec in hash_fields {
                    fields.push(AstTableField::Record(rec));
                }
            }
        }

        AstExpr::TableConstructor(Box::new(AstTableConstructor {
            fields,
            is_puc_batched,
        }))
    }

    pub(super) fn try_absorb_set_table(
        &mut self,
        iref: InstrRef,
        base: AccessBase,
        key: AccessKey,
        value: ValueOperand,
        out: &mut Vec<AstStmt>,
    ) -> bool {
        let AccessBase::Reg(base_reg) = base else {
            return false;
        };
        let Some(tbl_pos) = self.pending.iter().rposition(|p| {
            p.reg == base_reg
                && p.is_building_table
                && p.accepts_set_table
                && !p.table_sealed_by_setlist
        }) else {
            return false;
        };

        // 确认 key 和 value 都不引用正在构造的 base_reg 自身（防止 `t.self = t` 误吸收）
        if matches!(key, AccessKey::Reg(r) if r == base_reg)
            || matches!(value, ValueOperand::Reg(r) if r == base_reg)
        {
            return false;
        }
        // 若 key/value 引用了在 `NEWTABLE` 之前（`pos < tbl_pos`）产生的挂起项（如 `local key = "x"; local t = { [key] = 1 }`），
        // 先行冲刷到该项以保留表前的局部槽与声明顺序，同时保持 `tbl_pos` 本身仍在挂起栈中继续吸收后续字段！
        let mut flush_before_tbl: Option<usize> = None;
        if let AccessKey::Reg(kr) = key
            && let Some(kpos) = self.pending.iter().rposition(|p| p.reg == kr)
            && kpos < tbl_pos
        {
            flush_before_tbl = Some(flush_before_tbl.map_or(kpos, |m| m.max(kpos)));
        }
        if let ValueOperand::Reg(vr) = value
            && let Some(vpos) = self.pending.iter().rposition(|p| p.reg == vr)
            && vpos < tbl_pos
        {
            flush_before_tbl = Some(flush_before_tbl.map_or(vpos, |m| m.max(vpos)));
        }
        if let Some(flush_to) = flush_before_tbl {
            let flushed: Vec<PendingExpr> = self.pending.drain(..=flush_to).collect();
            for item in flushed {
                let name = self.name_for_pending(&item);
                out.push(AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(name)],
                    values: vec![item.expr],
                    compound_op: None,
                })));
            }
        }

        let base_name = self.name_for_use_at(iref, base_reg);

        let (key_expr, val_expr) = match (key, value) {
            (AccessKey::Reg(kr), ValueOperand::Reg(vr)) => {
                let mut seq = self.resolve_reg_sequence(iref, &[kr, vr], out);
                let v = seq.pop().unwrap();
                let k = seq.pop().unwrap();
                (k, v)
            }
            (AccessKey::Reg(kr), vop) => {
                let k = self.resolve_reg_expr(iref, kr, out);
                let v = self.resolve_value_operand(iref, vop, out);
                (k, v)
            }
            (kop, ValueOperand::Reg(vr)) => {
                let k = self.access_key_expr(kop);
                let v = self.resolve_reg_expr(iref, vr, out);
                (k, v)
            }
            (kop, vop) => (
                self.access_key_expr(kop),
                self.resolve_value_operand(iref, vop, out),
            ),
        };

        if expr_mentions_name(&key_expr, &base_name) || expr_mentions_name(&val_expr, &base_name) {
            // 回退并冲刷，保证自引用表按 `local t = {}; t.self = t` 发射
            self.flush_all_pending(out);
            out.push(AstStmt::Assign(Box::new(AstAssign {
                targets: vec![AstLValue::IndexAccess(Box::new(AstIndexAccess {
                    base: AstExpr::Var(base_name),
                    index: key_expr,
                }))],
                values: vec![val_expr],
                compound_op: None,
            })));
            return true;
        }

        // 重新定位 tbl_pos（因为弹出 key/value 可能缩短了 pending）
        let Some(new_pos) = self
            .pending
            .iter()
            .rposition(|p| p.reg == base_reg && p.is_building_table)
        else {
            // 若在求值过程中被冲刷了，按普通表赋值发出
            self.flush_all_pending(out);
            let lv = self.make_table_lvalue(AstExpr::Var(base_name), key_expr);
            out.push(AstStmt::Assign(Box::new(AstAssign {
                targets: vec![lv],
                values: vec![val_expr],
                compound_op: None,
            })));
            return true;
        };

        let set_order = self.alloc_eval_order();
        let write_effect = if super::expr_may_have_side_effect(&key_expr)
            || super::expr_may_have_side_effect(&val_expr)
        {
            EffectClass::MayObserveOrWrite
        } else if !expr_is_pure_literal(&key_expr)
            || (!expr_is_pure_literal(&val_expr) && !matches!(val_expr, AstExpr::FunctionExpr(_)))
        {
            EffectClass::ReadsState
        } else {
            EffectClass::Pure
        };
        let is_luau_template = self.pending[new_pos].is_luau_template;
        let luau_max_fields = self.pending[new_pos].luau_max_fields;
        let luau_force_index_keys = self.pending[new_pos].luau_force_index_keys;
        let is_luajit_indexed = self.pending[new_pos].is_luajit_indexed;
        let is_luajit_template = self.pending[new_pos].is_luajit_template;
        let int_key = match &key_expr {
            AstExpr::Integer(k) if *k >= 1 => Some(*k as usize),
            _ => None,
        };
        let table_key = if luau_force_index_keys {
            AstTableKey::Expr(key_expr)
        } else {
            self.expr_to_table_key(key_expr)
        };
        let PendingExpr {
            expr: AstExpr::TableConstructor(ref mut ctor),
            ref mut effect,
            ref mut array_field_count,
            ref mut field_orders,
            ..
        } = self.pending[new_pos]
        else {
            return false;
        };
        // 向上传播表字段求值的副作用等级（纯字面量/闭包函数字段保持 `Pure`，读取变量升为 `ReadsState`，
        // 含调用/索引/算术元方法升为 `MayObserveOrWrite`），确保纯表构造器可安全跨纯项内联而不重排副作用！
        *effect = merge_effect_class(*effect, write_effect);

        // LuaJIT `TNEW`（Indexed）编译数组 `{ a, b, c }` 时逐条发射 `TSETB(1), TSETB(2), ...`：
        // 若键是连续正整数 `existing_array_count + 1`，吸收为列表元素（多值表达式自动单值截断），
        // 保持原表的数组预分配容量与 `#t` 行为！
        if is_luajit_indexed && let Some(k) = int_key && k == *array_field_count + 1 {
            ctor.fields
                .push(AstTableField::Array(wrap_single_value_if_needed(val_expr)));
            *array_field_count += 1;
            field_orders.push(set_order);
            let _ = tbl_pos;
            return true;
        }

        // LuaJIT `TDUP` 模板（Template）：仅当目标占位之后的所有既有字段均为纯编译期字面量常量时，
        // 才允许用后续运行期值就地替换 `Nil` 占位（绝不跨任何运行期读/调用重排求值顺序！）。
        if is_luajit_template {
            if let Some(k) = int_key {
                let mut arr_idx = 0usize;
                let mut target_field_idx = None;
                for (fi, field) in ctor.fields.iter().enumerate() {
                    if let AstTableField::Array(slot_expr) = field {
                        arr_idx += 1;
                        if arr_idx == k && matches!(slot_expr, AstExpr::Nil) {
                            target_field_idx = Some(fi);
                            break;
                        }
                    }
                }
                if let Some(fi) = target_field_idx
                    && ctor.fields[fi + 1..].iter().all(table_field_is_pure_literal)
                {
                    ctor.fields[fi] = AstTableField::Array(wrap_single_value_if_needed(val_expr));
                    field_orders[fi] = set_order;
                    let _ = tbl_pos;
                    return true;
                }
            }
            if let Some(fi) = ctor.fields.iter().position(|f| {
                matches!(
                    f,
                    AstTableField::Record(rec)
                        if rec.key == table_key && matches!(rec.value, AstExpr::Nil)
                )
            }) && ctor.fields[fi + 1..].iter().all(table_field_is_pure_literal)
            {
                if let AstTableField::Record(rec) = &mut ctor.fields[fi] {
                    rec.value = val_expr;
                    field_orders[fi] = set_order;
                }
                let _ = tbl_pos;
                return true;
            }
            // 不能安全原地替换时，停止继续吞并该表：冲刷表构造器并发出显式表写入，严格保留原求值顺序！
            let _ = (ctor, field_orders);
            self.flush_pending_for_reg(base_reg, out);
            let lv = match table_key {
                AstTableKey::Name(field) => AstLValue::FieldAccess(Box::new(AstFieldAccess {
                    base: AstExpr::Var(base_name),
                    field,
                })),
                AstTableKey::Expr(index) => AstLValue::IndexAccess(Box::new(AstIndexAccess {
                    base: AstExpr::Var(base_name),
                    index,
                })),
            };
            out.push(AstStmt::Assign(Box::new(AstAssign {
                targets: vec![lv],
                values: vec![val_expr],
                compound_op: None,
            })));
            let _ = tbl_pos;
            return true;
        }

        // 仅 Luau DUPTABLE 预填键模板允许按同名键就地替换尚未写入过的 `nil` 占位（`field_orders[fi] == 0`）；
        // 若该键不在模板内（属于构造后扩展键，如 `result.e = 5`），或已被先前运行期赋值填充过（`field_orders[fi] != 0`），
        // 绝不可吞入构造器（否则改变表容量/rehash 次序或丢失副作用），立即冲刷表构造器并发出显式赋值！
        if is_luau_template {
            if let Some(fi) = ctor.fields.iter().position(|f| {
                matches!(f, AstTableField::Record(rec) if rec.key == table_key)
            }) && field_orders[fi] == 0
            {
                if let AstTableField::Record(rec) = &mut ctor.fields[fi] {
                    rec.value = val_expr;
                    field_orders[fi] = set_order;
                }
            } else {
                let _ = (ctor, field_orders);
                self.flush_pending_for_reg(base_reg, out);
                let lv = match table_key {
                    AstTableKey::Name(field) => AstLValue::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(base_name),
                        field,
                    })),
                    AstTableKey::Expr(index) => {
                        AstLValue::IndexAccess(Box::new(AstIndexAccess {
                            base: AstExpr::Var(base_name),
                            index,
                        }))
                    }
                };
                out.push(AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![lv],
                    values: vec![val_expr],
                    compound_op: None,
                })));
            }
        } else if let Some(cap) = luau_max_fields
            && ctor.fields.len() >= cap
        {
            // Luau NEWTABLE 已填满预分配容量：后续写入属于构造后扩表，冲刷并按显式赋值发射以保 `pairs()` / `#t` 语义
            let _ = (ctor, field_orders);
            self.flush_pending_for_reg(base_reg, out);
            let lv = match table_key {
                AstTableKey::Name(field) => AstLValue::FieldAccess(Box::new(AstFieldAccess {
                    base: AstExpr::Var(base_name),
                    field,
                })),
                AstTableKey::Expr(index) => AstLValue::IndexAccess(Box::new(AstIndexAccess {
                    base: AstExpr::Var(base_name),
                    index,
                })),
            };
            out.push(AstStmt::Assign(Box::new(AstAssign {
                targets: vec![lv],
                values: vec![val_expr],
                compound_op: None,
            })));
        } else {
            ctor.fields.push(AstTableField::Record(AstRecordField {
                key: table_key,
                value: val_expr,
            }));
            field_orders.push(set_order);
        }
        let _ = tbl_pos;
        true
    }

    pub(super) fn lift_set_list(
        &mut self,
        iref: InstrRef,
        base: Reg,
        values: ValuePack,
        start_index: u32,
        out: &mut Vec<AstStmt>,
    ) {
        // 在弹出元素前，先记录各输入槽位在 pending 栈中的原始求值序号，
        // 以便还原 `{ [k]=v, a(), tag=b(), c(), d() }` 等交错记录/数组构造器的精确从左到右求值顺序！
        let elem_orders: Vec<usize> = match values {
            ValuePack::Fixed(range) => (0..range.len)
                .map(|off| {
                    let r = Reg(range.start.index() + off);
                    self.pending
                        .iter()
                        .rposition(|p| p.reg == r)
                        .map(|i| self.pending[i].order)
                        .unwrap_or(usize::MAX)
                })
                .collect(),
            ValuePack::Open(consume_start) => {
                if let Some(link) = self.analysis.dataflow.open_pack_by_consumer.get(&iref).copied()
                {
                    let fixed_len = link.start.index().saturating_sub(consume_start.index());
                    let mut ords: Vec<usize> = (0..fixed_len)
                        .map(|off| {
                            let r = Reg(consume_start.index() + off);
                            self.pending
                                .iter()
                                .rposition(|p| p.reg == r)
                                .map(|i| self.pending[i].order)
                                .unwrap_or(usize::MAX)
                        })
                        .collect();
                    let open_ord = self
                        .pending
                        .iter()
                        .rposition(|p| p.open_producer == Some(link.producer))
                        .map(|i| self.pending[i].order)
                        .unwrap_or(usize::MAX);
                    ords.push(open_ord);
                    ords
                } else {
                    vec![usize::MAX]
                }
            }
        };
        let is_open_pack = matches!(values, ValuePack::Open(_));
        let mut elems = self.resolve_value_pack(iref, values, out);
        let elems_effect = elems.iter().fold(EffectClass::Pure, |acc, e| {
            let eff = if super::expr_may_have_side_effect(e) {
                EffectClass::MayObserveOrWrite
            } else if !expr_is_pure_literal(e) && !matches!(e, AstExpr::FunctionExpr(_)) {
                EffectClass::ReadsState
            } else {
                EffectClass::Pure
            };
            merge_effect_class(acc, eff)
        });
        if let Some(pos) = self
            .pending
            .iter()
            .rposition(|p| p.reg == base && p.is_building_table)
        {
            self.pending[pos].table_sealed_by_setlist = true;
            self.pending[pos].effect = merge_effect_class(self.pending[pos].effect, elems_effect);
            let PendingExpr {
                expr: AstExpr::TableConstructor(ref mut ctor),
                ref mut array_field_count,
                ref mut field_orders,
                ..
            } = self.pending[pos]
            else {
                return;
            };
            let start = start_index as usize;
            let existing_array_count = *array_field_count;
            if existing_array_count + 1 == start {
                // 检查是否需要按原始求值序号将数组元素交错归并回既有 Record 字段之间：
                // 仅在既有字段全为 Record（或数组前缀已齐）、且末尾开放多返回保持在列表最后时执行安全归并。
                let elem_count = elems.len();
                let orders_monotone = elem_orders.windows(2).all(|w| w[0] <= w[1]);
                let open_is_last = !is_open_pack
                    || elem_orders
                        .last()
                        .copied()
                        .unwrap_or(usize::MAX)
                        >= field_orders.last().copied().unwrap_or(0);
                let has_interleaving = existing_array_count == 0
                    && !field_orders.is_empty()
                    && orders_monotone
                    && open_is_last
                    && elem_orders.len() == elem_count
                    && elem_orders
                        .iter()
                        .any(|&eo| eo < usize::MAX && field_orders.iter().any(|&fo| fo > eo));

                if has_interleaving {
                    let old_fields = std::mem::take(&mut ctor.fields);
                    let old_orders = std::mem::take(field_orders);
                    let mut rec_iter = old_fields.into_iter().zip(old_orders).peekable();
                    let mut arr_iter = elems.into_iter().zip(elem_orders).peekable();
                    while let (Some(&(_, ro)), Some(&(_, ao))) = (rec_iter.peek(), arr_iter.peek()) {
                        if ao < ro {
                            let (e, o) = arr_iter.next().unwrap();
                            ctor.fields.push(AstTableField::Array(e));
                            *array_field_count += 1;
                            field_orders.push(o);
                        } else {
                            let (f, o) = rec_iter.next().unwrap();
                            ctor.fields.push(f);
                            field_orders.push(o);
                        }
                    }
                    for (f, o) in rec_iter {
                        ctor.fields.push(f);
                        field_orders.push(o);
                    }
                    for (e, o) in arr_iter {
                        ctor.fields.push(AstTableField::Array(e));
                        *array_field_count += 1;
                        field_orders.push(o);
                    }
                    return;
                }

                for (idx, elem) in elems.into_iter().enumerate() {
                    ctor.fields.push(AstTableField::Array(elem));
                    *array_field_count += 1;
                    field_orders.push(elem_orders.get(idx).copied().unwrap_or(usize::MAX));
                }
                return;
            }
            // 当模板（如 LuaJIT TDUP）预填了数组 `[1..=M]` 而开放/批量 SetList 从 `start <= M` 重叠写入
            // （如 `{ [2] = "old", "head", many() }`）时，将第 `start..=M` 个既有 Array 转为显式 Record
            // 留在前面，再将 SetList 元素以 Array 形式追加到末尾，完整保留开放多返回展开与 0 返回不覆盖语义！
            if start >= 1 && start <= existing_array_count {
                let mut arr_idx = 0usize;
                for field in &mut ctor.fields {
                    if let AstTableField::Array(_) = field {
                        arr_idx += 1;
                        if arr_idx >= start {
                            let owned = std::mem::replace(field, AstTableField::Array(AstExpr::Nil));
                            if let AstTableField::Array(v) = owned {
                                *field = AstTableField::Record(AstRecordField {
                                    key: AstTableKey::Expr(AstExpr::Integer(arr_idx as i64)),
                                    value: v,
                                });
                                *array_field_count -= 1;
                            }
                        }
                    }
                }
                for (idx, elem) in elems.into_iter().enumerate() {
                    ctor.fields.push(AstTableField::Array(elem));
                    *array_field_count += 1;
                    field_orders.push(elem_orders.get(idx).copied().unwrap_or(usize::MAX));
                }
                return;
            }
            for (i, elem) in elems.into_iter().enumerate() {
                ctor.fields.push(AstTableField::Record(AstRecordField {
                    key: AstTableKey::Expr(AstExpr::Integer(
                        i64::from(start_index) + i as i64,
                    )),
                    value: elem,
                }));
                field_orders.push(elem_orders.get(i).copied().unwrap_or(usize::MAX));
            }
            return;
        }

        // 若表已经落盘，按显式索引赋值发射；若是开放多值 `SetList`，绝不可截断为单值 `t[k] = f()`！
        self.flush_all_pending(out);
        let base_name = self.name_for_use_at(iref, base);
        let base_expr = AstExpr::Var(base_name.clone());
        let is_open_pack = matches!(values, ValuePack::Open(_));
        if is_open_pack && start_index == 1 {
            // 若前面仅落盘了空表或纯常量键表（无 Array 项，如 `t = { [3] = 99 }`）且之后无人读取/修改 `t`，
            // 直接吸收为干净的 `t = { [3] = 99, elems... }`，完整保住开放多返回值（含尾 nil）覆盖语义！
            let is_pure_const_literal = |e: &AstExpr| -> bool {
                matches!(
                    e,
                    AstExpr::Nil
                        | AstExpr::Boolean(_)
                        | AstExpr::Integer(_)
                        | AstExpr::Number(_)
                        | AstExpr::String(_)
                )
            };
            let is_pure_record_only_table = |tc: &AstTableConstructor| -> bool {
                tc.fields.iter().all(|f| match f {
                    AstTableField::Array(_) => false,
                    AstTableField::Record(r) => {
                        let key_ok = match &r.key {
                            AstTableKey::Name(_) => true,
                            AstTableKey::Expr(k) => is_pure_const_literal(k),
                        };
                        key_ok && is_pure_const_literal(&r.value)
                    }
                })
            };
            if let Some(def_pos) = out.iter().rposition(|stmt| {
                matches!(
                    stmt,
                    AstStmt::Assign(a)
                        if a.compound_op.is_none()
                            && a.targets.len() == 1
                            && a.targets[0] == AstLValue::Name(base_name.clone())
                            && a.values.len() == 1
                            && matches!(&a.values[0], AstExpr::TableConstructor(tc) if is_pure_record_only_table(tc))
                )
            }) && out[def_pos + 1..]
                .iter()
                .all(|s| !stmt_mentions_name_shallow(s, &base_name))
            {
                let mut fields = match out.remove(def_pos) {
                    AstStmt::Assign(mut a) => match a.values.pop() {
                        Some(AstExpr::TableConstructor(tc)) => tc.fields,
                        _ => Vec::new(),
                    },
                    _ => Vec::new(),
                };
                fields.extend(elems.into_iter().map(AstTableField::Array));
                out.push(AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(base_name)],
                    values: vec![AstExpr::TableConstructor(Box::new(AstTableConstructor {
                        fields,
                        is_puc_batched: false,
                    }))],
                    compound_op: None,
                })));
                return;
            }
        }
        if is_open_pack && let Some(open_tail) = elems.pop() {
            let fixed_count = elems.len();
            for (i, elem) in elems.drain(..).enumerate() {
                out.push(AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::IndexAccess(Box::new(AstIndexAccess {
                        base: base_expr.clone(),
                        index: AstExpr::Integer(i64::from(start_index) + i as i64),
                    }))],
                    values: vec![elem],
                    compound_op: None,
                })));
            }
            // 使用 `(function(t, n, ...) local p = { ... }; for i = 1, select("#", ...) do t[n + i] = p[i] end end)(base, offset, open_tail)`
            // 按 `select("#", ...)` 精确遍历全部返回值（含尾部/中间 `nil`），保证覆盖既有数组键！
            let offset = i64::from(start_index) + fixed_count as i64 - 1;
            let helper = self.proto_registry.alloc_synthetic_open_setlist_pack();
            out.push(AstStmt::CallStmt(Box::new(super::super::common::AstCallStmt {
                call: super::super::common::AstCallKind::Call(Box::new(AstCallExpr {
                    callee: AstExpr::FunctionExpr(Box::new(helper)),
                    args: vec![base_expr, AstExpr::Integer(offset), open_tail],
                })),
            })));
            return;
        }
        for (i, elem) in elems.drain(..).enumerate() {
            out.push(AstStmt::Assign(Box::new(AstAssign {
                targets: vec![AstLValue::IndexAccess(Box::new(AstIndexAccess {
                    base: base_expr.clone(),
                    index: AstExpr::Integer(i64::from(start_index) + i as i64),
                }))],
                values: vec![elem],
                compound_op: None,
            })));
        }
    }

    pub(super) fn lift_get_table(
        &mut self,
        iref: InstrRef,
        base: AccessBase,
        key: AccessKey,
        kind: GetTableKind,
        out: &mut Vec<AstStmt>,
    ) -> AstExpr {
        // `SELF` 方法查找：若接收者寄存器 `self_reg` 正在 pending 栈中等待被紧随的 `Call(Method)` 消费，
        // 绝不提前弹出或冲刷 `self_reg`；仅用 `Var(self_reg)` 作为万一发生冲刷时的安全回退表达式。
        if kind == GetTableKind::Method
            && let AccessBase::Reg(self_reg) = base
            && self.pending.iter().any(|p| p.reg == self_reg)
        {
            let key_expr = match key {
                AccessKey::Reg(kr) => self.resolve_reg_expr(iref, kr, out),
                other => self.access_key_expr(other),
            };
            let base_expr = AstExpr::Var(self.name_for_use_at(iref, self_reg));
            return self.make_table_expr(base_expr, key_expr);
        }

        // 全局环境变量访问（Env / EnvironmentUpvalue）：
        // Lua 5.2+ 常量表超过 255 项时会先 `LOADK` 再 `GETTABUP _ENV, rK`，
        // 因此先解析键表达式，再统一把合法标识符字符串还原为普通全局名。
        if matches!(base, AccessBase::Env | AccessBase::EnvironmentUpvalue(_)) {
            let key_expr = match key {
                AccessKey::Reg(kr) => self.resolve_reg_expr(iref, kr, out),
                other => self.access_key_expr(other),
            };
            if let AstExpr::String(ref s) = key_expr
                && let Some(name) = s.as_utf8()
                && self.target.version.is_identifier_name(name)
                && !(matches!(base, AccessBase::EnvironmentUpvalue(_)) && name == "_ENV")
            {
                return AstExpr::Var(AstNameRef::Global(AstGlobalName {
                    text: name.to_owned(),
                }));
            }
            let base_expr = match base {
                AccessBase::EnvironmentUpvalue(_) => AstExpr::Var(AstNameRef::Environment),
                AccessBase::Env => AstExpr::Var(AstNameRef::Global(AstGlobalName {
                    text: "_G".to_owned(),
                })),
                _ => unreachable!(),
            };
            return AstExpr::IndexAccess(Box::new(AstIndexAccess {
                base: base_expr,
                index: key_expr,
            }));
        }

        let (base_expr, key_expr) = match (base, key) {
            (AccessBase::Reg(br), AccessKey::Reg(kr)) => {
                let mut seq = self.resolve_reg_sequence(iref, &[br, kr], out);
                let k = seq.pop().unwrap();
                let b = seq.pop().unwrap();
                (b, k)
            }
            (AccessBase::Reg(br), other) => (
                self.resolve_reg_expr(iref, br, out),
                self.access_key_expr(other),
            ),
            (AccessBase::Upvalue(u), AccessKey::Reg(kr)) => (
                AstExpr::Var(AstNameRef::Upvalue(UpvalueId(u.index()))),
                self.resolve_reg_expr(iref, kr, out),
            ),
            (AccessBase::Upvalue(u), other) => (
                AstExpr::Var(AstNameRef::Upvalue(UpvalueId(u.index()))),
                self.access_key_expr(other),
            ),
            _ => unreachable!(),
        };

        self.make_table_expr(base_expr, key_expr)
    }

    pub(super) fn lift_set_table_parts(
        &mut self,
        iref: InstrRef,
        base: AccessBase,
        key: AccessKey,
        value: ValueOperand,
        out: &mut Vec<AstStmt>,
    ) -> (AstLValue, AstExpr) {
        if matches!(base, AccessBase::Env | AccessBase::EnvironmentUpvalue(_)) {
            let mut regs = Vec::new();
            if let AccessKey::Reg(r) = key {
                regs.push(r);
            }
            if let ValueOperand::Reg(r) = value {
                regs.push(r);
            }
            let mut resolved = self.resolve_reg_sequence(iref, &regs, out).into_iter();
            let key_expr = match key {
                AccessKey::Reg(_) => resolved.next().unwrap(),
                other => self.access_key_expr(other),
            };
            let val_expr = match value {
                ValueOperand::Reg(_) => resolved.next().unwrap(),
                other => self.resolve_value_operand(iref, other, out),
            };
            if let AstExpr::String(ref s) = key_expr
                && let Some(name) = s.as_utf8()
                && self.target.version.is_identifier_name(name)
                && !(matches!(base, AccessBase::EnvironmentUpvalue(_)) && name == "_ENV")
            {
                return (
                    AstLValue::Name(AstNameRef::Global(AstGlobalName {
                        text: name.to_owned(),
                    })),
                    val_expr,
                );
            }
            let base_expr = match base {
                AccessBase::EnvironmentUpvalue(_) => AstExpr::Var(AstNameRef::Environment),
                _ => AstExpr::Var(AstNameRef::Global(AstGlobalName {
                    text: "_G".to_owned(),
                })),
            };
            return (self.make_table_lvalue(base_expr, key_expr), val_expr);
        }

        // 在支持 `SETTABUP` 或延后读取 `upval` 的方言下：
        // - Lua 5.2~5.3 `upval[k()] = v()` 均在 `k()`/`v()` 之后读取 `upval`；
        // - Lua 5.4~5.5 常量键 `upval.k = v()` 在 `v()` 之后读取 `upval`，动态键 `upval[k()] = v()` 在 `k()` 之后读取 `upval`；
        // 若字节码显式先快照了 `upval`（`bpos < kpos` 或先于副作用值）或被捕获局部变量，必须先将 `base` 冲刷为局部快照！
        if let AccessBase::Reg(br) = base
            && let Some(bpos) = self.pending.iter().rposition(|p| p.reg == br)
        {
            let key_pos_with_effect = match key {
                AccessKey::Reg(kr) => self
                    .pending
                    .iter()
                    .rposition(|p| p.reg == kr && p.effect == EffectClass::MayObserveOrWrite),
                _ => None,
            };
            let val_has_effect = matches!(value, ValueOperand::Reg(vr) if self.pending.iter().any(|p| p.reg == vr && p.effect == EffectClass::MayObserveOrWrite));
            if key_pos_with_effect.is_some() || val_has_effect {
                let base_item = &self.pending[bpos];
                let dialect_delays_upval = match self.target.version {
                    crate::decompile::DecompileDialect::Lua52
                    | crate::decompile::DecompileDialect::Lua53 => true,
                    crate::decompile::DecompileDialect::Lua54
                    | crate::decompile::DecompileDialect::Lua55 => {
                        matches!(key, AccessKey::Const(c) if self.const_string_utf8(c).is_some())
                            || key_pos_with_effect.is_some_and(|kpos| bpos < kpos)
                    }
                    _ => false,
                };
                let is_upval_snapshot = dialect_delays_upval
                    && matches!(
                        base_item.expr,
                        AstExpr::Var(AstNameRef::Upvalue(_) | AstNameRef::Environment)
                    );
                let is_pinned_move_snapshot = match &self.proto.instrs[base_item.anchor.index()] {
                    LowInstr::Move(m) => self
                        .analysis
                        .ssa
                        .instr_use_value(base_item.anchor, m.src)
                        .is_some_and(|v| self.analysis.ssa.pinned_values.contains(&v)),
                    _ => false,
                };
                if is_upval_snapshot || is_pinned_move_snapshot {
                    self.flush_pending_for_reg(br, out);
                }
            }
        }

        // 按操作数顺序解析 (base, key, value)
        let mut regs = Vec::new();
        if let AccessBase::Reg(r) = base {
            regs.push(r);
        }
        if let AccessKey::Reg(r) = key {
            regs.push(r);
        }
        if let ValueOperand::Reg(r) = value {
            regs.push(r);
        }
        let mut resolved = self.resolve_reg_sequence(iref, &regs, out).into_iter();

        let base_expr = match base {
            AccessBase::Reg(_) => resolved.next().unwrap(),
            AccessBase::Upvalue(u) => AstExpr::Var(AstNameRef::Upvalue(UpvalueId(u.index()))),
            _ => unreachable!(),
        };
        let key_expr = match key {
            AccessKey::Reg(_) => resolved.next().unwrap(),
            other => self.access_key_expr(other),
        };
        let val_expr = match value {
            ValueOperand::Reg(_) => resolved.next().unwrap(),
            other => self.resolve_value_operand(iref, other, out),
        };

        (self.make_table_lvalue(base_expr, key_expr), val_expr)
    }

    fn make_table_expr(&self, base: AstExpr, key: AstExpr) -> AstExpr {
        if let AstExpr::String(ref s) = key
            && let Some(name) = s.as_utf8()
            && self.target.version.is_identifier_name(name)
        {
            // Lua 5.4/5.5 常量索引 > 255 时，普通全局读取会降级为 `GETUPVAL rE, _ENV; LOADK rK, "g"; GETTABLE rE[rK]`；
            // 若 `base` 是未遮蔽的词法环境 upvalue `_ENV`（非局部快照），还原为普通全局名。
            if matches!(base, AstExpr::Var(AstNameRef::Environment)) && name != "_ENV" {
                return AstExpr::Var(AstNameRef::Global(AstGlobalName {
                    text: name.to_owned(),
                }));
            }
            return AstExpr::FieldAccess(Box::new(AstFieldAccess {
                base,
                field: name.to_owned(),
            }));
        }
        AstExpr::IndexAccess(Box::new(AstIndexAccess { base, index: key }))
    }

    fn make_table_lvalue(&self, base: AstExpr, key: AstExpr) -> AstLValue {
        if let AstExpr::String(ref s) = key
            && let Some(name) = s.as_utf8()
            && self.target.version.is_identifier_name(name)
        {
            if matches!(base, AstExpr::Var(AstNameRef::Environment)) && name != "_ENV" {
                return AstLValue::Name(AstNameRef::Global(AstGlobalName {
                    text: name.to_owned(),
                }));
            }
            return AstLValue::FieldAccess(Box::new(AstFieldAccess {
                base,
                field: name.to_owned(),
            }));
        }
        AstLValue::IndexAccess(Box::new(AstIndexAccess { base, index: key }))
    }

    // ── 函数调用、方法糖与变参 ───────────────────────────────

    pub(super) fn lift_call(&mut self, iref: InstrRef, call: &CallInstr, out: &mut Vec<AstStmt>) {
        let call_kind = self.build_call_kind(
            iref,
            call.callee,
            call.args,
            call.kind,
            call.method_name,
            out,
        );

        match call.results {
            ResultPack::Ignore => {
                self.flush_all_pending(out);
                out.push(AstStmt::CallStmt(Box::new(AstCallStmt { call: call_kind })));
            }
            ResultPack::Open(start) => {
                let expr = call_kind_to_expr(call_kind);
                self.flush_before_reg_write(iref, start, out);
                let order = self.alloc_eval_order();
                self.pending.push(PendingExpr {
                    reg: start,
                    val: self.analysis.ssa.instr_def_value(iref, start),
                    anchor: iref,
                    expr,
                    effect: EffectClass::MayObserveOrWrite,
                    order,
                    is_building_table: false,
                    accepts_set_table: false,
                    is_luau_template: false,
                    luau_max_fields: None,
                    luau_force_index_keys: false,
                    is_luajit_indexed: false,
                    is_luajit_template: false,
                    table_sealed_by_setlist: false,
                    array_field_count: 0,
                    field_orders: Vec::new(),
                    open_producer: Some(iref),
                    method_lookup: None,
                });
            }
            ResultPack::Fixed(range) if range.len == 0 => {
                self.flush_all_pending(out);
                out.push(AstStmt::CallStmt(Box::new(AstCallStmt { call: call_kind })));
            }
            ResultPack::Fixed(range) if range.len == 1 => {
                let dst = range.start;
                let expr = call_kind_to_expr(call_kind);
                let val = self.analysis.ssa.instr_def_value(iref, dst);
                // 若返回值未被使用，直接发射为 CallStmt，避免无意义 `local _ = f()`
                if val.is_some_and(|v| {
                    self.analysis.ssa.use_count(v) == 0 && !self.materialized_values.contains(&v)
                }) {
                    self.flush_all_pending(out);
                    out.push(AstStmt::CallStmt(Box::new(AstCallStmt {
                        call: expr_to_call_kind(expr),
                    })));
                    return;
                }
                self.emit_single_def(iref, dst, expr, out);
            }
            ResultPack::Fixed(range) => {
                // 多返回值调用：`a, b, c = f(...)`
                self.flush_all_pending(out);
                let mut targets = Vec::with_capacity(range.len);
                for offset in 0..range.len {
                    let r = Reg(range.start.index() + offset);
                    targets.push(AstLValue::Name(self.name_for_def_at(iref, r)));
                }
                out.push(AstStmt::Assign(Box::new(AstAssign {
                    targets,
                    values: vec![call_kind_to_expr(call_kind)],
                    compound_op: None,
                })));
            }
        }
    }

    pub(super) fn lift_tail_call_expr(
        &mut self,
        iref: InstrRef,
        tc: &TailCallInstr,
        out: &mut Vec<AstStmt>,
    ) -> AstExpr {
        let kind = self.build_call_kind(iref, tc.callee, tc.args, tc.kind, tc.method_name, out);
        call_kind_to_expr(kind)
    }

    fn build_call_kind(
        &mut self,
        iref: InstrRef,
        callee: Reg,
        args: ValuePack,
        kind: CallKind,
        method_name: Option<crate::transformer::MethodNameHint>,
        out: &mut Vec<AstStmt>,
    ) -> AstCallKind {
        // 先尝试按方法协议消费 `obj:method(args...)`
        if kind == CallKind::Method
            && let Some(hint) = method_name
            && let Some(name) = self.const_string_utf8(hint.const_ref)
            && self.target.version.is_identifier_name(&name)
        {
            let first_arg_reg = match args {
                ValuePack::Fixed(range) if range.len >= 1 => Some(range.start),
                ValuePack::Open(consume_start) => self
                    .analysis
                    .dataflow
                    .open_pack_by_consumer
                    .get(&iref)
                    .and_then(|link| (link.start > consume_start).then_some(consume_start)),
                _ => None,
            };
            // 若 callee 是刚在 `self_reg` 之上压入的 `GetTableKind::Method` 查找，先将其摘出 pending 栈，
            // 使随后的 `resolve_value_pack` 能从栈顶顺滑弹出 `args[1..]` 与 `self_reg`，避免产生多余 `local r = obj; r:m()`！
            let matched_callee_pos = first_arg_reg.and_then(|self_reg| {
                let cpos = self.pending.iter().rposition(|p| p.reg == callee)?;
                let item = &self.pending[cpos];
                let (mreg, mkey) = item.method_lookup.as_ref()?;
                if *mreg != self_reg || mkey.as_utf8() != Some(name.as_str()) {
                    return None;
                }
                if let Some(spos) = self.pending[..cpos].iter().rposition(|p| p.reg == self_reg)
                    && spos + 1 != cpos
                {
                    return None;
                }
                Some(cpos)
            });
            if let Some(cpos) = matched_callee_pos {
                self.pending.remove(cpos);
                // Luau `NAMECALL` 对简单接收者会先求值实参再 `MOVE self; NAMECALL`：
                // 若 `self_reg` 恰位于栈顶且为无副作用不变量，先弹出接收者再按序消费其余实参，避免把实参冲刷成多余局部！
                if let Some(self_reg) = first_arg_reg
                    && let ValuePack::Fixed(range) = args
                    && range.len >= 2
                    && self.pending.last().is_some_and(|p| {
                        p.reg == self_reg
                            && p.open_producer.is_none()
                            && self.expr_is_invariant_across_effects(&p.expr)
                    })
                {
                    let receiver = self.pending.pop().unwrap().expr;
                    let tail_pack = ValuePack::Fixed(crate::transformer::RegRange {
                        start: Reg(range.start.index() + 1),
                        len: range.len - 1,
                    });
                    let arg_exprs = self.resolve_value_pack(iref, tail_pack, out);
                    return AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                        interpolation: None,
                        receiver,
                        method: name,
                        args: arg_exprs,
                    }));
                }
                let mut arg_exprs = self.resolve_value_pack(iref, args, out);
                if !arg_exprs.is_empty() {
                    let receiver = arg_exprs.remove(0);
                    return AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                        interpolation: None,
                        receiver,
                        method: name,
                        args: arg_exprs,
                    }));
                }
            }

            let mut arg_exprs = self.resolve_value_pack(iref, args, out);
            let callee_item = self
                .pending
                .iter()
                .rposition(|p| p.reg == callee)
                .map(|pos| self.pending.remove(pos));
            if !arg_exprs.is_empty() {
                let receiver = arg_exprs.remove(0);
                if callee_item.is_some() {
                    return AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                        interpolation: None,
                        receiver,
                        method: name,
                        args: arg_exprs,
                    }));
                }
                // 回退普通调用
                arg_exprs.insert(0, receiver);
                let callee_expr = AstExpr::Var(self.name_for_use_at(iref, callee));
                return AstCallKind::Call(Box::new(AstCallExpr {
                    callee: callee_expr,
                    args: arg_exprs,
                }));
            }
        }

        // Luau `FASTCALL` 字节码把 `GETIMPORT` callee 放在实参准备指令之后压入 pending 栈顶：
        // 若 callee 恰位于栈顶，先弹出 callee 再顺序消费实参，彻底消除 `FASTCALL` 导致的虚假临时变量与局部寄存器爆炸！
        if matches!(kind, CallKind::FastCall(_))
            && self
                .pending
                .last()
                .is_some_and(|p| p.reg == callee && p.open_producer.is_none())
        {
            let callee_expr = self.pending.pop().unwrap().expr;
            let arg_exprs = self.resolve_value_pack(iref, args, out);
            return AstCallKind::Call(Box::new(AstCallExpr {
                callee: callee_expr,
                args: arg_exprs,
            }));
        }

        // 普通调用：先按序弹出参数，再弹出 callee（符合 Lua 从左到右先求 callee 再求 args 的栈序！）
        let arg_exprs = self.resolve_value_pack(iref, args, out);
        let callee_expr = self.resolve_reg_expr(iref, callee, out);
        AstCallKind::Call(Box::new(AstCallExpr {
            callee: callee_expr,
            args: arg_exprs,
        }))
    }

    pub(super) fn lift_vararg(&mut self, iref: InstrRef, results: ResultPack, out: &mut Vec<AstStmt>) {
        match results {
            ResultPack::Ignore => {}
            ResultPack::Open(start) => {
                let order = self.alloc_eval_order();
                self.pending.push(PendingExpr {
                    reg: start,
                    val: self.analysis.ssa.instr_def_value(iref, start),
                    anchor: iref,
                    expr: AstExpr::VarArg,
                    effect: EffectClass::Pure,
                    order,
                    is_building_table: false,
                    accepts_set_table: false,
                    is_luau_template: false,
                    luau_max_fields: None,
                    luau_force_index_keys: false,
                    is_luajit_indexed: false,
                    is_luajit_template: false,
                    table_sealed_by_setlist: false,
                    array_field_count: 0,
                    field_orders: Vec::new(),
                    open_producer: Some(iref),
                    method_lookup: None,
                });
            }
            ResultPack::Fixed(range) if range.len == 1 => {
                self.emit_single_def(iref, range.start, AstExpr::VarArg, out);
            }
            ResultPack::Fixed(range) if range.len > 1 => {
                self.flush_all_pending(out);
                let mut targets = Vec::with_capacity(range.len);
                for offset in 0..range.len {
                    let r = Reg(range.start.index() + offset);
                    targets.push(AstLValue::Name(self.name_for_def_at(iref, r)));
                }
                out.push(AstStmt::Assign(Box::new(AstAssign {
                    targets,
                    values: vec![AstExpr::VarArg],
                    compound_op: None,
                })));
            }
            ResultPack::Fixed(_) => {}
        }
    }

    // ── 常量与辅助映射 ───────────────────────────────────────

    pub(super) fn const_to_expr(&self, cref: ConstRef) -> AstExpr {
        let Some(lit) = self.proto.constants.get(cref.index()) else {
            return AstExpr::Nil;
        };
        match lit {
            RawLiteralConst::Nil => AstExpr::Nil,
            RawLiteralConst::Boolean(b) => AstExpr::Boolean(*b),
            RawLiteralConst::Integer(i) => AstExpr::Integer(*i),
            RawLiteralConst::Number(n) => AstExpr::Number(*n),
            RawLiteralConst::String(s) => AstExpr::String(LuaString::from_raw(s)),
            RawLiteralConst::Int64(i) => AstExpr::Int64(*i),
            RawLiteralConst::UInt64(u) => AstExpr::UInt64(*u),
            RawLiteralConst::Complex { real, imag } => AstExpr::Complex {
                real: *real,
                imag: *imag,
            },
            RawLiteralConst::Vector(v) => AstExpr::Vector(*v),
        }
    }

    pub(super) fn const_string_utf8(&self, cref: ConstRef) -> Option<String> {
        let RawLiteralConst::String(s) = self.proto.constants.get(cref.index())? else {
            return None;
        };
        std::str::from_utf8(&s.bytes).ok().map(ToOwned::to_owned)
    }

    fn access_key_expr(&self, key: AccessKey) -> AstExpr {
        match key {
            AccessKey::Const(c) => self.const_to_expr(c),
            AccessKey::Integer(i) => AstExpr::Integer(i),
            AccessKey::Reg(_) => unreachable!("register access key resolved earlier"),
        }
    }

    fn table_key_from_const(&self, cref: ConstRef) -> AstTableKey {
        if let Some(name) = self.const_string_utf8(cref)
            && self.target.version.is_identifier_name(&name)
        {
            return AstTableKey::Name(name);
        }
        AstTableKey::Expr(self.const_to_expr(cref))
    }

    fn expr_to_table_key(&self, expr: AstExpr) -> AstTableKey {
        if let AstExpr::String(ref s) = expr
            && let Some(name) = s.as_utf8()
            && self.target.version.is_identifier_name(name)
        {
            return AstTableKey::Name(name.to_owned());
        }
        AstTableKey::Expr(expr)
    }

    pub(super) fn upvalue_operand_name(&self, op: UpvalueOperand) -> AstNameRef {
        match op {
            UpvalueOperand::Env(_) => AstNameRef::Environment,
            UpvalueOperand::Upvalue(u) => AstNameRef::Upvalue(UpvalueId(u.index())),
        }
    }

    pub(super) fn upvalue_operand_expr(&self, op: UpvalueOperand) -> AstExpr {
        AstExpr::Var(self.upvalue_operand_name(op))
    }
}

fn merge_effect_class(a: EffectClass, b: EffectClass) -> EffectClass {
    match (a, b) {
        (EffectClass::MayObserveOrWrite, _) | (_, EffectClass::MayObserveOrWrite) => {
            EffectClass::MayObserveOrWrite
        }
        (EffectClass::ReadsState, _) | (_, EffectClass::ReadsState) => EffectClass::ReadsState,
        (EffectClass::Pure, EffectClass::Pure) => EffectClass::Pure,
    }
}

fn expr_is_pure_literal(expr: &AstExpr) -> bool {
    matches!(
        expr,
        AstExpr::Nil
            | AstExpr::Boolean(_)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_)
            | AstExpr::Int64(_)
            | AstExpr::UInt64(_)
            | AstExpr::Complex { .. }
            | AstExpr::Vector(_)
    )
}

fn table_field_is_pure_literal(field: &AstTableField) -> bool {
    match field {
        AstTableField::Array(v) => expr_is_pure_literal(v),
        AstTableField::Record(rec) => {
            let key_pure = match &rec.key {
                AstTableKey::Name(_) => true,
                AstTableKey::Expr(k) => expr_is_pure_literal(k),
            };
            key_pure && expr_is_pure_literal(&rec.value)
        }
    }
}

fn call_kind_to_expr(kind: AstCallKind) -> AstExpr {
    match kind {
        AstCallKind::Call(c) => AstExpr::Call(c),
        AstCallKind::MethodCall(m) => AstExpr::MethodCall(m),
    }
}

fn expr_to_call_kind(expr: AstExpr) -> AstCallKind {
    match expr {
        AstExpr::Call(c) => AstCallKind::Call(c),
        AstExpr::MethodCall(m) => AstCallKind::MethodCall(m),
        _ => unreachable!("expected call expr"),
    }
}

fn table_key_sort_key(key: &AstTableKey) -> (u8, i64, String) {
    match key {
        AstTableKey::Name(name) => (0, 0, name.clone()),
        AstTableKey::Expr(AstExpr::Integer(i)) => (1, *i, String::new()),
        AstTableKey::Expr(AstExpr::Number(n)) => (2, n.to_bits() as i64, String::new()),
        AstTableKey::Expr(AstExpr::String(s)) => (3, 0, s.display_text().into_owned()),
        AstTableKey::Expr(AstExpr::Boolean(b)) => (4, i64::from(*b), String::new()),
        AstTableKey::Expr(other) => (5, 0, format!("{other:?}")),
    }
}

fn stmt_mentions_name_shallow(stmt: &AstStmt, target: &AstNameRef) -> bool {
    match stmt {
        AstStmt::Assign(a) => {
            a.targets.iter().any(|t| match t {
                AstLValue::Name(n) => n == target,
                AstLValue::FieldAccess(f) => expr_mentions_name(&f.base, target),
                AstLValue::IndexAccess(ia) => {
                    expr_mentions_name(&ia.base, target) || expr_mentions_name(&ia.index, target)
                }
            }) || a.values.iter().any(|v| expr_mentions_name(v, target))
        }
        AstStmt::LocalDecl(d) => d.values.iter().any(|v| expr_mentions_name(v, target)),
        AstStmt::GlobalDecl(d) => d.values.iter().any(|v| expr_mentions_name(v, target)),
        AstStmt::CallStmt(c) => match &c.call {
            AstCallKind::Call(call) => {
                expr_mentions_name(&call.callee, target)
                    || call.args.iter().any(|a| expr_mentions_name(a, target))
            }
            AstCallKind::MethodCall(m) => {
                expr_mentions_name(&m.receiver, target)
                    || m.args.iter().any(|a| expr_mentions_name(a, target))
            }
        },
        AstStmt::If(i) => {
            expr_mentions_name(&i.cond, target)
                || i.then_block
                    .stmts
                    .iter()
                    .any(|s| stmt_mentions_name_shallow(s, target))
                || i.else_block.as_ref().is_some_and(|eb| {
                    eb.stmts
                        .iter()
                        .any(|s| stmt_mentions_name_shallow(s, target))
                })
        }
        AstStmt::DoBlock(b) => b.stmts.iter().any(|s| stmt_mentions_name_shallow(s, target)),
        _ => true,
    }
}

/// 以显式栈在 O(limit) 内检查表达式嵌套深度是否超过 `max_depth`，防止数千连环调用/二元链撑爆递归栈。
fn expr_depth_exceeds(root: &AstExpr, max_depth: usize) -> bool {
    let mut stack: Vec<(&AstExpr, usize)> = vec![(root, 0)];
    while let Some((expr, depth)) = stack.pop() {
        if depth > max_depth {
            return true;
        }
        let next = depth + 1;
        match expr {
            AstExpr::Unary(u) => stack.push((&u.expr, next)),
            AstExpr::Binary(b) => {
                stack.push((&b.lhs, next));
                stack.push((&b.rhs, next));
            }
            AstExpr::LogicalAnd(l) | AstExpr::LogicalOr(l) => {
                stack.push((&l.lhs, next));
                stack.push((&l.rhs, next));
            }
            AstExpr::IfExpr(ie) => {
                stack.push((&ie.cond, next));
                stack.push((&ie.then_expr, next));
                stack.push((&ie.else_expr, next));
            }
            AstExpr::FieldAccess(f) => stack.push((&f.base, next)),
            AstExpr::IndexAccess(ia) => {
                stack.push((&ia.base, next));
                stack.push((&ia.index, next));
            }
            AstExpr::Call(c) => {
                stack.push((&c.callee, next));
                for a in &c.args {
                    stack.push((a, next));
                }
            }
            AstExpr::MethodCall(m) => {
                stack.push((&m.receiver, next));
                for a in &m.args {
                    stack.push((a, next));
                }
            }
            AstExpr::SingleValue(inner) => stack.push((inner, next)),
            AstExpr::TableConstructor(tc) => {
                for f in &tc.fields {
                    match f {
                        AstTableField::Array(e) => stack.push((e, next)),
                        AstTableField::Record(r) => {
                            if let AstTableKey::Expr(k) = &r.key {
                                stack.push((k, next));
                            }
                            stack.push((&r.value, next));
                        }
                    }
                }
            }
            _ => {}
        }
    }
    false
}
