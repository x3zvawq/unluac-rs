//! 核对原调用与 scratch 覆盖所依赖的源码声明前缀，向 AST 发布身份保留要求。
//!
//! trusted home 是原槽身份，不是 locals allocator 对最终源码槽序的承诺。这里在 HIR
//! 收尾按实际保留的参数与声明顺序核对两者；例如原 callee 在 r3 时，前面必须恰好保留
//! 对应 r0、r1、r2 的三个身份。仅恢复调用内部相对槽距，不能容忍第四个额外 local。
//! 多个调用及其拟删除语句在同一次正向扫描中验证；只有整个事务通过才由调用方保留
//! 返回的声明集合。AST 消费 PhysicalFramePrefix，不重新读取寄存器或猜测原 CALL 布局。
//! 数值循环以原控制槽和用户 binding 共同进出声明栈；循环后的 assert 因而仍在原空闲槽准备。
//! 未证声明只阻止其仍活跃时的候选；已退出的循环 cell 不属于后缀调用的声明前缀。
//! 此处将未失效的唯一原 home 投影到源码槽序，不要求原 cell 的 epoch 为零。例如
//! `do local x; capture(x) end; assert(f())` 中已关闭的 r2 可供后续帧使用，原新 epoch
//! 仍由调用/capture owner 核对；位置相等不合并 binding，也不把根释放当作声明出栈。
//! 请求错位撤回该词法块的后缀，防止恢复的声明改变后续请求的前缀；正常退栈后仍可
//! 验证外层独立请求。声明状态无法解释时停止；撤回后从原快照重建并整体验证一次。

use std::collections::{BTreeMap, BTreeSet};

use crate::decompile::DecompileDialect;
use crate::hir::common::{
    HirBinding, HirBlock, HirInlineRetentionReason, HirLValue, HirProto, HirStmt, LocalId, TempId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};
use crate::hir::simplify::mention::BindingReadCollector;
use crate::hir::visit::{HirVisitor, visit_stmts};

pub(super) mod coordinates;
mod materializations;
pub(super) use materializations::close_gc_inert_terminal_prefix;
pub(super) use materializations::{pending_nil_prefix_temps, restore_materializations};

/// 候选除原 freereg 外，还可要求特定低槽身份在开始前已声明；不能借后缀新声明替代。
pub(super) struct PrefixRequest {
    pub(super) home: HomeSlotKey,
    pub(super) required: BTreeSet<LocalId>,
}

/// 请求不匹配撤回当前词法作用域的后缀；无法解释声明栈时，整个后缀未知。
/// 例如循环体内的错位帧不阻止退出该作用域后验证外层帧。消费者撤回计划后仍须
/// 重建预览并整批验证，不能把这个快照中的其它成功请求直接当作提交许可。
/// 区间覆盖本次请求窗口；扫描可能在最后请求处结束，不用于查询任意后续坐标。
pub(super) struct PrefixFailures {
    rejected: BTreeMap<usize, usize>,
    invalid_from: Option<usize>,
}

impl PrefixFailures {
    pub(super) fn invalid_from(index: usize) -> Self {
        Self {
            rejected: BTreeMap::new(),
            invalid_from: Some(index),
        }
    }

    pub(super) fn first(&self) -> usize {
        self.rejected
            .first_key_value()
            .map(|(&start, _)| start)
            .into_iter()
            .chain(self.invalid_from)
            .min()
            .expect("prefix failure contains a rejected request or invalid suffix")
    }

    pub(super) fn rejects(&self, start: usize) -> bool {
        self.rejected
            .range(..=start)
            .next_back()
            .is_some_and(|(_, &end)| start < end)
            || self.invalid_from.is_some_and(|index| start >= index)
    }

    /// 后缀帧属于更早的根退休事务时，将其失败归回该 owner，不能局部接受依赖链。
    pub(super) fn with_dependent_suffix(mut self, owner: Option<usize>) -> Self {
        if let Some(owner) = owner
            && (self.rejected.values().any(|&end| end > owner)
                || self.invalid_from.is_some_and(|index| index >= owner))
        {
            self.invalid_from = Some(self.invalid_from.map_or(owner, |index| index.min(owner)));
        }
        self
    }
}

/// COPY 的旧槽覆盖及返回残根要求实际源码前缀与原 home 一致；只保留 COPY local 不足以证明。
/// 复用调用帧的声明验证，避免 AST 删除低槽参数别名后让全部 scratch 左移。
pub(super) fn preserve_copy_prefixes(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
) -> bool {
    let locals = facts.physical_copy_prefix_locals(&proto.physical_root_locals);
    if locals.is_empty() {
        return false;
    }
    struct Candidates<'a> {
        locals: &'a BTreeSet<LocalId>,
        facts: &'a ProtoPromotionFacts,
        cursor: usize,
        starts: BTreeMap<usize, PrefixRequest>,
    }
    impl Candidates<'_> {
        fn visit_stmt(&mut self, index: usize, stmt: &HirStmt) {
            if let HirStmt::LocalDecl(decl) = stmt
                && let [local] = decl.bindings.as_slice()
                && self.locals.contains(local)
                && let Some(home) = self.facts.trusted_local_home_slot(*local)
            {
                self.starts.insert(
                    index,
                    PrefixRequest {
                        home,
                        required: BTreeSet::new(),
                    },
                );
            }
        }
    }
    let mut scan = Candidates {
        locals: &locals,
        facts,
        cursor: 0,
        starts: BTreeMap::new(),
    };
    let mut cursor = 0;
    coordinates::visit(&proto.body, &mut cursor, &mut |index, kind, stmt| {
        if kind == coordinates::PointKind::Statement {
            scan.visit_stmt(index, stmt);
        }
    });
    scan.cursor = cursor;
    preserve_prefix_requests(
        proto,
        facts,
        dialect,
        is_chunk_entry,
        scan.cursor,
        scan.starts,
    )
}

/// 已由各帧 owner 核对的入口请求，共用一次声明扫描发布保留事实；不改写 HIR 语句。
pub(super) fn preserve_prefix_requests(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
    stmt_count: usize,
    mut starts: BTreeMap<usize, PrefixRequest>,
) -> bool {
    let removed = vec![false; stmt_count];
    let preserved = match validate_prefixes(
        proto,
        facts,
        dialect,
        is_chunk_entry,
        &removed,
        &starts,
        false,
    ) {
        Ok(preserved) => preserved,
        Err(failures) => {
            // 一次截断只保留已通过的独立前缀；不为每个候选重扫整个 proto。
            drop(starts.split_off(&failures.first()));
            let Ok(preserved) = validate_prefixes(
                proto,
                facts,
                dialect,
                is_chunk_entry,
                &removed,
                &starts,
                false,
            ) else {
                return false;
            };
            preserved
        }
    };
    let mut changed = false;
    for local in preserved {
        changed |= proto
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    changed
}

/// 词法 Block、If/While 子块及已有原槽协议的 for 使用声明栈；Repeat 的声明延续到尾条件点。
/// candidates 使用 coordinates 的全 proto 帧坐标，removed 必须覆盖同一快照。成功集合尚未发布；
/// 失败区分可继续扫描的请求拒绝与未知后缀，调用方撤回相关计划后必须整批重验。
/// scan_suffix 用于新增声明的完整事务：最后一次写之后仍须检查其余 owner，不能只证明起点。
pub(super) fn validate_prefixes(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
    removed: &[bool],
    candidates: &BTreeMap<usize, PrefixRequest>,
    scan_suffix: bool,
) -> Result<BTreeSet<LocalId>, PrefixFailures> {
    let Some((&last_candidate, _)) = candidates.last_key_value() else {
        return Ok(BTreeSet::new());
    };
    if last_candidate >= removed.len() {
        return Err(PrefixFailures::invalid_from(0));
    }
    let last_start = if scan_suffix {
        removed.len() - 1
    } else {
        last_candidate
    };
    for (slot, &param) in proto.params.iter().enumerate() {
        if facts.trusted_param_home_slot(param).map(HomeSlotKey::slot) != Some(slot) {
            return Err(PrefixFailures::invalid_from(0));
        }
    }

    let mut declared = BTreeSet::new();
    let mut header_slots = proto.params.len();
    if let Some(local) = proto.vararg_param_local {
        // Lua 5.1 的 parlist 为 HASARG 保留一槽；省略号决定重编译时是否清除
        // NEEDSARG。必须匹配原入口的建表事实，不能仅凭槽存在推断 GC 分配相同。
        let header_supported = match dialect {
            DecompileDialect::Lua55 => !proto.signature.legacy_arg_slot,
            DecompileDialect::Lua51 if proto.signature.legacy_arg_slot && !is_chunk_entry => {
                struct VarargUse(bool);
                impl HirVisitor<'_> for VarargUse {
                    fn is_complete(&self) -> bool {
                        self.0
                    }
                    fn visit_expr(&mut self, expr: &crate::hir::common::HirExpr) {
                        self.0 |= matches!(expr, crate::hir::common::HirExpr::VarArg);
                    }
                }
                let mut usage = VarargUse(false);
                visit_stmts(&proto.body.stmts, &mut usage);
                usage.0 != proto.signature.legacy_arg_table
            }
            _ => false,
        };
        if !header_supported
            || !proto.signature.is_vararg
            || !proto.signature.has_vararg_param_reg
            || facts.trusted_local_home_slot(local).map(HomeSlotKey::slot) != Some(header_slots)
        {
            return Err(PrefixFailures::invalid_from(0));
        }
        if !is_chunk_entry {
            // chunk 的 entry 从模块 body 发射，不经过函数 parlist；Lua 5.5 main
            // 虽初始化该槽为 nil，却不保留参数声明，第一条普通写即可复用该槽。
            declared.insert(local);
            header_slots += 1;
        }
    }
    let mut read_temps = BTreeSet::new();
    visit_stmts(
        &proto.body.stmts,
        &mut BindingReadCollector(|binding| {
            if let HirBinding::Temp(temp) = binding {
                read_temps.insert(temp);
            }
        }),
    );
    let mut scan = PrefixScan {
        facts,
        removed,
        candidates,
        last_start,
        cursor: 0,
        header_slots,
        locals: Vec::new(),
        declared,
        pending: BTreeSet::new(),
        preserved: BTreeSet::new(),
        rejected: BTreeMap::new(),
        scope_rejected: None,
        unproven_prefix: false,
        read_temps,
        scan_suffix,
    };
    let invalid_from = scan.block(&proto.body).err();
    if invalid_from.is_some() || !scan.rejected.is_empty() {
        // 嵌套块的区间可能被父块包含；合并后才能用一次前驱查询判断候选。
        let mut rejected = BTreeMap::<usize, usize>::new();
        for (start, end) in scan.rejected {
            if let Some(mut previous) = rejected.last_entry()
                && *previous.get() >= start
            {
                *previous.get_mut() = (*previous.get()).max(end);
            } else {
                rejected.insert(start, end);
            }
        }
        Err(PrefixFailures {
            rejected,
            invalid_from,
        })
    } else {
        Ok(scan.preserved)
    }
}

struct PrefixScan<'a> {
    facts: &'a ProtoPromotionFacts,
    removed: &'a [bool],
    candidates: &'a BTreeMap<usize, PrefixRequest>,
    last_start: usize,
    cursor: usize,
    header_slots: usize,
    locals: Vec<Option<LocalId>>,
    declared: BTreeSet<LocalId>,
    pending: BTreeSet<usize>,
    preserved: BTreeSet<LocalId>,
    rejected: BTreeMap<usize, usize>,
    scope_rejected: Option<usize>,
    unproven_prefix: bool,
    read_temps: BTreeSet<TempId>,
    scan_suffix: bool,
}

impl PrefixScan<'_> {
    fn block(&mut self, block: &HirBlock) -> Result<(), usize> {
        self.block_contents(block, false)
    }

    fn check_request(&mut self, index: usize) -> bool {
        if let Some(request) = self.candidates.get(&index) {
            if self.unproven_prefix
                || request.home.slot() != self.header_slots + self.locals.len()
                || !request.required.is_subset(&self.declared)
            {
                return false;
            }
            for pending in std::mem::take(&mut self.pending) {
                self.preserved
                    .insert(self.locals[pending].expect("only named slots are pending"));
            }
        }
        true
    }

    fn block_contents(&mut self, block: &HirBlock, keep_scope: bool) -> Result<(), usize> {
        // 候选撤回后，原声明重新占槽；依赖这些槽的同块后缀必须一并撤回。
        // 子块出栈后该依赖结束，不沿先序坐标误伤外层后缀，也不为每个请求重扫树。
        let incoming = self.scope_rejected.take();
        let result = self.scan_block_contents(block, keep_scope);
        if let Some(start) = self.scope_rejected.take() {
            // repeat 的 body 声明仍延续到额外的 condition 坐标。
            self.rejected
                .insert(start, self.cursor + usize::from(keep_scope));
        }
        self.scope_rejected = incoming;
        result
    }

    fn scan_block_contents(&mut self, block: &HirBlock, keep_scope: bool) -> Result<(), usize> {
        let scope_start = self.locals.len();
        let incoming_unproven = self.unproven_prefix;
        for stmt in &block.stmts {
            if self.cursor > self.last_start {
                break;
            }
            let index = self.cursor;
            self.cursor += 1;
            if !self.check_request(index) {
                self.scope_rejected.get_or_insert(index);
            }
            if index == self.last_start && !self.scan_suffix {
                break;
            }
            if *self.removed.get(index).ok_or(index)? {
                // 删除整块只取消其声明效果，后续请求仍使用原快照的 DFS 坐标。
                crate::hir::visit::for_each_nested_block(stmt, &mut |child| {
                    coordinates::visit(child, &mut self.cursor, &mut |_, _, _| {});
                });
                if matches!(stmt, HirStmt::Repeat(_)) {
                    self.cursor += 1;
                }
                continue;
            }
            if let HirStmt::Block(child) = stmt {
                self.block(child)?;
                continue;
            }
            if let HirStmt::Repeat(repeat) = stmt {
                let repeat_start = self.locals.len();
                let repeat_unproven = self.unproven_prefix;
                self.block_contents(&repeat.body, true)?;
                // 条件在 body 的局部作用域内，额外坐标与 coordinates owner 一致。
                if self.cursor <= self.last_start {
                    let condition = self.cursor;
                    self.cursor += 1;
                    if !self.check_request(condition) {
                        self.rejected.insert(condition, condition + 1);
                    }
                    if self.removed.get(condition) != Some(&false) {
                        return Err(condition);
                    }
                    let mut has_temp = false;
                    crate::hir::visit::visit_stmt_header(
                        stmt,
                        &mut BindingReadCollector(|binding| {
                            has_temp |= matches!(binding, HirBinding::Temp(_));
                        }),
                    );
                    if has_temp {
                        return Err(condition);
                    }
                }
                self.leave_scope(repeat_start);
                self.unproven_prefix = repeat_unproven;
                continue;
            }
            let mut has_temp = false;
            let mut reads = BindingReadCollector(|binding| {
                has_temp |= matches!(binding, HirBinding::Temp(_));
            });
            if matches!(
                stmt,
                HirStmt::GenericFor(_)
                    | HirStmt::NumericFor(_)
                    | HirStmt::If(_)
                    | HirStmt::While(_)
            ) {
                crate::hir::visit::visit_stmt_header(stmt, &mut reads);
            } else {
                visit_stmts(std::slice::from_ref(stmt), &mut reads);
            }
            if has_temp {
                return Err(index);
            }
            match stmt {
                HirStmt::LocalDecl(decl) => {
                    for &local in &decl.bindings {
                        let slot = self.header_slots + self.locals.len();
                        if !self.declared.insert(local) {
                            return Err(index);
                        }
                        self.unproven_prefix |= self
                            .facts
                            .trusted_local_home_slot(local)
                            .map(HomeSlotKey::slot)
                            != Some(slot);
                        if !self.preserved.contains(&local) {
                            self.pending.insert(self.locals.len());
                        }
                        self.locals.push(Some(local));
                    }
                }
                HirStmt::NumericFor(for_) => {
                    let frame = self.facts.numeric_for_body_frame(for_).ok_or(index)?;
                    let loop_start = self.locals.len();
                    for &home in &frame.controls[..frame.controls_len] {
                        if home.slot() != self.header_slots + self.locals.len() {
                            return Err(index);
                        }
                        self.locals.push(None);
                    }
                    if frame.binding_slot != self.header_slots + self.locals.len()
                        || !self.declared.insert(for_.binding)
                    {
                        return Err(index);
                    }
                    if !self.preserved.contains(&for_.binding) {
                        self.pending.insert(self.locals.len());
                    }
                    self.locals.push(Some(for_.binding));
                    self.block(&for_.body)?;
                    self.leave_scope(loop_start);
                }
                HirStmt::GenericFor(for_) => {
                    let frame = self.facts.generic_for_body_frame(for_).ok_or(index)?;
                    let loop_start = self.locals.len();
                    for &home in &frame.controls {
                        if home.slot() != self.header_slots + self.locals.len() {
                            return Err(index);
                        }
                        self.locals.push(None);
                    }
                    for (&local, &home) in for_.bindings.iter().zip(&frame.bindings) {
                        if home.slot() != self.header_slots + self.locals.len()
                            || !self.declared.insert(local)
                        {
                            return Err(index);
                        }
                        if !self.preserved.contains(&local) {
                            self.pending.insert(self.locals.len());
                        }
                        self.locals.push(Some(local));
                    }
                    self.locals
                        .extend(std::iter::repeat_n(None, frame.binding_padding));
                    self.block(&for_.body)?;
                    self.leave_scope(loop_start);
                }
                HirStmt::If(if_) => {
                    self.block(&if_.then_block)?;
                    if let Some(else_block) = &if_.else_block {
                        self.block(else_block)?;
                    }
                }
                HirStmt::While(while_) => {
                    // while 不创建隐式控制 local；body 进入/退出与条件前使用同一声明前缀。
                    // 这里只核对已恢复词法布局，不推导循环值或删除循环内的物理写。
                    self.block(&while_.body)?;
                }
                HirStmt::Assign(assign)
                    if assign.targets.iter().all(|target| match target {
                        HirLValue::Temp(temp) => !self.read_temps.contains(temp),
                        HirLValue::Local(local) => self.declared.contains(local),
                        _ => true,
                    }) =>
                {
                    // 无读取或捕获的 Temp 不会为后续使用跨块提升声明，因此未知
                    // 占槽只影响当前词法作用域。读取集合覆盖最后一个帧请求之后，
                    // 防止提前结束扫描而漏掉后缀逃逸；有使用的 Temp 仍拒绝整个后缀。
                    self.unproven_prefix |= assign
                        .targets
                        .iter()
                        .any(|target| matches!(target, HirLValue::Temp(_)));
                }
                HirStmt::GlobalDecl(_)
                | HirStmt::CallStmt(_)
                | HirStmt::Return(_)
                | HirStmt::Break
                | HirStmt::Continue => {}
                HirStmt::ToBeClosed(tbc)
                    if matches!(tbc.value, crate::hir::common::HirExpr::LocalRef(local)
                        if self.declared.contains(&local)
                            && self.facts.trusted_local_home_slot(local)
                                == Some(self.facts.tbc_home(tbc.origin))) =>
                {
                    // TBC 激活已声明的同一槽，不新增声明位置；其资源与关闭边界仍由原
                    // owner 保留。后续帧可以验证该前缀，不能吸收或移动这条 activation。
                }
                HirStmt::LocalRootRelease(local) if self.declared.contains(local) => {}
                _ => return Err(index),
            }
        }
        if !keep_scope {
            self.leave_scope(scope_start);
            self.unproven_prefix = incoming_unproven;
        }
        Ok(())
    }

    fn leave_scope(&mut self, scope_start: usize) {
        for local in self.locals.drain(scope_start..).flatten() {
            self.declared.remove(&local);
        }
        drop(self.pending.split_off(&scope_start));
    }
}
