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

use std::collections::{BTreeMap, BTreeSet};

use crate::decompile::DecompileDialect;
use crate::hir::common::{
    HirBinding, HirBlock, HirInlineRetentionReason, HirLValue, HirProto, HirStmt, LocalId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};
use crate::hir::simplify::mention::BindingReadCollector;
use crate::hir::visit::{HirVisitor, visit_stmts};

mod nil_writes;
pub(super) use nil_writes::restore_nil_writes;

/// 候选除原 freereg 外，还可要求特定低槽身份在开始前已声明；不能借后缀新声明替代。
pub(super) struct PrefixRequest {
    pub(super) home: HomeSlotKey,
    pub(super) required: BTreeSet<LocalId>,
}

/// COPY 的旧槽覆盖要求实际源码前缀与原 home 一致；单独保留 COPY local 不足以证明。
/// 复用调用帧的声明验证，避免 AST 删除低槽参数别名后让全部 scratch 左移。
pub(super) fn preserve_scratch_prefixes(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
) -> bool {
    let locals = facts.scratch_overwrite_locals();
    if locals.is_empty() {
        return false;
    }
    struct Candidates<'a> {
        locals: &'a BTreeSet<LocalId>,
        facts: &'a ProtoPromotionFacts,
        cursor: usize,
        starts: BTreeMap<usize, PrefixRequest>,
    }
    impl HirVisitor<'_> for Candidates<'_> {
        fn visit_stmt(&mut self, stmt: &HirStmt) {
            if let HirStmt::LocalDecl(decl) = stmt
                && let [local] = decl.bindings.as_slice()
                && self.locals.contains(local)
                && let Some(home) = self.facts.trusted_local_home_slot(*local)
            {
                self.starts.insert(
                    self.cursor,
                    PrefixRequest {
                        home,
                        required: BTreeSet::new(),
                    },
                );
            }
            self.cursor += 1;
        }
    }
    let mut scan = Candidates {
        locals: &locals,
        facts,
        cursor: 0,
        starts: BTreeMap::new(),
    };
    visit_stmts(&proto.body.stmts, &mut scan);
    let removed = vec![false; scan.cursor];
    let preserved = match validate_prefixes(
        proto,
        facts,
        dialect,
        is_chunk_entry,
        &removed,
        &scan.starts,
        false,
    ) {
        Ok(preserved) => preserved,
        Err(index) => {
            // 一次截断只保留已通过的独立前缀；不为每个候选重扫整个 proto。
            drop(scan.starts.split_off(&index));
            let Ok(preserved) = validate_prefixes(
                proto,
                facts,
                dialect,
                is_chunk_entry,
                &removed,
                &scan.starts,
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

/// 词法 Block、If/While 子块及已有原槽协议的 for 使用声明栈；未知资源和未物化 Temp 不签证。
/// candidates 使用全 proto 的词法 DFS 坐标，removed 必须覆盖同一快照。成功集合尚未发布；
/// 失败返回首个未证位置，调用方可截断独立候选前缀后统一重验，不能忽略中间声明。
/// scan_suffix 用于新增声明的完整事务：最后一次写之后仍须检查其余 owner，不能只证明起点。
pub(super) fn validate_prefixes(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
    removed: &[bool],
    candidates: &BTreeMap<usize, PrefixRequest>,
    scan_suffix: bool,
) -> Result<BTreeSet<LocalId>, usize> {
    let Some((&last_candidate, _)) = candidates.last_key_value() else {
        return Ok(BTreeSet::new());
    };
    if last_candidate >= removed.len() {
        return Err(0);
    }
    let last_start = if scan_suffix {
        removed.len() - 1
    } else {
        last_candidate
    };
    for (slot, &param) in proto.params.iter().enumerate() {
        if facts.trusted_param_home_slot(param).map(HomeSlotKey::slot) != Some(slot) {
            return Err(0);
        }
    }

    let mut declared = BTreeSet::new();
    let mut header_slots = proto.params.len();
    if let Some(local) = proto.vararg_param_local {
        // Lua 5.5 的签名明确包含原隐式变参槽；目标编译器仍在固定参数后保留该槽。
        // legacy arg 有不同建表/兼容语义，不能借这个签名证明。
        if dialect != DecompileDialect::Lua55
            || !proto.signature.is_vararg
            || !proto.signature.has_vararg_param_reg
            || proto.signature.legacy_arg_slot
            || facts.trusted_local_home_slot(local).map(HomeSlotKey::slot) != Some(header_slots)
        {
            return Err(0);
        }
        if !is_chunk_entry {
            // chunk 的 entry 从模块 body 发射，不经过函数 parlist；Lua 5.5 main
            // 虽初始化该槽为 nil，却不保留参数声明，第一条普通写即可复用该槽。
            declared.insert(local);
            header_slots += 1;
        }
    }
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
        unproven_prefix: false,
        scan_suffix,
    };
    scan.block(&proto.body)?;
    Ok(scan.preserved)
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
    unproven_prefix: bool,
    scan_suffix: bool,
}

impl PrefixScan<'_> {
    fn block(&mut self, block: &HirBlock) -> Result<(), usize> {
        let scope_start = self.locals.len();
        let incoming_unproven = self.unproven_prefix;
        for stmt in &block.stmts {
            if self.cursor > self.last_start {
                break;
            }
            let index = self.cursor;
            self.cursor += 1;
            if let Some(request) = self.candidates.get(&index) {
                // 候选拒绝[ProofIncomplete]：精确原 home 已由调用方持有；这里验证源码位置及活动声明身份。
                if self.unproven_prefix
                    || request.home.slot() != self.header_slots + self.locals.len()
                    || !request.required.is_subset(&self.declared)
                {
                    return Err(index);
                }
                // 每个身份只发布一次；不在每个嵌套 block 重扫/复制整个祖先前缀。
                for pending in std::mem::take(&mut self.pending) {
                    self.preserved
                        .insert(self.locals[pending].expect("only named slots are pending"));
                }
            }
            if index == self.last_start && !self.scan_suffix {
                break;
            }
            if *self.removed.get(index).ok_or(index)? {
                continue;
            }
            if let HirStmt::Block(child) = stmt {
                self.block(child)?;
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
                    if frame.binding.slot() != self.header_slots + self.locals.len()
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
                        HirLValue::Temp(_) => false,
                        HirLValue::Local(local) => self.declared.contains(local),
                        _ => true,
                    }) => {}
                HirStmt::CallStmt(_) | HirStmt::Return(_) | HirStmt::Break | HirStmt::Continue => {}
                HirStmt::LocalRootRelease(local) if self.declared.contains(local) => {}
                _ => return Err(index),
            }
        }
        self.leave_scope(scope_start);
        self.unproven_prefix = incoming_unproven;
        Ok(())
    }

    fn leave_scope(&mut self, scope_start: usize) {
        for local in self.locals.drain(scope_start..).flatten() {
            self.declared.remove(&local);
        }
        drop(self.pending.split_off(&scope_start));
    }
}
