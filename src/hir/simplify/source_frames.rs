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
use crate::hir::simplify::mention::{BindingReadCollector, BindingWriteCollector};
use crate::hir::visit::{HirVisitor, visit_stmts};

pub(super) mod coordinates;
mod materializations;
pub(super) use materializations::{close_gc_inert_terminal_prefix, indexed_assignment_frame};
pub(super) use materializations::{
    pending_nil_prefix_temps, restore_materializations, restore_split_nil_declarations,
};

/// 臂首原 CALL 及其准备写均位于条件输入之上时，该输入仍占据声明前缀。
/// 只检查连续准备区；任何低槽写或控制结构都会结束本次证明。
pub(super) fn branch_entry_requires_prefix(
    branch: &crate::hir::common::HirIf,
    home: HomeSlotKey,
    facts: &ProtoPromotionFacts,
) -> bool {
    std::iter::once(&branch.then_block)
        .chain(branch.else_block.as_ref())
        .any(|block| {
            for stmt in &block.stmts {
                let (call, target) = match stmt {
                    HirStmt::CallStmt(stmt) => (Some(&stmt.call), None),
                    _ => {
                        let Some((binding, value)) = super::call_frames::scalar_binding(stmt)
                        else {
                            return false;
                        };
                        let target = match binding {
                            HirBinding::Temp(temp) => facts.trusted_temp_home_slot(temp),
                            HirBinding::Local(local) => facts.trusted_local_home_slot(local),
                            _ => None,
                        };
                        let call = match value {
                            crate::hir::common::HirExpr::Call(call) => Some(call.as_ref()),
                            _ => None,
                        };
                        (call, target)
                    }
                };
                if let Some(call) = call {
                    return facts
                        .native_call_layout(call)
                        .is_some_and(|frame| frame.home.slot() > home.slot());
                }
                if target.is_none_or(|target| target.slot() <= home.slot()) {
                    return false;
                }
            }
            false
        })
}

/// 候选除原 freereg 外，还可要求特定低槽身份在开始前已声明；不能借后缀新声明替代。
pub(super) struct PrefixRequest {
    pub(super) home: HomeSlotKey,
    pub(super) required: BTreeSet<LocalId>,
}

/// 请求不匹配撤回当前词法作用域的后缀；无法解释声明栈时，整个后缀未知。
/// 例如循环体内的错位帧不阻止退出该作用域后验证外层帧。消费者撤回计划后仍须
/// 重建预览并整批验证，不能把这个快照中的其它成功请求直接当作提交许可。
/// 区间覆盖本次请求窗口；扫描可能在最后请求处结束，不用于查询任意后续坐标。
#[derive(Debug)]
pub(super) struct PrefixFailures {
    dependent_owners: BTreeSet<usize>,
    rejected: BTreeMap<usize, usize>,
    invalid_from: Option<usize>,
}

impl PrefixFailures {
    pub(super) fn invalid_from(index: usize) -> Self {
        Self {
            dependent_owners: BTreeSet::new(),
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
            .chain(self.dependent_owners.iter().copied())
            .min()
            .expect("prefix failure contains a rejected request or invalid suffix")
    }

    pub(super) fn rejects(&self, start: usize) -> bool {
        self.dependent_owners.contains(&start)
            || self
                .rejected
                .range(..=start)
                .next_back()
                .is_some_and(|(_, &end)| start < end)
            || self.invalid_from.is_some_and(|index| start >= index)
    }

    /// 声明恢复只依赖实际使用其前缀的请求；兄弟作用域的失败不能扩散到整个 DFS 后缀。
    pub(super) fn with_dependent_owners(mut self, owners: impl IntoIterator<Item = usize>) -> Self {
        self.dependent_owners.extend(owners);
        self
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
    struct GlobalKeys<'a> {
        facts: &'a ProtoPromotionFacts,
        keys: BTreeMap<TempId, crate::LuaString>,
        reads: BTreeSet<TempId>,
    }
    impl HirVisitor<'_> for GlobalKeys<'_> {
        fn visit_expr(&mut self, expr: &crate::hir::common::HirExpr) {
            match expr {
                crate::hir::common::HirExpr::GlobalRef(global) => {
                    if let Some(temp) = self.facts.global_read_key_preparation(global) {
                        self.keys.insert(temp, global.key.clone());
                    }
                }
                crate::hir::common::HirExpr::TempRef(temp) => {
                    self.reads.insert(*temp);
                }
                _ => {}
            }
        }
    }
    let mut global_keys = GlobalKeys {
        facts,
        keys: BTreeMap::new(),
        reads: BTreeSet::new(),
    };
    coordinates::visit(&proto.body, &mut 0, &mut |index, kind, stmt| {
        if kind == coordinates::PointKind::Statement && removed.get(index) == Some(&false) {
            crate::hir::visit::visit_stmt_header(stmt, &mut global_keys);
        }
    });
    global_keys.keys.retain(|temp, _| {
        !global_keys.reads.contains(temp)
            && proto.temp_debug_locals[temp.index()].is_none()
            && proto.temp_debug_scopes[temp.index()].is_none()
    });
    let temp_scopes = TemporaryScopes::new(&proto.body, removed);
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
        temp_scopes,
        global_keys: global_keys.keys,
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
            dependent_owners: BTreeSet::new(),
            rejected,
            invalid_from,
        })
    } else {
        Ok(scan.preserved)
    }
}

/// Temp 尚未物化时，只污染其所有读写的最小公共词法作用域。
/// 用倍增祖先求 LCA，避免深层输入反复向根扫描；每轮改写后重新建立索引。
struct TemporaryScopes {
    shared: BTreeSet<usize>,
}

impl TemporaryScopes {
    fn new(body: &HirBlock, removed: &[bool]) -> Self {
        struct Scope {
            entry: usize,
            depth: usize,
            ancestors: Vec<usize>,
        }
        struct Builder<'a> {
            removed: &'a [bool],
            scopes: Vec<Scope>,
            owners: BTreeMap<TempId, usize>,
            first: BTreeMap<TempId, (usize, usize)>,
            shared: BTreeSet<TempId>,
            cursor: usize,
        }
        impl Builder<'_> {
            fn ancestor(&self, scope: usize, power: usize) -> usize {
                self.scopes[scope]
                    .ancestors
                    .get(power)
                    .copied()
                    .unwrap_or(0)
            }
            fn common(&self, mut left: usize, mut right: usize) -> usize {
                if self.scopes[left].depth < self.scopes[right].depth {
                    std::mem::swap(&mut left, &mut right);
                }
                let difference = self.scopes[left].depth - self.scopes[right].depth;
                for power in 0..usize::BITS as usize {
                    if difference & (1usize << power) != 0 {
                        left = self.ancestor(left, power);
                    }
                }
                if left == right {
                    return left;
                }
                for power in (0..self.scopes[left].ancestors.len()).rev() {
                    let a = self.ancestor(left, power);
                    let b = self.ancestor(right, power);
                    if a != b {
                        left = a;
                        right = b;
                    }
                }
                self.ancestor(left, 0)
            }
            fn block(&mut self, block: &HirBlock, parent: Option<usize>, entry: usize) {
                let scope = self.scopes.len();
                let depth = parent.map_or(0, |parent| self.scopes[parent].depth + 1);
                let mut ancestors = vec![parent.unwrap_or(0)];
                let mut power = 1;
                while (1usize << power) <= depth {
                    ancestors.push(self.ancestor(ancestors[power - 1], power - 1));
                    power += 1;
                }
                self.scopes.push(Scope {
                    entry,
                    depth,
                    ancestors,
                });
                for stmt in &block.stmts {
                    let statement = self.cursor;
                    self.cursor += 1;
                    if self.removed.get(statement) == Some(&true) {
                        crate::hir::visit::for_each_nested_block(stmt, &mut |child| {
                            coordinates::visit(child, &mut self.cursor, &mut |_, _, _| {})
                        });
                        self.cursor += usize::from(matches!(stmt, HirStmt::Repeat(_)));
                        continue;
                    }
                    let mut record = |binding| {
                        if let HirBinding::Temp(temp) = binding {
                            self.first.entry(temp).or_insert((scope, statement));
                            let owner = self.owners.get(&temp).copied();
                            let merged = owner.map_or(scope, |owner| self.common(owner, scope));
                            if owner.is_some_and(|owner| owner != scope) {
                                self.shared.insert(temp);
                            }
                            self.owners.insert(temp, merged);
                        }
                    };
                    crate::hir::visit::visit_stmt_header(
                        stmt,
                        &mut BindingReadCollector(&mut record),
                    );
                    crate::hir::visit::visit_stmt_header(
                        stmt,
                        &mut BindingWriteCollector(&mut record),
                    );
                    crate::hir::visit::for_each_nested_block(stmt, &mut |child| {
                        self.block(child, Some(scope), statement)
                    });
                    self.cursor += usize::from(matches!(stmt, HirStmt::Repeat(_)));
                }
            }
        }
        let mut builder = Builder {
            removed,
            scopes: Vec::new(),
            owners: BTreeMap::new(),
            first: BTreeMap::new(),
            shared: BTreeSet::new(),
            cursor: 0,
        };
        builder.block(body, None, 0);
        Self {
            shared: builder
                .shared
                .iter()
                .map(|temp| {
                    let owner = builder.owners[temp];
                    let (mut first, statement) = builder.first[temp];
                    if first == owner {
                        return statement;
                    }
                    let distance = builder.scopes[first].depth - builder.scopes[owner].depth - 1;
                    for power in 0..usize::BITS as usize {
                        if distance & (1usize << power) != 0 {
                            first = builder.ancestor(first, power);
                        }
                    }
                    builder.scopes[first].entry
                })
                .collect(),
        }
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
    temp_scopes: TemporaryScopes,
    global_keys: BTreeMap<TempId, crate::LuaString>,
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
            self.unproven_prefix |= self.temp_scopes.shared.contains(&index);
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
                if let HirBinding::Temp(_) = binding {
                    has_temp = true;
                }
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

            // 同块 Temp 的最终声明尚未知，只阻止该作用域内的候选；退出子块后，
            // 不把它错误传播为外层后缀的未知前缀。跨块使用仍须先恢复身份。
            self.unproven_prefix |= has_temp;
            match stmt {
                HirStmt::LocalDecl(decl) => {
                    for &local in &decl.bindings {
                        let slot = self.header_slots + self.locals.len();
                        if !self.declared.insert(local) {
                            // 同一身份重复声明使当前候选无效，但不会改变父块的声明栈。
                            // 记录本块失败并占住未证明的源码槽，继续收集独立兄弟块的请求。
                            self.scope_rejected.get_or_insert(index);
                            self.unproven_prefix = true;
                            self.locals.push(None);
                            continue;
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
                    let loop_unproven = self.unproven_prefix;
                    for &home in &frame.controls[..frame.controls_len] {
                        self.unproven_prefix |=
                            home.slot() != self.header_slots + self.locals.len();
                        self.locals.push(None);
                    }
                    self.unproven_prefix |=
                        frame.binding_slot != self.header_slots + self.locals.len();
                    if !self.declared.insert(for_.binding) {
                        return Err(index);
                    }
                    if !self.preserved.contains(&for_.binding) {
                        self.pending.insert(self.locals.len());
                    }
                    self.locals.push(Some(for_.binding));
                    self.block(&for_.body)?;
                    self.leave_scope(loop_start);
                    self.unproven_prefix = loop_unproven;
                }
                HirStmt::GenericFor(for_) => {
                    let frame = self.facts.generic_for_body_frame(for_).ok_or(index)?;
                    let loop_start = self.locals.len();
                    let loop_unproven = self.unproven_prefix;
                    for &home in &frame.controls {
                        self.unproven_prefix |=
                            home.slot() != self.header_slots + self.locals.len();
                        self.locals.push(None);
                    }
                    for (&local, &home) in for_.bindings.iter().zip(&frame.bindings) {
                        self.unproven_prefix |=
                            home.slot() != self.header_slots + self.locals.len();
                        if !self.declared.insert(local) {
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
                    self.unproven_prefix = loop_unproven;
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
                        HirLValue::Temp(_) => true,
                        HirLValue::Local(local) => self.declared.contains(local),
                        _ => true,
                    }) =>
                {
                    // 全函数 use/write scope 分析包含请求窗口之后的读取；只有不跨块
                    // 的 Temp 才能把未知声明效果限制在当前词法作用域。
                    // 环境读取已拥有这个确切的字符串 key；它不会再产生独立源码声明。
                    // 仍被显式读取或带 debug 身份的 Temp 不借用该许可。
                    let represented_key =
                        stmt.scalar_temp_assignment().is_some_and(|(temp, value)| {
                            matches!(value, crate::hir::common::HirExpr::String(key)
                            if self.global_keys.get(&temp) == Some(key))
                        });
                    self.unproven_prefix |= !represented_key
                        && assign
                            .targets
                            .iter()
                            .any(|target| matches!(target, HirLValue::Temp(_)));
                }
                HirStmt::TableSetList(_) => {
                    // 残余批次尚未获得完整源码帧；它的临时声明影响当前块后缀，
                    // 不影响兄弟作用域。不能把尚待恢复的 SETLIST 当成跨块未知身份。
                    self.unproven_prefix = true;
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
