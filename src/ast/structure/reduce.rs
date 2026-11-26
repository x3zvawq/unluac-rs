//! 通用分层控制流结构化引擎（Phase 1 迭代区域规约 + Phase 2 按方言能力完备降级）。
//!
//! 优先级顺序：
//! 1. 显式 VM `for` 循环（`NumericFor` / `GenericFor`）
//! 2. 不可规约多入口 SCC（目标支持 `goto` 时最小化 label/goto；无 `goto` 时局部 `StateMachine`）
//! 3. 自然循环（`while cond` / `repeat ... until` / `while true`）
//! 4. 短路条件折叠 + 布尔物化赋值（`BoolAssign`）
//! 5. 分支与顺序规约（`if/else`、Soft Merge、早退 Guard、受控小尾块复制、单遍 `repeat ... until true`）
//! 6. 残余不可直接吸收的跳跃边按 `ControlFlowCaps` 完备降级（绝不向 Lua 5.1 输出非法 `goto`）。

use std::collections::{BTreeMap, BTreeSet};

use crate::analysis::{BlockId, Cfg, EdgeKind, LoopProtocolHint, NaturalLoop, ProtoAnalysis};
use crate::decompile::ControlFlowCaps;
use crate::transformer::{AccessBase, CloseKind, InstrRef, LowInstr, LoweredProto, Reg};

use super::cond_fold::{FoldedCondition, fold_condition};
use super::region::{CondExpr, Region, StateArm, StateTransition};

/// 当前活跃 `<close>` 显式作用域上下文（Lua 5.4/5.5 `TBC` + `CLOSE` 边界）。
#[derive(Debug, Clone)]
struct ActiveTbcScope {
    /// 该作用域的自然落出目标（离开 `DoScope` 后紧接着执行的块）；
    /// 若该块在 `mid_block_closes` 中，则先在作用域内发射其关闭前切片，再落出并在作用域外继续余部。
    fallthrough_exit: Option<BlockId>,
    /// 该作用域中所有“块首即关闭 `reg`”的外部退出块，记录其关闭指令后的续跑指令位置。
    leading_close_exits: BTreeMap<BlockId, InstrRef>,
    /// 该作用域中所有“块中段关闭 `reg`”的退出块，记录 `(close_iref, post_dest)`：
    /// `post_dest == Some(block)` 表示关闭后本块仍有后继语句在作用域外执行；
    /// `post_dest == Some(succ)` 表示关闭后直接跳转至外部后继块 `succ`。
    mid_block_closes: BTreeMap<BlockId, (InstrRef, Option<BlockId>)>,
    /// 对每个非落出（或被 `goto` 命中的）外部退出块延迟分配的作用域专属局部标签。
    exit_labels: BTreeMap<BlockId, usize>,
}

/// 当前活跃循环上下文。
#[derive(Debug, Clone)]
struct ActiveLoop {
    /// 对应的自然循环 ID（显式 `NumericFor`/`GenericFor` 为 `None`）。
    loop_id: Option<usize>,
    header: BlockId,
    /// 循环继续目标（对 while/generic-for 是 header，对 numeric-for/repeat 可为 latch）。
    continue_target: BlockId,
    /// 循环主退出目标（到达此块即触发 `break`）。
    exit: Option<BlockId>,
    /// 该循环的显式 `NumericForLoop` 尾块集合（到达时发射其前缀即自然完成本轮迭代）。
    numeric_latches: BTreeSet<BlockId>,
    /// 若循环体内向 `continue_target` 发出了 `goto`（Lua 5.2+/LuaJIT），延迟分配的循环尾标签。
    continue_label: Option<usize>,
    /// 若内层循环向本外层循环的 `exit` 发出了跨层 `goto`，延迟分配的循环后标签。
    exit_label: Option<usize>,
    /// 是否为单遍 `repeat ... until true` 早退围栏。
    is_fence: bool,
}

/// 单入口化的不可规约超区域（以全部多入口的最近公共支配块 `entry` 为唯一入口）。
#[derive(Debug, Clone)]
struct IrreducibleSuperRegion {
    entry: BlockId,
    blocks: BTreeSet<BlockId>,
}

/// 结构化执行上下文。
struct Structurer<'a> {
    proto: &'a LoweredProto,
    analysis: &'a ProtoAnalysis,
    caps: ControlFlowCaps,
    numeric_for_by_init: BTreeMap<BlockId, usize>,
    generic_for_by_entry: BTreeMap<BlockId, usize>,
    irreducible_regions: Vec<IrreducibleSuperRegion>,
    loop_stack: Vec<ActiveLoop>,
    /// 活跃 `<close>` 作用域栈，用于将跨分支/循环/早退的显式 `CLOSE` 还原为精确的 `do ... end` + `goto` 边界。
    tbc_stack: Vec<ActiveTbcScope>,
    /// 单个基本块的续跑起始指令（用于跳过外层 `DoScope` 已发射的前缀或已在作用域出口执行的块首 `CLOSE`）。
    block_start_instr: BTreeMap<BlockId, InstrRef>,
    /// 当前递归 `structure_slice` 调用链中正在展开的祖先块集合，杜绝嵌套不可规约环无限递归展开。
    active_slice_blocks: BTreeSet<BlockId>,
    label_ids: BTreeMap<BlockId, usize>,
    next_label: usize,
    emitted_labels: BTreeSet<BlockId>,
    /// 已识别的长早退阶梯（长度 >= 4）的所有步进头块集合，确保整条阶梯（含末尾 3 步）完整线性展开而不回退成指数复制。
    ladder_blocks: BTreeSet<BlockId>,
    /// 递归深度或长链超出安全预算，完成后须退回平级完备降级，绝不静默丢弃代码块。
    hit_depth_limit: bool,
}

/// 结构化入口：将单个 proto 的 CFG 完整规约为单根 `Region`。
pub fn structure_proto(
    proto: &LoweredProto,
    analysis: &ProtoAnalysis,
    caps: ControlFlowCaps,
) -> Region {
    let mut numeric_for_by_init = BTreeMap::new();
    let mut generic_for_by_entry = BTreeMap::new();

    for (idx, hint) in analysis.cfg.loop_protocols.iter().enumerate() {
        match hint {
            LoopProtocolHint::NumericFor { init_block, .. } => {
                numeric_for_by_init.insert(*init_block, idx);
            }
            LoopProtocolHint::GenericFor {
                prep_block,
                header_block,
                ..
            } => {
                if let Some(prep) = prep_block {
                    generic_for_by_entry.insert(*prep, idx);
                } else {
                    generic_for_by_entry.insert(*header_block, idx);
                }
            }
        }
    }

    let irreducible_regions = build_irreducible_super_regions(analysis);

    let mut structurer = Structurer {
        proto,
        analysis,
        caps,
        numeric_for_by_init,
        generic_for_by_entry,
        irreducible_regions,
        loop_stack: Vec::new(),
        tbc_stack: Vec::new(),
        block_start_instr: BTreeMap::new(),
        active_slice_blocks: BTreeSet::new(),
        label_ids: BTreeMap::new(),
        next_label: 0,
        emitted_labels: BTreeSet::new(),
        ladder_blocks: BTreeSet::new(),
        hit_depth_limit: false,
    };

    let cfg = &analysis.cfg;
    if cfg.blocks.is_empty() || cfg.entry_block == cfg.exit_block {
        return Region::Empty;
    }

    let region = structurer.structure_slice(cfg.entry_block, Some(cfg.exit_block), None, 0, false);

    // 完备守卫：校验最终 Region 是否触达深度上限以及全部 goto/label 的存在性、唯一性与块级可见性；
    // 若超限或残余极少数跨循环交叉跳转破坏了可见性，退回函数级单块平级降级（100% 保证合法且不丢代码）。
    if structurer.hit_depth_limit || !region_gotos_are_valid(&region) {
        return structurer.structure_flat_proto_fallback();
    }
    region
}

impl<'a> Structurer<'a> {
    fn cfg(&self) -> &'a Cfg {
        &self.analysis.cfg
    }

    fn alloc_fresh_label(&mut self) -> usize {
        let id = self.next_label;
        self.next_label += 1;
        id
    }

    fn label_for(&mut self, block: BlockId) -> usize {
        if let Some(&id) = self.label_ids.get(&block) {
            id
        } else {
            let id = self.alloc_fresh_label();
            self.label_ids.insert(block, id);
            id
        }
    }

    /// 获取或分配当前最内层循环专属的 continue 尾标签（避免与外部块标签冲突或缺失）。
    fn innermost_continue_label(&mut self) -> usize {
        if let Some(lbl) = self.loop_stack.last().and_then(|l| l.continue_label) {
            return lbl;
        }
        let lbl = self.alloc_fresh_label();
        if let Some(last) = self.loop_stack.last_mut() {
            last.continue_label = Some(lbl);
        }
        lbl
    }

    /// 获取或分配指定外层循环的 exit 出口标签。
    fn outer_exit_label(&mut self, stack_index: usize) -> usize {
        if let Some(lbl) = self.loop_stack[stack_index].exit_label {
            return lbl;
        }
        let lbl = self.alloc_fresh_label();
        self.loop_stack[stack_index].exit_label = Some(lbl);
        lbl
    }

    /// 获取或分配指定外层循环的 continue 尾标签。
    fn outer_continue_label(&mut self, stack_index: usize) -> usize {
        if let Some(lbl) = self.loop_stack[stack_index].continue_label {
            return lbl;
        }
        let lbl = self.alloc_fresh_label();
        self.loop_stack[stack_index].continue_label = Some(lbl);
        lbl
    }

    fn is_active_loop_header(&self, block: BlockId) -> bool {
        self.loop_stack.iter().any(|l| l.header == block)
    }

    fn is_active_natural_loop(&self, loop_id: usize) -> bool {
        self.loop_stack.iter().any(|l| l.loop_id == Some(loop_id))
    }

    /// 查找以 `header` 为入口、尚未入栈且被 `allowed` 完整包含的最外层自然循环。
    fn next_unentered_natural_loop(
        &self,
        header: BlockId,
        allowed: Option<&BTreeSet<BlockId>>,
    ) -> Option<&'a NaturalLoop> {
        self.analysis
            .graph
            .loops_by_header(header)
            .find(|nat_loop| {
                !self.is_active_natural_loop(nat_loop.id)
                    && allowed.is_none_or(|a| nat_loop.blocks.is_subset(a))
            })
    }

    /// 判断在 `header` 处是否存在尚未进入的自然循环，其块集严格包含了指定 `for` 协议的退出块
    /// （如 `repeat for i = 1, 2 do ... end until cond` 共享入口块）。
    fn has_enclosing_unentered_natural_loop_over_for(
        &self,
        proto_idx: usize,
        header: BlockId,
        allowed: Option<&BTreeSet<BlockId>>,
    ) -> bool {
        let for_exit = match &self.analysis.cfg.loop_protocols[proto_idx] {
            LoopProtocolHint::NumericFor { exit_block, .. }
            | LoopProtocolHint::GenericFor { exit_block, .. } => *exit_block,
        };
        self.analysis
            .graph
            .loops_by_header(header)
            .any(|nat_loop| {
                !self.is_active_natural_loop(nat_loop.id)
                    && allowed.is_none_or(|a| nat_loop.blocks.is_subset(a))
                    && nat_loop.blocks.contains(&for_exit)
            })
    }

    fn is_loop_boundary_block(&self, b: BlockId) -> bool {
        self.loop_stack.iter().any(|l| {
            l.exit == Some(b)
                || l.continue_target == b
                || l.header == b
                || l.numeric_latches.contains(&b)
        })
    }

    fn innermost_loop(&self) -> Option<&ActiveLoop> {
        self.loop_stack.last()
    }

    /// 核心递归切片结构化：从 `start` 执行到 `stop`（不含 `stop`）。
    ///
    /// `allow_header_once`: 当从循环头（如 `repeat` 循环体入口）首次进入切片时为 `true`，
    /// 允许执行首块本身，但在首块之后的任何回跳均不得再次展开该循环头。
    fn structure_slice(
        &mut self,
        start: BlockId,
        stop: Option<BlockId>,
        allowed: Option<&BTreeSet<BlockId>>,
        depth: usize,
        allow_header_once: bool,
    ) -> Region {
        if depth > 512 {
            self.hit_depth_limit = true;
            return Region::Empty;
        }
        let cfg = self.cfg();
        let mut items = Vec::new();
        let mut cur = start;
        let mut visited_in_slice = BTreeSet::new();
        let mut inserted_active = Vec::new();
        let mut is_first_step = allow_header_once;

        while Some(cur) != stop && cur != cfg.exit_block {
            let skip_header_guard = is_first_step;
            is_first_step = false;

            // 0. 检查是否命中活跃 `<close>` 显式作用域的关闭边界
            if let Some(transfer) = self.check_enclosing_tbc_boundary(cur, stop) {
                items.push(transfer);
                break;
            }

            // 1. 检查是否命中活跃循环的退出 / 回跳边界
            if let Some(transfer) = self.check_enclosing_loop_boundary(cur, stop, skip_header_guard)
            {
                items.push(transfer);
                break;
            }

            if let Some(allow) = allowed
                && !allow.contains(&cur)
            {
                let innermost_exit = self.innermost_loop().and_then(|l| l.exit);
                if innermost_exit == Some(cur) {
                    items.push(Region::Break);
                } else if self.can_inline_external_exit_pad(cur, innermost_exit) {
                    // 循环内的早退 return-pad 或 break-pad 块不在自然循环块集内，
                    // 但会无环终止于 Return/TailCall 或直接汇合到 loop_exit（触发 Break）：
                    // 直接在当前分支就地发射，绝不静默丢弃！
                    let pad = self.structure_slice(cur, None, None, depth + 1, false);
                    items.push(pad);
                } else if let Some(edge_region) = self.emit_out_of_region_jump(cur) {
                    items.push(edge_region);
                }
                break;
            }

            // 若到达当前最内层 NumericFor 的 latch 块（以 NumericForLoop 结尾）：
            // - 若 `stop.is_none()`（位于循环体自然末尾），发射其前缀即自然完成本轮迭代；
            // - 若 `stop.is_some()`（位于嵌套分支内部，后续仍有循环体尾代码），必须在前缀之后发射
            //   `continue`（Luau）或 `goto L_continue`（Lua 5.2+），绝不能穿透到分支后的尾语句！
            if let Some(innermost) = self.innermost_loop().cloned()
                && innermost.numeric_latches.contains(&cur)
            {
                if self.has_non_branch_prefix(cur) {
                    items.push(Region::BlockPrefix(cur));
                }
                if stop.is_some() && !innermost.is_fence {
                    if self.caps.continue_stmt {
                        items.push(Region::Continue);
                    } else if self.caps.goto_label {
                        let lbl = self.innermost_continue_label();
                        items.push(Region::Goto(lbl));
                    }
                }
                break;
            }

            // 防止异常图或未收敛环导致死循环/256 层指数展开
            // （当 `skip_header_guard == true` 时是外层 `repeat` 合法地以首步进入循环体，不算环）
            if !visited_in_slice.insert(cur) {
                if self.caps.goto_label {
                    let lbl = self.label_for(cur);
                    items.push(Region::Goto(lbl));
                }
                break;
            }
            if self.active_slice_blocks.insert(cur) {
                inserted_active.push(cur);
            } else if !skip_header_guard {
                if self.caps.goto_label {
                    let lbl = self.label_for(cur);
                    items.push(Region::Goto(lbl));
                }
                break;
            }

            // 若外部跳跃已为当前块分配过 label 且尚未发射，在此块入口挂接该 label
            if self.caps.goto_label
                && let Some(&lbl) = self.label_ids.get(&cur)
                && self.emitted_labels.insert(cur)
            {
                items.push(Region::Labeled(lbl, Box::new(Region::Empty)));
            }

            // 2. 显式 NumericFor（若当前块同时是更外层自然循环的头且外层循环包含该 for 的退出块，
            //    例如 `repeat for i = 1, 2 do ... end until cond`，必须先进入外层自然循环再在体内首步展开 for！）
            if let Some(&proto_idx) = self.numeric_for_by_init.get(&cur)
                && (!self.is_active_loop_header(cur) || skip_header_guard)
                && !self.has_enclosing_unentered_natural_loop_over_for(proto_idx, cur, allowed)
                && let Some((region, next)) = self.structure_numeric_for(proto_idx, depth)
            {
                items.push(region);
                cur = next;
                continue;
            }

            // 3. 显式 GenericFor（同理，外层自然循环包含本 for 退出块时先进入外层循环，体内首步允许展开）
            if let Some(&proto_idx) = self.generic_for_by_entry.get(&cur)
                && (!self.is_active_loop_header(cur) || skip_header_guard)
                && !self.has_enclosing_unentered_natural_loop_over_for(proto_idx, cur, allowed)
                && let Some((region, next)) = self.structure_generic_for(proto_idx, depth)
            {
                items.push(region);
                cur = next;
                continue;
            }

            // 4. 不可规约多入口 SCC（从该入口首次进入时整体接管）
            if let Some(scc_idx) = self.find_unentered_irreducible_scc(cur, allowed) {
                let (region, next_opt) = self.structure_irreducible_scc(scc_idx, cur, stop, depth);
                items.push(region);
                match next_opt {
                    Some(next) => {
                        cur = next;
                        continue;
                    }
                    None => break,
                }
            }

            // 5. 自然循环（while / repeat / while true；支持共享入口的严格嵌套循环逐层展开）
            if let Some(nat_loop) = self.next_unentered_natural_loop(cur, allowed) {
                let (region, next_opt) = self.structure_natural_loop(nat_loop, depth);
                items.push(region);
                match next_opt {
                    Some(next) => {
                        cur = next;
                        continue;
                    }
                    None => break,
                }
            }

            // 5.5. Lua 5.4/5.5 显式 `<close>` 词法作用域边界结构化（跨分支/循环早退精确包裹 `do ... end`）
            if self.caps.goto_label
                && let Some((region, next_opt)) =
                    self.try_structure_tbc_scope(cur, stop, allowed, depth)
            {
                items.push(region);
                match next_opt {
                    Some(next) => {
                        cur = next;
                        continue;
                    }
                    None => break,
                }
            }

            // 6. 条件分支（短路折叠 → 布尔物化 / If-Else / Guard / Soft Merge）
            // 传入 `fold_condition` 的允许集合必须排除 `stop`，避免短路折叠跨越边界（例如跨过 repeat latch 回跳 header）。
            let fold_allowed_buf: Option<BTreeSet<BlockId>> = if let Some(s) = stop {
                if let Some(allow) = allowed {
                    if allow.contains(&s) {
                        let mut trimmed = allow.clone();
                        trimmed.remove(&s);
                        Some(trimmed)
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            };
            let fold_allowed = fold_allowed_buf.as_ref().or(allowed);
            if cfg.branch_edges(cur).is_some()
                && let Some(folded) = fold_condition(self.proto, self.analysis, cur, fold_allowed)
            {
                // 6a) 布尔物化菱形：`cond ? LoadBool(dst, b1) : LoadBool(dst, b2) -> J`
                // 仅当首块含非条件语句时才单独发射 BlockPrefix；纯条件块的前缀会在 lift_cond_expr 中求值一次，
                // 避免像 `object.enabled and object.read(1) == 5` 那样重复求值两次！
                if let Some((bool_region, join)) = self.try_fold_bool_materialize(cur, &folded) {
                    if let Some(pref) = self.block_prefix_region(cur) {
                        items.push(pref);
                    }
                    items.push(bool_region);
                    cur = join;
                    continue;
                }

                // 6b) 常规条件分支
                let (branch_region, next_opt) =
                    self.structure_branch(cur, folded, stop, allowed, depth);
                items.push(branch_region);
                match next_opt {
                    Some(next) => {
                        cur = next;
                        continue;
                    }
                    None => break,
                }
            }

            // 7. 普通线性基本块（Jump / Fallthrough / Return / TailCall / ForLoop 边界）
            items.push(self.block_full_region(cur));
            match cfg.succs[cur.index()].as_slice() {
                [edge_id] => {
                    let edge = cfg.edges[edge_id.index()];
                    match edge.kind {
                        EdgeKind::Return | EdgeKind::TailCall => break,
                        _ => cur = edge.to,
                    }
                }
                _ => break,
            }
        }

        for b in inserted_active {
            self.active_slice_blocks.remove(&b);
        }
        Region::sequence(items)
    }

    fn has_non_branch_prefix(&self, block: BlockId) -> bool {
        self.cfg().blocks[block.index()].instrs.len > 1
    }

    fn block_prefix_region(&self, block: BlockId) -> Option<Region> {
        let range = self.cfg().blocks[block.index()].instrs;
        if range.len <= 1 || !self.block_has_non_cond_stmts(block) {
            return None;
        }
        let last = InstrRef(range.end() - 1);
        if let Some(&start) = self.block_start_instr.get(&block) {
            (start.index() < last.index()).then_some(Region::BlockSlice {
                block,
                start_instr: start,
                end_instr: last,
            })
        } else {
            Some(Region::BlockPrefix(block))
        }
    }

    fn block_full_region(&self, block: BlockId) -> Region {
        if let Some(&start) = self.block_start_instr.get(&block) {
            let end = InstrRef(self.cfg().blocks[block.index()].instrs.end());
            if start.index() < end.index() {
                Region::BlockSlice {
                    block,
                    start_instr: start,
                    end_instr: end,
                }
            } else {
                Region::Empty
            }
        } else {
            Region::Block(block)
        }
    }

    /// 检查基本块 `block` 是否声明了 `<close>` 资源且在所有出边目标块首均立即关闭该资源（如不可规约 SCC 中的独立 `do local g <close> ... end`）。
    fn block_tbc_closes_on_all_exits(&self, block: BlockId) -> bool {
        let cfg = self.cfg();
        let range = cfg.blocks[block.index()].instrs;
        let mut min_open_tbc: Option<usize> = None;
        for iref in range.iter() {
            match &self.proto.instrs[iref.index()] {
                LowInstr::Tbc(t) => {
                    let r = t.reg.index();
                    min_open_tbc = Some(min_open_tbc.map_or(r, |m| m.min(r)));
                }
                LowInstr::Close(c) if c.kind == CloseKind::Explicit => {
                    if let Some(m) = min_open_tbc
                        && c.from.index() <= m
                    {
                        min_open_tbc = None;
                    }
                }
                _ => {}
            }
        }
        let Some(tbc_reg) = min_open_tbc else {
            return false;
        };
        let succs = &cfg.succs[block.index()];
        if succs.is_empty() {
            return false;
        }
        succs.iter().all(|&eid| {
            let edge = cfg.edges[eid.index()];
            matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                || edge.to == cfg.exit_block
                || self.block_leading_close_after(edge.to, Reg(tbc_reg)).is_some()
        })
    }

    /// 若 `block` 从首指令起以 `Close(Explicit { from <= reg })` 关闭 `reg`，返回跳过连续前导关闭指令后的续跑 `InstrRef`。
    fn block_leading_close_after(&self, block: BlockId, reg: Reg) -> Option<InstrRef> {
        let range = self.cfg().blocks[block.index()].instrs;
        let first = range.iter().next()?;
        let closes_reg = matches!(
            &self.proto.instrs[first.index()],
            LowInstr::Close(c) if c.kind == CloseKind::Explicit && c.from.index() <= reg.index()
        );
        if !closes_reg {
            return None;
        }
        // 只跳过与本次关闭匹配的块首单条关闭指令（保留更外层或后续逻辑）
        Some(InstrRef(first.index() + 1))
    }

    /// 若 `block` 是纯“关闭 + 单边跳转”pad（不含任何其它可执行语句），返回其跳转目标块。
    fn pure_close_jump_target(&self, block: BlockId, after_close: InstrRef) -> Option<BlockId> {
        let cfg = self.cfg();
        let range = cfg.blocks[block.index()].instrs;
        for instr in self
            .proto
            .instrs
            .get(after_close.index()..range.end())
            .unwrap_or(&[])
        {
            match instr {
                LowInstr::Jump(_) => {}
                LowInstr::Close(c) if c.kind == CloseKind::Explicit => {}
                _ => return None,
            }
        }
        if let [eid] = cfg.succs[block.index()].as_slice() {
            let edge = cfg.edges[eid.index()];
            if !matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                && edge.to != cfg.exit_block
            {
                return Some(edge.to);
            }
        }
        None
    }

    fn is_tbc_fallthrough_exit(&self, block: BlockId) -> bool {
        let Some(top) = self.tbc_stack.last() else {
            return false;
        };
        if top.fallthrough_exit == Some(block) && !top.mid_block_closes.contains_key(&block) {
            return true;
        }
        top.mid_block_closes
            .get(&block)
            .is_some_and(|&(_, post_dest)| post_dest == top.fallthrough_exit)
    }

    fn is_tbc_early_exit(&self, block: BlockId) -> bool {
        let top_idx = self.tbc_stack.len().saturating_sub(1);
        for (si, scope) in self.tbc_stack.iter().enumerate().rev() {
            if scope.leading_close_exits.contains_key(&block) {
                return si != top_idx || scope.fallthrough_exit != Some(block);
            }
            if let Some(&(_, post_dest_opt)) = scope.mid_block_closes.get(&block) {
                return si != top_idx || post_dest_opt != scope.fallthrough_exit;
            }
        }
        false
    }

    /// 检查从 `<close>` 作用域内部跳出至 `target` 时是否命中外层循环的 `break`/`continue` 边界
    /// （包括仅含前导 `Close` + `NumericForLoop` 的纯数值 for latch 块）。
    fn try_loop_transfer_for_tbc_exit(
        &mut self,
        target: BlockId,
        after_close: Option<InstrRef>,
        stop: Option<BlockId>,
    ) -> Option<Region> {
        if let Some(loop_transfer) = self.check_enclosing_loop_boundary(target, stop, false) {
            return Some(loop_transfer);
        }
        if let Some(innermost) = self.innermost_loop().cloned()
            && innermost.numeric_latches.contains(&target)
            && !innermost.is_fence
        {
            let range = self.cfg().blocks[target.index()].instrs;
            let start = after_close.unwrap_or(range.start);
            let only_close_and_loop = (start.index()..range.end()).all(|idx| {
                matches!(
                    &self.proto.instrs[idx],
                    LowInstr::Close(c) if c.kind == CloseKind::Explicit
                ) || matches!(&self.proto.instrs[idx], LowInstr::NumericForLoop(_))
            });
            if only_close_and_loop {
                if self.caps.continue_stmt {
                    return Some(Region::Continue);
                }
                if self.caps.goto_label {
                    let lbl = self.innermost_continue_label();
                    return Some(Region::Goto(lbl));
                }
            }
        }
        None
    }

    fn check_enclosing_tbc_boundary(&mut self, cur: BlockId, stop: Option<BlockId>) -> Option<Region> {
        if self.tbc_stack.is_empty() {
            return None;
        }
        let cfg = self.cfg();
        let top_idx = self.tbc_stack.len() - 1;
        for si in (0..self.tbc_stack.len()).rev() {
            // 1. 块中段关闭：`cur` 先在作用域内执行关闭前切片，再跳出作用域
            if let Some(&(close_iref, post_dest_opt)) = self.tbc_stack[si].mid_block_closes.get(&cur)
            {
                let start = self
                    .block_start_instr
                    .get(&cur)
                    .copied()
                    .unwrap_or(cfg.blocks[cur.index()].instrs.start);
                let mut parts = Vec::new();
                if start.index() < close_iref.index() {
                    parts.push(Region::BlockSlice {
                        block: cur,
                        start_instr: start,
                        end_instr: close_iref,
                    });
                }
                if si == top_idx && post_dest_opt == self.tbc_stack[si].fallthrough_exit {
                    return Some(Region::sequence(parts));
                }
                if let Some(dest) = post_dest_opt {
                    if let Some(loop_transfer) =
                        self.try_loop_transfer_for_tbc_exit(dest, None, stop)
                    {
                        parts.push(loop_transfer);
                        return Some(Region::sequence(parts));
                    }
                    // 检查是否命中外层某个 `<close>` 作用域的退出块
                    let target_si = (0..=si)
                        .find(|&oi| {
                            self.tbc_stack[oi].fallthrough_exit == Some(dest)
                                || self.tbc_stack[oi].leading_close_exits.contains_key(&dest)
                        })
                        .unwrap_or(si);
                    let lbl = self.tbc_exit_label(target_si, dest);
                    parts.push(Region::Goto(lbl));
                    return Some(Region::sequence(parts));
                }
                // 关闭后直接 Return/TailCall：把 Return 留在作用域内即可（Lua `return` 自动关闭 `<close>`）
                let end = InstrRef(cfg.blocks[cur.index()].instrs.end());
                if close_iref.index() + 1 < end.index() {
                    parts.push(Region::BlockSlice {
                        block: cur,
                        start_instr: InstrRef(close_iref.index() + 1),
                        end_instr: end,
                    });
                }
                return Some(Region::sequence(parts));
            }

            // 2. 块首关闭：`cur` 整体在作用域之外
            if let Some(&after_close) = self.tbc_stack[si].leading_close_exits.get(&cur) {
                if let Some(loop_transfer) =
                    self.try_loop_transfer_for_tbc_exit(cur, Some(after_close), stop)
                {
                    return Some(loop_transfer);
                }
                if let Some(jump_target) = self.pure_close_jump_target(cur, after_close)
                    && let Some(loop_transfer) =
                        self.try_loop_transfer_for_tbc_exit(jump_target, None, stop)
                {
                    return Some(loop_transfer);
                }
                if si == top_idx && self.tbc_stack[si].fallthrough_exit == Some(cur) {
                    return Some(Region::Empty);
                }
                // 若该退出块同时也是更外层 `<close>` 作用域的退出块（如 `island_08` 的 `B5`），
                // 将标签挂在最外层对应作用域出口处，一次 `goto` 穿透多层 `do ... end` 按 LIFO 自动关闭！
                let target_si = (0..=si)
                    .find(|&oi| {
                        self.tbc_stack[oi].fallthrough_exit == Some(cur)
                            || self.tbc_stack[oi].leading_close_exits.contains_key(&cur)
                    })
                    .unwrap_or(si);
                let lbl = self.tbc_exit_label(target_si, cur);
                return Some(Region::Goto(lbl));
            }
        }
        None
    }

    fn tbc_exit_label(&mut self, stack_idx: usize, block: BlockId) -> usize {
        if let Some(&lbl) = self.tbc_stack[stack_idx].exit_labels.get(&block) {
            return lbl;
        }
        let lbl = self.alloc_fresh_label();
        self.tbc_stack[stack_idx].exit_labels.insert(block, lbl);
        lbl
    }

    /// 识别并结构化以 `cur` 内 `LowInstr::Tbc(reg)` 为起点的显式 `<close>` 作用域。
    ///
    /// 仅当该 `<close>` 跨出 `cur` 且在 `stop` 之前存在需要在关闭后继续执行的块/切片时才包裹 `Region::DoScope`，
    /// 对单块内闭合或直达函数末尾返回的普通 `<close>` 保持零开销直通。
    fn try_structure_tbc_scope(
        &mut self,
        cur: BlockId,
        stop: Option<BlockId>,
        allowed: Option<&BTreeSet<BlockId>>,
        depth: usize,
    ) -> Option<(Region, Option<BlockId>)> {
        let cfg = self.cfg();
        let range = cfg.blocks[cur.index()].instrs;
        let cur_start = self
            .block_start_instr
            .get(&cur)
            .copied()
            .unwrap_or(range.start);
        if cur_start.index() >= range.end() {
            return None;
        }

        // 查找从 `cur_start` 起尚未在 `cur` 本身内闭合的候选 `Tbc` 指令列表
        let mut tbc_candidates: Vec<(InstrRef, Reg)> = Vec::new();
        for idx in cur_start.index()..range.end() {
            if let LowInstr::Tbc(t) = &self.proto.instrs[idx] {
                let closed_in_cur = ((idx + 1)..range.end()).any(|j| {
                    matches!(
                        &self.proto.instrs[j],
                        LowInstr::Close(c)
                            if c.kind == CloseKind::Explicit && c.from.index() <= t.reg.index()
                    )
                });
                if !closed_in_cur {
                    tbc_candidates.push((InstrRef(idx), t.reg));
                }
            }
        }
        if tbc_candidates.is_empty() {
            return None;
        }

        let innermost_exit = self.innermost_loop().and_then(|l| l.exit);
        let is_outer_tbc_exit = |b: BlockId| -> bool {
            self.tbc_stack.iter().any(|s| {
                s.leading_close_exits.contains_key(&b)
                    || (s.fallthrough_exit == Some(b) && !s.mid_block_closes.contains_key(&b))
            })
        };

        struct TbcScopeCandidate {
            ci: usize,
            tbc_iref: InstrRef,
            reg: Reg,
            scope_blocks: BTreeSet<BlockId>,
            leading_close_exits: BTreeMap<BlockId, InstrRef>,
            mid_block_closes: BTreeMap<BlockId, (InstrRef, Option<BlockId>)>,
            fallthrough_exit: Option<BlockId>,
        }

        // 从最外层候选 `Tbc` 开始，找到第一个确实需要显式 `DoScope` 的 `<close>` 作用域
        let mut chosen: Option<TbcScopeCandidate> = None;
        for (ci, &(tbc_iref, reg)) in tbc_candidates.iter().enumerate() {
            let mut leading_close_exits: BTreeMap<BlockId, InstrRef> = BTreeMap::new();
            let mut mid_block_closes: BTreeMap<BlockId, (InstrRef, Option<BlockId>)> =
                BTreeMap::new();
            let mut scope_blocks: BTreeSet<BlockId> = BTreeSet::new();
            let mut visited: BTreeSet<BlockId> = BTreeSet::new();
            let mut queue: Vec<BlockId> = Vec::new();
            visited.insert(cur);
            scope_blocks.insert(cur);

            for &eid in &cfg.succs[cur.index()] {
                let edge = cfg.edges[eid.index()];
                if !matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                    && edge.to != cfg.exit_block
                    && visited.insert(edge.to)
                {
                    queue.push(edge.to);
                }
            }

            let mut qi = 0;
            while qi < queue.len() {
                let b = queue[qi];
                qi += 1;
                if Some(b) == stop || b == cfg.exit_block {
                    continue;
                }
                // 先检测块首关闭或块中段关闭
                if let Some(after_close) = self.block_leading_close_after(b, reg) {
                    leading_close_exits.insert(b, after_close);
                    continue;
                }
                let brange = cfg.blocks[b.index()].instrs;
                let mid_close = brange.iter().find(|&ir| {
                    matches!(
                        &self.proto.instrs[ir.index()],
                        LowInstr::Close(c)
                            if c.kind == CloseKind::Explicit && c.from.index() <= reg.index()
                    )
                });
                if let Some(c_iref) = mid_close {
                    scope_blocks.insert(b);
                    // 判断关闭指令后本块是否仍有非 Jump/Close/Return/Loop 的续跑语句
                    let has_post_stmts = ((c_iref.index() + 1)..brange.end()).any(|j| {
                        !matches!(
                            &self.proto.instrs[j],
                            LowInstr::Jump(_)
                                | LowInstr::Return(_)
                                | LowInstr::TailCall(_)
                                | LowInstr::Close(_)
                                | LowInstr::NumericForLoop(_)
                                | LowInstr::GenericForCall(_)
                                | LowInstr::GenericForLoop(_)
                        )
                    });
                    let post_dest = if has_post_stmts {
                        Some(b)
                    } else if let [eid] = cfg.succs[b.index()].as_slice() {
                        let edge = cfg.edges[eid.index()];
                        if matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                            || edge.to == cfg.exit_block
                        {
                            None
                        } else {
                            Some(edge.to)
                        }
                    } else {
                        None
                    };
                    mid_block_closes.insert(b, (c_iref, post_dest));
                    continue;
                }

                // 若该块已越出当前 allowed 且不是可内联的退出 pad，则停止继续扩展
                if let Some(allow) = allowed
                    && !allow.contains(&b)
                    && !self.can_inline_external_exit_pad(b, innermost_exit)
                {
                    continue;
                }
                if self.is_loop_boundary_block(b) {
                    continue;
                }
                scope_blocks.insert(b);
                for &eid in &cfg.succs[b.index()] {
                    let edge = cfg.edges[eid.index()];
                    if !matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                        && edge.to != cfg.exit_block
                        && visited.insert(edge.to)
                    {
                        queue.push(edge.to);
                    }
                }
            }

            // 收集所有真正需要留在作用域之后执行的内部续跑点
            let mut interior_continuations: Vec<BlockId> = Vec::new();
            for (&b, &(_, post_dest_opt)) in &mid_block_closes {
                if let Some(dest) = post_dest_opt
                    && dest == b
                {
                    interior_continuations.push(b);
                } else if let Some(dest) = post_dest_opt
                    && Some(dest) != stop
                    && dest != cfg.exit_block
                    && !self.is_loop_boundary_block(dest)
                    && !is_outer_tbc_exit(dest)
                    && !interior_continuations.contains(&dest)
                {
                    interior_continuations.push(dest);
                }
            }
            for (&b, &after_close) in &leading_close_exits {
                let is_pure_loop_jump = self
                    .pure_close_jump_target(b, after_close)
                    .is_some_and(|t| self.is_loop_boundary_block(t) || Some(t) == stop);
                if !is_pure_loop_jump
                    && Some(b) != stop
                    && b != cfg.exit_block
                    && !self.is_loop_boundary_block(b)
                    && !is_outer_tbc_exit(b)
                    && !interior_continuations.contains(&b)
                {
                    interior_continuations.push(b);
                }
            }

            if interior_continuations.is_empty() {
                continue;
            }

            // 挑选最自然的落出目标：
            // 1) 优先选块中段关闭后同块续跑的目标（如 `close_17` `B6` 的 `after-inner`）；
            // 2) 其次选被某中段关闭直达的后继（如 `close_17` 外层的 `B7` 或 `island_08` 外层的 `B5`）；
            // 3) 否则取首个内部续跑点（如 `island_08` 内层的 `B2`、`loop_33` 的 `B_after`、`close_19` 的 `B3`）。
            let fallthrough_exit = interior_continuations
                .iter()
                .copied()
                .find(|&b| mid_block_closes.get(&b).is_some_and(|&(_, d)| d == Some(b)))
                .or_else(|| {
                    interior_continuations.iter().copied().find(|&b| {
                        mid_block_closes
                            .values()
                            .any(|&(_, d)| d == Some(b))
                    })
                })
                .or_else(|| interior_continuations.first().copied());

            chosen = Some(TbcScopeCandidate {
                ci,
                tbc_iref,
                reg,
                scope_blocks,
                leading_close_exits,
                mid_block_closes,
                fallthrough_exit,
            });
            break;
        }

        let TbcScopeCandidate {
            ci,
            tbc_iref,
            reg,
            scope_blocks,
            leading_close_exits,
            mid_block_closes,
            fallthrough_exit,
        } = chosen?;

        // 计算 `tbc_iref` 的初始化起点：若之前有其它 `Tbc`（未包 DoScope），紧跟在其后；
        // 否则沿块内逆向 def-use 切片回溯 `reg`（含多返回声明如 `local plain, res <close> = f()` 及表构造参数），
        // 确保不吞并前序无关语句，也不把 `reg` 的初值定义留在 `DoScope` 之外。
        let scope_start = if ci > 0 {
            InstrRef(tbc_candidates[ci - 1].0.index() + 1)
        } else {
            let mut s = tbc_iref.index();
            let mut min_reg = reg.index();
            let mut needed: BTreeSet<usize> = BTreeSet::new();
            needed.insert(reg.index());
            while s > cur_start.index() && !needed.is_empty() {
                let prev = s - 1;
                let prev_instr = &self.proto.instrs[prev];
                match prev_instr {
                    LowInstr::Tbc(_)
                    | LowInstr::Close(_)
                    | LowInstr::Jump(_)
                    | LowInstr::Branch(_)
                    | LowInstr::Return(_)
                    | LowInstr::TailCall(_)
                    | LowInstr::NumericForInit(_)
                    | LowInstr::NumericForLoop(_)
                    | LowInstr::GenericForPrep(_)
                    | LowInstr::GenericForCall(_)
                    | LowInstr::GenericForLoop(_)
                    | LowInstr::SetUpvalue(_) => break,
                    LowInstr::SetTable(st) => {
                        let AccessBase::Reg(tbl_reg) = st.base else {
                            break;
                        };
                        if !needed.contains(&tbl_reg.index()) {
                            break;
                        }
                        for &(ur, _) in &self.analysis.ssa.instr_uses[prev] {
                            if ur.index() >= min_reg {
                                needed.insert(ur.index());
                            }
                        }
                    }
                    LowInstr::SetList(sl) => {
                        if !needed.contains(&sl.base.index()) {
                            break;
                        }
                        for &(ur, _) in &self.analysis.ssa.instr_uses[prev] {
                            if ur.index() >= min_reg {
                                needed.insert(ur.index());
                            }
                        }
                    }
                    _ => {
                        let defs = &self.analysis.ssa.instr_defs[prev];
                        if !defs.iter().any(|(r, _)| needed.contains(&r.index())) {
                            break;
                        }
                        if defs.iter().any(|(r, _)| r.index() == reg.index()) {
                            for (r, _) in defs {
                                min_reg = min_reg.min(r.index());
                            }
                            if let LowInstr::Call(call) = prev_instr {
                                min_reg = min_reg.min(call.callee.index());
                            }
                        } else if defs.iter().any(|(r, _)| r.index() < min_reg) {
                            break;
                        }
                        for (r, _) in defs {
                            needed.remove(&r.index());
                        }
                        for &(ur, _) in &self.analysis.ssa.instr_uses[prev] {
                            if ur.index() >= min_reg {
                                needed.insert(ur.index());
                            }
                        }
                    }
                }
                s = prev;
            }
            InstrRef(s)
        };

        let mut outer_items = Vec::new();
        if scope_start.index() > cur_start.index() {
            outer_items.push(Region::BlockSlice {
                block: cur,
                start_instr: cur_start,
                end_instr: scope_start,
            });
        }

        let has_more_tbc_in_cur = ci + 1 < tbc_candidates.len();
        let inner_stop = fallthrough_exit.filter(|fb| !mid_block_closes.contains_key(fb));

        self.tbc_stack.push(ActiveTbcScope {
            fallthrough_exit,
            leading_close_exits,
            mid_block_closes,
            exit_labels: BTreeMap::new(),
        });

        let saved_cur_start = self.block_start_instr.get(&cur).copied();
        let scope_body = if has_more_tbc_in_cur {
            let mut inner_parts = vec![Region::BlockSlice {
                block: cur,
                start_instr: scope_start,
                end_instr: InstrRef(tbc_iref.index() + 1),
            }];
            self.block_start_instr
                .insert(cur, InstrRef(tbc_iref.index() + 1));
            let rest =
                self.structure_slice(cur, inner_stop, Some(&scope_blocks), depth + 1, true);
            inner_parts.push(rest);
            Region::sequence(inner_parts)
        } else {
            self.block_start_instr.insert(cur, scope_start);
            if cfg.branch_edges(cur).is_some()
                && let Some(folded) =
                    fold_condition(self.proto, self.analysis, cur, Some(&scope_blocks))
            {
                if let Some((bool_region, join)) = self.try_fold_bool_materialize(cur, &folded) {
                    let mut inner_parts = Vec::new();
                    if let Some(prefix) = self.block_prefix_region(cur) {
                        inner_parts.push(prefix);
                    }
                    inner_parts.push(bool_region);
                    if Some(join) != inner_stop && join != cfg.exit_block {
                        inner_parts.push(self.structure_slice(
                            join,
                            inner_stop,
                            Some(&scope_blocks),
                            depth + 1,
                            false,
                        ));
                    }
                    Region::sequence(inner_parts)
                } else {
                    let (br_region, br_next) =
                        self.structure_branch(cur, folded, inner_stop, Some(&scope_blocks), depth + 1);
                    let mut inner_parts = vec![br_region];
                    if let Some(next) = br_next {
                        inner_parts.push(self.structure_slice(
                            next,
                            inner_stop,
                            Some(&scope_blocks),
                            depth + 1,
                            false,
                        ));
                    }
                    Region::sequence(inner_parts)
                }
            } else {
                let mut inner_parts = vec![self.block_full_region(cur)];
                if let [eid] = cfg.succs[cur.index()].as_slice() {
                    let edge = cfg.edges[eid.index()];
                    if !matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                        && edge.to != cfg.exit_block
                    {
                        inner_parts.push(self.structure_slice(
                            edge.to,
                            inner_stop,
                            Some(&scope_blocks),
                            depth + 1,
                            false,
                        ));
                    }
                }
                Region::sequence(inner_parts)
            }
        };
        if let Some(prev) = saved_cur_start {
            self.block_start_instr.insert(cur, prev);
        } else {
            self.block_start_instr.remove(&cur);
        }

        let popped = self.tbc_stack.pop().unwrap();
        outer_items.push(Region::DoScope(Box::new(scope_body)));

        // 按序收集需要在 `DoScope` 之后立刻发射的续跑块（先落出目标，再其余被 goto 命中的兄弟出口）
        let mut post_blocks: Vec<BlockId> = Vec::new();
        if let Some(fb) = popped.fallthrough_exit
            && Some(fb) != stop
            && fb != cfg.exit_block
            && !self.is_loop_boundary_block(fb)
        {
            post_blocks.push(fb);
        }
        for &eb in popped.exit_labels.keys() {
            if Some(eb) != stop
                && eb != cfg.exit_block
                && !self.is_loop_boundary_block(eb)
                && !post_blocks.contains(&eb)
            {
                post_blocks.push(eb);
            }
        }

        if post_blocks.len() == 1 {
            let fb = post_blocks[0];
            if let Some(&lbl) = popped.exit_labels.get(&fb) {
                outer_items.push(Region::Labeled(lbl, Box::new(Region::Empty)));
            }
            let resume_iref = popped
                .leading_close_exits
                .get(&fb)
                .copied()
                .or_else(|| {
                    popped
                        .mid_block_closes
                        .get(&fb)
                        .filter(|&&(_, d)| d == Some(fb))
                        .map(|&(c_iref, _)| InstrRef(c_iref.index() + 1))
                });
            let saved_fb = self.block_start_instr.get(&fb).copied();
            if let Some(ri) = resume_iref {
                self.block_start_instr.insert(fb, ri);
            }
            // 若落出块位于外层循环 `allowed` 之外（如 `close_19` 的 `B3` 退出 pad），以 `allowed = None` 展开到 Return
            let post_allowed = if allowed.is_some_and(|a| !a.contains(&fb)) {
                None
            } else {
                allowed
            };
            let post_stop = if post_allowed.is_none() { None } else { stop };
            let tail = self.structure_slice(fb, post_stop, post_allowed, depth + 1, false);
            if let Some(prev) = saved_fb {
                self.block_start_instr.insert(fb, prev);
            } else {
                self.block_start_instr.remove(&fb);
            }
            outer_items.push(tail);
            return Some((Region::sequence(outer_items), None));
        }

        if post_blocks.len() > 1 {
            let after_all_lbl = self.alloc_fresh_label();
            let mut used_after = false;
            for (idx, &eb) in post_blocks.iter().enumerate() {
                if let Some(&lbl) = popped.exit_labels.get(&eb) {
                    outer_items.push(Region::Labeled(lbl, Box::new(Region::Empty)));
                }
                let resume_iref = popped
                    .leading_close_exits
                    .get(&eb)
                    .copied()
                    .or_else(|| {
                        popped
                            .mid_block_closes
                            .get(&eb)
                            .filter(|&&(_, d)| d == Some(eb))
                            .map(|&(c_iref, _)| InstrRef(c_iref.index() + 1))
                    });
                let saved_eb = self.block_start_instr.get(&eb).copied();
                if let Some(ri) = resume_iref {
                    self.block_start_instr.insert(eb, ri);
                }
                let post_allowed = if allowed.is_some_and(|a| !a.contains(&eb)) {
                    None
                } else {
                    allowed
                };
                let tail = self.structure_slice(eb, stop, post_allowed, depth + 1, false);
                if let Some(prev) = saved_eb {
                    self.block_start_instr.insert(eb, prev);
                } else {
                    self.block_start_instr.remove(&eb);
                }
                outer_items.push(tail);
                if idx + 1 < post_blocks.len() {
                    outer_items.push(Region::Goto(after_all_lbl));
                    used_after = true;
                }
            }
            if used_after {
                outer_items.push(Region::Labeled(after_all_lbl, Box::new(Region::Empty)));
            }
            return Some((Region::sequence(outer_items), None));
        }

        Some((Region::sequence(outer_items), None))
    }

    fn check_enclosing_loop_boundary(
        &mut self,
        cur: BlockId,
        stop: Option<BlockId>,
        skip_header_guard: bool,
    ) -> Option<Region> {
        let innermost = self.innermost_loop()?.clone();
        // 到达当前最内层循环退出点 → Break
        if innermost.exit == Some(cur) && stop != Some(cur) {
            return Some(Region::Break);
        }
        // 到达当前最内层循环回跳点（非正常尾部 fallthrough；NumericFor latch 需由下方的专属逻辑发射其前缀）
        if !skip_header_guard
            && cur == innermost.continue_target
            && stop != Some(cur)
            && !innermost.numeric_latches.contains(&cur)
        {
            if self.caps.continue_stmt && !innermost.is_fence {
                return Some(Region::Continue);
            }
            if self.caps.goto_label {
                let lbl = self.innermost_continue_label();
                return Some(Region::Goto(lbl));
            }
            // 无 continue/goto 时回到当前循环头代表本轮迭代结束（绝不再递归展开 header！）
            if cur == innermost.header {
                return Some(Region::Empty);
            }
        }
        // 绝不允许在已进入循环体之后沿着任意回边重新展开最内层循环头（防止指数级递归爆炸！）
        if !skip_header_guard && cur == innermost.header && stop != Some(cur) && !innermost.is_fence
        {
            if self.caps.continue_stmt {
                return Some(Region::Continue);
            }
            if self.caps.goto_label {
                let lbl = self.innermost_continue_label();
                return Some(Region::Goto(lbl));
            }
            return Some(Region::Empty);
        }
        // 命中外层循环退出点或回跳点（跨层跳出 / 跨层 continue）
        // 注意：当 `skip_header_guard == true`（刚进入共享头内层循环的首步）时，
        // 绝不能因共享 header 误命中外层循环的 header 而直接跳过整个内层循环体！
        if self.loop_stack.len() > 1 && self.caps.goto_label {
            for idx in (0..self.loop_stack.len() - 1).rev() {
                if self.loop_stack[idx].exit == Some(cur) {
                    let lbl = self.outer_exit_label(idx);
                    return Some(Region::Goto(lbl));
                }
                if !skip_header_guard
                    && (self.loop_stack[idx].continue_target == cur
                        || self.loop_stack[idx].header == cur)
                    && !self.loop_stack[idx].is_fence
                {
                    let lbl = self.outer_continue_label(idx);
                    return Some(Region::Goto(lbl));
                }
            }
        }
        None
    }

    fn emit_out_of_region_jump(&mut self, target: BlockId) -> Option<Region> {
        if let Some(innermost) = self.innermost_loop().cloned() {
            if innermost.exit == Some(target) {
                return Some(Region::Break);
            }
            if (innermost.continue_target == target || innermost.header == target)
                && !innermost.is_fence
            {
                if self.caps.continue_stmt {
                    return Some(Region::Continue);
                }
                if self.caps.goto_label {
                    let lbl = self.innermost_continue_label();
                    return Some(Region::Goto(lbl));
                }
            }
        }
        if self.loop_stack.len() > 1 && self.caps.goto_label {
            for idx in (0..self.loop_stack.len() - 1).rev() {
                if self.loop_stack[idx].exit == Some(target) {
                    let lbl = self.outer_exit_label(idx);
                    return Some(Region::Goto(lbl));
                }
                if (self.loop_stack[idx].continue_target == target
                    || self.loop_stack[idx].header == target)
                    && !self.loop_stack[idx].is_fence
                {
                    let lbl = self.outer_continue_label(idx);
                    return Some(Region::Goto(lbl));
                }
            }
        }
        if self.caps.goto_label {
            let lbl = self.label_for(target);
            return Some(Region::Goto(lbl));
        }
        None
    }

    /// 按需在循环体末尾挂接 `::L_continue::`，并在循环外紧接着挂接 `::L_exit::`。
    fn finalize_loop_labels(
        loop_state: ActiveLoop,
        mut body: Region,
        make_loop: impl FnOnce(Region) -> Region,
    ) -> Region {
        if let Some(cont_lbl) = loop_state.continue_label {
            body = Region::sequence(vec![
                body,
                Region::Labeled(cont_lbl, Box::new(Region::Empty)),
            ]);
        }
        let loop_region = make_loop(body);
        if let Some(exit_lbl) = loop_state.exit_label {
            Region::sequence(vec![
                loop_region,
                Region::Labeled(exit_lbl, Box::new(Region::Empty)),
            ])
        } else {
            loop_region
        }
    }

    fn structure_numeric_for(&mut self, proto_idx: usize, depth: usize) -> Option<(Region, BlockId)> {
        let LoopProtocolHint::NumericFor {
            init_block,
            init_instr,
            body_entry,
            exit_block,
            ref latch_blocks,
            index,
            limit,
            step,
            binding,
        } = self.analysis.cfg.loop_protocols[proto_idx]
        else {
            return None;
        };

        let latch_blocks = latch_blocks.clone();
        let mut body_blocks = BTreeSet::new();
        // 收集从 body_entry 出发在不越过 exit_block/init_block 前可达的循环体块
        let mut work = vec![body_entry];
        while let Some(b) = work.pop() {
            if b == exit_block || b == init_block || b == self.cfg().exit_block {
                continue;
            }
            if !body_blocks.insert(b) {
                continue;
            }
            if latch_blocks.contains(&b) {
                continue;
            }
            for succ in self.cfg().succ_blocks(b) {
                if succ != exit_block
                    && succ != body_entry
                    && !body_blocks.contains(&succ)
                    && self.analysis.graph.dominates(body_entry, succ)
                {
                    work.push(succ);
                }
            }
        }

        let primary_latch = latch_blocks.first().copied().unwrap_or(init_block);
        let numeric_latches: BTreeSet<BlockId> = latch_blocks.iter().copied().collect();

        self.loop_stack.push(ActiveLoop {
            loop_id: None,
            header: init_block,
            continue_target: primary_latch,
            exit: Some(exit_block),
            numeric_latches,
            continue_label: None,
            exit_label: None,
            is_fence: false,
        });
        let prev_irr = self.push_nested_irreducible_regions(&body_blocks, init_block);

        let body = if latch_blocks.len() == 1 && body_entry == primary_latch {
            // 单块数值 for 循环体：只发射 NumericForLoop 之前的语句
            Region::BlockPrefix(primary_latch)
        } else {
            // 不再强制在循环末尾拼接 primary_latch；structure_slice 会在每条真正到达
            // latch 块的路径上自然发射其前缀并结束迭代，彻底避免 break 后残留语句！
            self.structure_slice(body_entry, None, Some(&body_blocks), depth + 1, false)
        };

        self.irreducible_regions.truncate(prev_irr);
        let loop_state = self.loop_stack.pop().unwrap();
        let region = Self::finalize_loop_labels(loop_state, body, |body| Region::NumericFor {
            init_block,
            init_instr,
            body: Box::new(body),
            index,
            limit,
            step,
            binding,
        });
        Some((region, exit_block))
    }

    fn structure_generic_for(&mut self, proto_idx: usize, depth: usize) -> Option<(Region, BlockId)> {
        let LoopProtocolHint::GenericFor {
            prep_block,
            header_block,
            call_instr,
            loop_instr,
            body_entry,
            exit_block,
            iterator,
            state,
            control,
            bindings,
        } = self.analysis.cfg.loop_protocols[proto_idx]
        else {
            return None;
        };

        let effective_exit = self
            .pure_generic_for_close_pad_target(exit_block, iterator)
            .filter(|&t| t != header_block && t != body_entry)
            .unwrap_or(exit_block);

        let mut body_blocks = BTreeSet::new();
        let mut work = vec![body_entry];
        while let Some(b) = work.pop() {
            if b == header_block
                || b == exit_block
                || b == effective_exit
                || b == self.cfg().exit_block
            {
                continue;
            }
            if !body_blocks.insert(b) {
                continue;
            }
            for succ in self.cfg().succ_blocks(b) {
                if succ != header_block
                    && succ != exit_block
                    && succ != effective_exit
                    && !body_blocks.contains(&succ)
                    && self.analysis.graph.dominates(body_entry, succ)
                {
                    work.push(succ);
                }
            }
        }
        self.loop_stack.push(ActiveLoop {
            loop_id: None,
            header: header_block,
            continue_target: header_block,
            exit: Some(effective_exit),
            numeric_latches: BTreeSet::new(),
            continue_label: None,
            exit_label: None,
            is_fence: false,
        });
        let prev_irr = self.push_nested_irreducible_regions(&body_blocks, header_block);

        let body =
            self.structure_slice(body_entry, Some(header_block), Some(&body_blocks), depth + 1, false);
        self.irreducible_regions.truncate(prev_irr);
        let loop_state = self.loop_stack.pop().unwrap();
        let region = Self::finalize_loop_labels(loop_state, body, |body| Region::GenericFor {
            prep_block,
            header_block,
            call_instr,
            loop_instr,
            body: Box::new(body),
            iterator,
            state,
            control,
            bindings,
        });
        Some((region, effective_exit))
    }

    /// Lua 5.5 泛型 for 的正常 `exit_block` 可能是仅关闭循环自有 `<close>` 槽（`from >= iterator`）的纯 Close pad，
    /// 而循环体内的 `break` / 跳出 `goto` 会自带 `Close` 后直接跳过该 pad 落到后续块。
    /// 识别此类纯 Close pad 并推进循环逻辑出口，避免将循环后语句误当作循环内早退 pad 吸进循环体。
    fn pure_generic_for_close_pad_target(
        &self,
        block: BlockId,
        iterator: Reg,
    ) -> Option<BlockId> {
        let cfg = self.cfg();
        if block == cfg.exit_block {
            return None;
        }
        let range = cfg.blocks[block.index()].instrs;
        if range.is_empty() {
            return None;
        }
        let mut saw_close = false;
        for iref in range.iter() {
            match &self.proto.instrs[iref.index()] {
                LowInstr::Close(c)
                    if c.kind == CloseKind::Explicit && c.from.index() >= iterator.index() =>
                {
                    saw_close = true;
                }
                LowInstr::Jump(_) => {}
                _ => return None,
            }
        }
        if !saw_close {
            return None;
        }
        if let [eid] = cfg.succs[block.index()].as_slice() {
            let edge = cfg.edges[eid.index()];
            if !matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                && edge.to != cfg.exit_block
            {
                return Some(edge.to);
            }
        }
        None
    }

    fn structure_natural_loop(
        &mut self,
        nat_loop: &'a NaturalLoop,
        depth: usize,
    ) -> (Region, Option<BlockId>) {
        let cfg = self.cfg();
        let header = nat_loop.header;
        let loop_exit = self.select_loop_exit(nat_loop);

        // Case 1: 前测试 `while cond do body end`
        // 条件：header 以 Branch 结尾（可带短路折叠），且恰好一侧跳到 loop_exit、另一侧留在循环内，
        // 且 header 本身不含除条件准备外的普通语句（避免重复或漏执行语句）。
        if cfg.branch_edges(header).is_some()
            && !self.block_has_non_cond_stmts(header)
            && let Some(folded) =
                fold_condition(self.proto, self.analysis, header, Some(&nat_loop.blocks))
        {
            let then_in = nat_loop.blocks.contains(&folded.then_target);
            let else_in = nat_loop.blocks.contains(&folded.else_target);
            if then_in != else_in {
                let (while_cond, body_start, actual_exit) = if then_in {
                    (folded.cond, folded.then_target, folded.else_target)
                } else {
                    (folded.cond.negate(), folded.else_target, folded.then_target)
                };
                // 在无 goto 方言（Lua 5.1/Luau）下，若循环体内还存在跳向异于 actual_exit 且不能内联到达
                // actual_exit 的其它外部出口（如 `repeat if a then ... else <pad>; break end until c` 的尾条件），
                // 则不应抢先套用 while 壳导致另一出口无处可跳，留给后续 Case 2 (repeat ... until) 准确结构化！
                let exits_compatible = self.caps.goto_label
                    || nat_loop.blocks.iter().all(|&b| {
                        cfg.succs[b.index()].iter().all(|&eid| {
                            let e = cfg.edges[eid.index()];
                            matches!(e.kind, EdgeKind::Return | EdgeKind::TailCall)
                                || nat_loop.blocks.contains(&e.to)
                                || e.to == actual_exit
                                || e.to == cfg.exit_block
                                || self.can_inline_external_exit_pad(e.to, Some(actual_exit))
                        })
                    });
                if !exits_compatible {
                    // fall through to Case 2 (repeat) / Case 3 (while true)
                } else {
                    let mut body_allowed = nat_loop.blocks.clone();
                    body_allowed.remove(&header);
                    for b in &folded.consumed_blocks {
                        body_allowed.remove(b);
                    }
                    self.loop_stack.push(ActiveLoop {
                        loop_id: Some(nat_loop.id),
                        header,
                        continue_target: header,
                        exit: Some(actual_exit),
                        numeric_latches: BTreeSet::new(),
                        continue_label: None,
                        exit_label: None,
                        is_fence: false,
                    });
                    let prev_irr = self.push_nested_irreducible_regions(&body_allowed, header);
                    let body = self.structure_slice(
                        body_start,
                        Some(header),
                        Some(&body_allowed),
                        depth + 1,
                        false,
                    );
                    self.irreducible_regions.truncate(prev_irr);
                    let loop_state = self.loop_stack.pop().unwrap();
                    let region = Self::finalize_loop_labels(loop_state, body, |body| Region::While {
                        cond: while_cond,
                        body: Box::new(body),
                    });
                    return (
                        region,
                        (actual_exit != cfg.exit_block).then_some(actual_exit),
                    );
                }
            }
        }

        // Case 2: 后测试 `repeat body until cond`
        // 支持单块 latch 与复合短路尾条件（如 `until (d and i >= 3) or i >= 4` / `until b or stop(x)`）：
        // 从 latch 往前寻找最早的纯条件入口 `cond_entry`，使得 `fold_condition(cond_entry)` 覆盖 latch
        // 且两个出口恰好为 `{header, actual_exit}`。
        if nat_loop.backedges.len() == 1 {
            let latch = cfg.edges[nat_loop.backedges[0].index()].from;
            if latch != header
                && cfg.branch_edges(latch).is_some()
                && let Some((cond_entry, until_cond, actual_exit, cond_blocks)) =
                    self.find_repeat_until_condition(nat_loop, header, latch)
            {
                let mut body_allowed = nat_loop.blocks.clone();
                body_allowed.remove(&cond_entry);
                body_allowed.remove(&latch);
                for b in &cond_blocks {
                    body_allowed.remove(b);
                }
                self.loop_stack.push(ActiveLoop {
                    loop_id: Some(nat_loop.id),
                    header,
                    continue_target: cond_entry,
                    exit: Some(actual_exit),
                    numeric_latches: BTreeSet::new(),
                    continue_label: None,
                    exit_label: None,
                    is_fence: false,
                });
                let prev_irr = self.push_nested_irreducible_regions(&body_allowed, header);
                let mut parts = Vec::new();
                let main_body = self.structure_slice(
                    header,
                    Some(cond_entry),
                    Some(&body_allowed),
                    depth + 1,
                    true,
                );
                parts.push(main_body);
                if self.has_non_branch_prefix(cond_entry)
                    && self.block_has_non_cond_stmts(cond_entry)
                {
                    parts.push(Region::BlockPrefix(cond_entry));
                }
                self.irreducible_regions.truncate(prev_irr);
                let loop_state = self.loop_stack.pop().unwrap();
                let region = Self::finalize_loop_labels(
                    loop_state,
                    Region::sequence(parts),
                    |body| Region::Repeat {
                        body: Box::new(body),
                        until_cond,
                    },
                );
                return (
                    region,
                    (actual_exit != cfg.exit_block).then_some(actual_exit),
                );
            }
        }

        // Case 3: 通用 `while true do body end`
        self.loop_stack.push(ActiveLoop {
            loop_id: Some(nat_loop.id),
            header,
            continue_target: header,
            exit: loop_exit,
            numeric_latches: BTreeSet::new(),
            continue_label: None,
            exit_label: None,
            is_fence: false,
        });
        let prev_irr = self.push_nested_irreducible_regions(&nat_loop.blocks, header);
        let body = self.structure_loop_body_from_header(header, &nat_loop.blocks, depth + 1);
        self.irreducible_regions.truncate(prev_irr);
        let loop_state = self.loop_stack.pop().unwrap();
        let region = Self::finalize_loop_labels(loop_state, body, |body| Region::While {
            cond: CondExpr::True,
            body: Box::new(body),
        });

        (
            region,
            loop_exit.filter(|&e| e != cfg.exit_block),
        )
    }

    /// 为 `while true` 构造从 `header` 开始的循环体（若存在共享入口的内层循环或嵌套不可规约子区域，先展开）。
    fn structure_loop_body_from_header(
        &mut self,
        header: BlockId,
        loop_blocks: &BTreeSet<BlockId>,
        depth: usize,
    ) -> Region {
        let cfg = self.cfg();
        let mut parts = Vec::new();
        if let Some(&proto_idx) = self.numeric_for_by_init.get(&header)
            && !self.has_enclosing_unentered_natural_loop_over_for(
                proto_idx,
                header,
                Some(loop_blocks),
            )
            && let Some((inner_region, next)) = self.structure_numeric_for(proto_idx, depth + 1)
        {
            parts.push(inner_region);
            parts.push(self.structure_slice(
                next,
                Some(header),
                Some(loop_blocks),
                depth + 1,
                false,
            ));
            return Region::sequence(parts);
        }
        if let Some(&proto_idx) = self.generic_for_by_entry.get(&header)
            && !self.has_enclosing_unentered_natural_loop_over_for(
                proto_idx,
                header,
                Some(loop_blocks),
            )
            && let Some((inner_region, next)) = self.structure_generic_for(proto_idx, depth + 1)
        {
            parts.push(inner_region);
            parts.push(self.structure_slice(
                next,
                Some(header),
                Some(loop_blocks),
                depth + 1,
                false,
            ));
            return Region::sequence(parts);
        }
        if let Some(scc_idx) = self.find_unentered_irreducible_scc(header, Some(loop_blocks)) {
            let (irr_region, next_opt) =
                self.structure_irreducible_scc(scc_idx, header, Some(header), depth + 1);
            parts.push(irr_region);
            if let Some(next) = next_opt {
                parts.push(self.structure_slice(
                    next,
                    Some(header),
                    Some(loop_blocks),
                    depth + 1,
                    false,
                ));
            }
            return Region::sequence(parts);
        }
        if let Some(inner_loop) = self.next_unentered_natural_loop(header, Some(loop_blocks)) {
            let (inner_region, next_opt) = self.structure_natural_loop(inner_loop, depth + 1);
            parts.push(inner_region);
            if let Some(next) = next_opt {
                parts.push(self.structure_slice(
                    next,
                    Some(header),
                    Some(loop_blocks),
                    depth + 1,
                    false,
                ));
            }
            return Region::sequence(parts);
        }
        if self.caps.goto_label
            && let Some((tbc_region, next_opt)) =
                self.try_structure_tbc_scope(header, Some(header), Some(loop_blocks), depth + 1)
        {
            parts.push(tbc_region);
            if let Some(next) = next_opt {
                parts.push(self.structure_slice(
                    next,
                    Some(header),
                    Some(loop_blocks),
                    depth + 1,
                    false,
                ));
            }
            return Region::sequence(parts);
        }
        if cfg.branch_edges(header).is_some()
            && let Some(folded) =
                fold_condition(self.proto, self.analysis, header, Some(loop_blocks))
        {
            if let Some((bool_region, join)) = self.try_fold_bool_materialize(header, &folded) {
                if self.has_non_branch_prefix(header) && self.block_has_non_cond_stmts(header) {
                    parts.push(Region::BlockPrefix(header));
                }
                parts.push(bool_region);
                parts.push(self.structure_slice(
                    join,
                    Some(header),
                    Some(loop_blocks),
                    depth + 1,
                    false,
                ));
                return Region::sequence(parts);
            }
            let (branch_region, next_opt) =
                self.structure_branch(header, folded, Some(header), Some(loop_blocks), depth + 1);
            parts.push(branch_region);
            if let Some(next) = next_opt {
                parts.push(self.structure_slice(
                    next,
                    Some(header),
                    Some(loop_blocks),
                    depth + 1,
                    false,
                ));
            }
            return Region::sequence(parts);
        }

        parts.push(Region::Block(header));
        if let [edge_id] = cfg.succs[header.index()].as_slice() {
            let edge = cfg.edges[edge_id.index()];
            if !matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall) && edge.to != header {
                parts.push(self.structure_slice(
                    edge.to,
                    Some(header),
                    Some(loop_blocks),
                    depth + 1,
                    false,
                ));
            }
        }
        Region::sequence(parts)
    }

    fn select_loop_exit(&self, nat_loop: &NaturalLoop) -> Option<BlockId> {
        let cfg = self.cfg();
        let targets: BTreeSet<BlockId> = nat_loop
            .exits
            .iter()
            .map(|&e| cfg.edges[e.index()].to)
            .collect();
        if targets.is_empty() {
            return None;
        }
        if targets.len() == 1 {
            let single = targets.into_iter().next().unwrap();
            return Some(self.advance_past_loop_private_close_pad(nat_loop, single));
        }
        // 优先选择非 exit_block 的主出口（其余多出口如提前 return 会直接在循环内发射 return）
        let non_return: Vec<BlockId> = targets
            .iter()
            .copied()
            .filter(|&t| t != cfg.exit_block)
            .collect();
        if non_return.len() == 1 {
            return Some(non_return[0]);
        }
        // 优先排除单纯的循环内早退 return/tailcall 块，挑选真正承载循环后代码的延续块作为主出口；
        // 若所有外部出口都是直接 return 块，取块号最大（最靠后）的作为循环尾出口。
        let non_direct_return: Vec<BlockId> = non_return
            .iter()
            .copied()
            .filter(|&t| !self.is_single_block_return(t))
            .collect();
        if non_direct_return.len() == 1 {
            return Some(non_direct_return[0]);
        }
        let candidates = if non_direct_return.is_empty() {
            &non_return
        } else {
            &non_direct_return
        };
        let mut iter = candidates.iter().copied();
        if let Some(first) = iter.next() {
            let mut common = Some(first);
            for next in iter {
                common = common.and_then(|c| self.analysis.graph.nearest_common_postdom(c, next));
            }
            if let Some(c) = common
                && c != cfg.exit_block
                && !nat_loop.blocks.contains(&c)
            {
                return Some(c);
            }
            // 所有候选互不后支配（如多个独立 return 块）：选布局最靠后的那个作为循环尾出口
            return candidates.iter().copied().max_by_key(|b| b.index());
        }
        Some(cfg.exit_block)
    }

    fn is_single_block_return(&self, block: BlockId) -> bool {
        let cfg = self.cfg();
        matches!(
            cfg.succs[block.index()].as_slice(),
            [eid] if matches!(cfg.edges[eid.index()].kind, EdgeKind::Return | EdgeKind::TailCall)
        )
    }

    /// 若自然循环的唯一出口块 `exit` 实际上是循环内的私有清理 pad（例如 `events[#events+1] = "private"; Close(guard); break`
    /// 或 `Close(inner); after-inner; Close(outer); return`），该块仅由循环内进入且进入时循环内的 `<close>` 尚未关闭：
    /// - 若单后继 `next`（或在 `exit` 自身）以 `Close(Explicit)` 关闭循环内 `<close>` 后继续循环外代码，推进 `loop_exit` 至 `next`；
    /// - 若从 `exit` 出发的所有路径均在关闭外层 `<close>` 后直接终止于 `Return`/`TailCall`，返回 `cfg.exit_block`，
    ///   让该退出路径留在循环体内部执行（确保外层 `<close>` 晚于 `after-inner` 关闭）！
    fn advance_past_loop_private_close_pad(
        &self,
        nat_loop: &NaturalLoop,
        exit: BlockId,
    ) -> BlockId {
        let cfg = self.cfg();
        if exit == cfg.exit_block {
            return exit;
        }
        // 仅当 exit 的所有可达前驱均来自循环内部时，才属于本循环私有退出 pad
        if !cfg
            .reachable_preds(exit)
            .all(|e| nat_loop.blocks.contains(&e.from))
        {
            return exit;
        }

        // 计算在进入 `exit` 之前于循环体内声明且尚未关闭的最低 `<close>` 寄存器号：
        // 若某个 `<close>` 在循环体内部（离开至 `exit` 前的所有路径上）均已显式关闭（如 `repeat do local r <close> ... end until done()`），
        // 则绝不应把 `exit` 当作未关闭的循环私有 pad 吸进循环体。
        let mut live_loop_tbc: Option<usize> = None;
        for &tb in &nat_loop.blocks {
            let range = cfg.blocks[tb.index()].instrs;
            for idx in range.start.index()..range.end() {
                let LowInstr::Tbc(t) = &self.proto.instrs[idx] else {
                    continue;
                };
                let r = t.reg.index();
                let closed_in_tb = ((idx + 1)..range.end()).any(|j| {
                    matches!(
                        &self.proto.instrs[j],
                        LowInstr::Close(c) if c.kind == CloseKind::Explicit && c.from.index() <= r
                    )
                });
                if closed_in_tb {
                    continue;
                }
                // 在 `nat_loop.blocks` 内做有界可达性分析：若存在未经过 `Close(from <= r)` 的路径到达 `exit`，则 `r` 进入 `exit` 时仍活跃
                let mut seen = BTreeSet::new();
                let mut work = vec![tb];
                seen.insert(tb);
                let mut reaches_exit_open = false;
                while let Some(b) = work.pop() {
                    if b != tb {
                        let closes_here = cfg.blocks[b.index()].instrs.iter().any(|ir| {
                            matches!(
                                &self.proto.instrs[ir.index()],
                                LowInstr::Close(c)
                                    if c.kind == CloseKind::Explicit && c.from.index() <= r
                            )
                        });
                        if closes_here {
                            continue;
                        }
                    }
                    for succ in cfg.succ_blocks(b) {
                        if succ == exit {
                            reaches_exit_open = true;
                            break;
                        }
                        if nat_loop.blocks.contains(&succ) && seen.insert(succ) {
                            work.push(succ);
                        }
                    }
                    if reaches_exit_open {
                        break;
                    }
                }
                if reaches_exit_open {
                    live_loop_tbc = Some(live_loop_tbc.map_or(r, |m| m.min(r)));
                }
            }
        }

        let block_starts_closing = |b: BlockId, min_reg: usize| -> bool {
            cfg.blocks[b.index()]
                .instrs
                .iter()
                .next()
                .is_some_and(|iref| {
                    matches!(
                        &self.proto.instrs[iref.index()],
                        LowInstr::Close(c)
                            if c.kind == CloseKind::Explicit && c.from.index() <= min_reg
                    )
                })
        };

        let has_explicit_close = cfg.blocks[exit.index()].instrs.iter().any(|iref| {
            matches!(
                &self.proto.instrs[iref.index()],
                LowInstr::Close(c) if c.kind == CloseKind::Explicit
            )
        });

        // 1. 原始规则：`exit` 本身含显式 Close 且单边跳到循环外非终结块 `next`
        if has_explicit_close
            && let [eid] = cfg.succs[exit.index()].as_slice()
        {
            let edge = cfg.edges[eid.index()];
            if !matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                && edge.to != cfg.exit_block
                && !nat_loop.blocks.contains(&edge.to)
            {
                return edge.to;
            }
        }

        // 2. 循环内含 `<close>` 变量且进入 `exit` 时最低 `<close>` 仍活跃未关闭：
        if let Some(tbc_reg) = live_loop_tbc
            && !block_starts_closing(exit, tbc_reg)
        {
            // 2a) `exit` 执行完循环私有语句后单边跳转到以 `Close(from <= tbc_reg)` 开头的公有出口 `next`（如 `exit_03`）
            if let [eid] = cfg.succs[exit.index()].as_slice() {
                let edge = cfg.edges[eid.index()];
                if !matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                    && edge.to != cfg.exit_block
                    && !nat_loop.blocks.contains(&edge.to)
                    && block_starts_closing(edge.to, tbc_reg)
                {
                    return edge.to;
                }
            }
            // 2b) 从 `exit` 出发的所有路径均无环直达 `Return`/`TailCall`（如 `close_12` / `close_19` 的 `after-inner; return`）：
            //     退回 `cfg.exit_block`，使 `exit` 留在循环体内部，保持外层 `<close>` 的存活周期！
            if self.can_inline_external_exit_pad(exit, Some(cfg.exit_block)) {
                return cfg.exit_block;
            }
        }
        exit
    }

    /// 为 `repeat ... until` 从回边块 `latch` 向前搜寻完整的复合短路尾条件入口。
    ///
    /// 返回 `(cond_entry, until_cond, actual_exit, all_cond_blocks)`。
    fn find_repeat_until_condition(
        &self,
        nat_loop: &NaturalLoop,
        header: BlockId,
        latch: BlockId,
    ) -> Option<(BlockId, CondExpr, BlockId, BTreeSet<BlockId>)> {
        let cfg = self.cfg();
        // 先收集以 latch 为尾、在 nat_loop 内的候选条件起点（逆 BFS 最多扩展 12 个条件块）
        let mut candidates = vec![latch];
        let mut seen = BTreeSet::new();
        seen.insert(latch);
        let mut idx = 0;
        while idx < candidates.len() && candidates.len() < 16 {
            let b = candidates[idx];
            idx += 1;
            for pred in cfg.reachable_preds(b) {
                let p = pred.from;
                if p != header
                    && nat_loop.blocks.contains(&p)
                    && cfg.branch_edges(p).is_some()
                    && seen.insert(p)
                {
                    candidates.push(p);
                }
            }
        }

        // 选择覆盖最多条件块且最靠前（RPO 靠前）的合法复合条件起点
        let mut best: Option<(usize, usize, BlockId, CondExpr, BlockId, BTreeSet<BlockId>)> = None;
        for cand in candidates {
            let Some(folded) = fold_condition(self.proto, self.analysis, cand, Some(&nat_loop.blocks))
            else {
                continue;
            };
            let mut all_cond = folded.consumed_blocks.clone();
            all_cond.insert(cand);
            if !all_cond.contains(&latch) {
                continue;
            }
            let then_back = folded.then_target == header;
            let else_back = folded.else_target == header;
            if then_back == else_back {
                continue;
            }
            let (until_cond, actual_exit) = if then_back {
                (folded.cond.negate(), folded.else_target)
            } else {
                (folded.cond, folded.then_target)
            };
            if nat_loop.blocks.contains(&actual_exit) {
                continue;
            }
            // 确保 cond 子图内部块（除 cond_entry 本身外）不被循环体其他路径直接跳入
            let internal_clean = all_cond.iter().all(|&cb| {
                cb == cand
                    || cfg
                        .reachable_preds(cb)
                        .all(|e| all_cond.contains(&e.from))
            });
            if !internal_clean {
                continue;
            }
            let size = all_cond.len();
            let rpo = self
                .analysis
                .graph
                .dom
                .preorder_index[cand.index()]
                .unwrap_or(usize::MAX);
            let better = match &best {
                None => true,
                Some((best_size, best_rpo, ..)) => {
                    size > *best_size || (size == *best_size && rpo < *best_rpo)
                }
            };
            if better {
                best = Some((size, rpo, cand, until_cond, actual_exit, all_cond));
            }
        }
        best.map(|(_, _, entry, cond, exit, blocks)| (entry, cond, exit, blocks))
    }

    /// 判断循环外块 `start` 是否是一条不重入活跃外层循环的小规模自包含早退路径（允许内部包含独立内层循环）：
    /// 所有分支最终全部到达 `loop_exit`（触发 `break`）或 `cfg.exit_block`（触发 `return`/`tailcall`）。
    fn can_inline_external_exit_pad(&self, start: BlockId, loop_exit: Option<BlockId>) -> bool {
        let cfg = self.cfg();
        if start == cfg.exit_block || Some(start) == loop_exit {
            return false;
        }
        let mut seen = BTreeSet::new();
        self.check_exit_pad_region(start, loop_exit, &mut seen)
    }

    fn check_exit_pad_region(
        &self,
        b: BlockId,
        loop_exit: Option<BlockId>,
        seen: &mut BTreeSet<BlockId>,
    ) -> bool {
        let cfg = self.cfg();
        // 不得重入当前任何活跃外层循环头
        if self.loop_stack.iter().any(|l| l.header == b) {
            return false;
        }
        if !seen.insert(b) {
            // 回到出口路径内部已访问块（自包含内层循环或内部菱形合流）允许结构化
            return true;
        }
        if seen.len() >= 32 {
            return false;
        }
        for &eid in &cfg.succs[b.index()] {
            let e = cfg.edges[eid.index()];
            match e.kind {
                EdgeKind::Return | EdgeKind::TailCall => {}
                _ => {
                    if e.to == cfg.exit_block || Some(e.to) == loop_exit {
                        // 到达 loop_exit 将自然发射 Region::Break；到达 exit_block 自然结束
                    } else if !self.check_exit_pad_region(e.to, loop_exit, seen) {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// 检查 `block` 除条件测试本身和仅服务于条件的纯临时求值外，是否含其它前置语句。
    fn block_has_non_cond_stmts(&self, block: BlockId) -> bool {
        !super::cond_fold::is_pure_condition_continuation(self.proto, self.analysis, block)
    }

    /// 检测并折叠 `CMP/TEST -> LoadBool(dst, true/false) -> Join` 布尔物化菱形。
    fn try_fold_bool_materialize(
        &self,
        _header: BlockId,
        folded: &FoldedCondition,
    ) -> Option<(Region, BlockId)> {
        let cfg = self.cfg();
        let then_bool = cfg.bool_load_blocks.get(&folded.then_target)?;
        let else_bool = cfg.bool_load_blocks.get(&folded.else_target)?;
        if then_bool.dst != else_bool.dst
            || then_bool.value == else_bool.value
            || then_bool.next != else_bool.next
        {
            return None;
        }
        let cond = if then_bool.value {
            folded.cond.clone()
        } else {
            folded.cond.clone().negate()
        };
        Some((
            Region::BoolAssign {
                dst: then_bool.dst,
                cond,
                join_block: then_bool.next,
            },
            then_bool.next,
        ))
    }

    /// 结构化条件分支（单臂、双臂、Soft Merge、早退 Guard、循环无 continue 消去）。
    fn structure_branch(
        &mut self,
        header: BlockId,
        folded: FoldedCondition,
        stop: Option<BlockId>,
        allowed: Option<&BTreeSet<BlockId>>,
        depth: usize,
    ) -> (Region, Option<BlockId>) {
        let cfg = self.cfg();
        let mut prefix = Vec::new();
        if let Some(pref) = self.block_prefix_region(header) {
            prefix.push(pref);
        }

        let then_t = folded.then_target;
        let else_t = folded.else_target;
        let cond = folded.cond;

        // 退化同目标分支：仍须保留条件求值（如 `if xs[x] then break end; break` 或 `(a < b and false)`
        // 含 `__index` / `__lt` 元方法副作用），绝不可静默丢弃 `cond`！
        if then_t == else_t {
            prefix.push(Region::If {
                cond,
                then_body: Box::new(Region::Empty),
                else_body: None,
            });
            return (Region::sequence(prefix), Some(then_t));
        }

        // 1. 若某一臂直接到达当前 `stop`（含循环 header 回边），自然形成单臂 `if`
        if Some(else_t) == stop {
            let then_body = self.structure_slice(then_t, stop, allowed, depth + 1, false);
            prefix.push(Region::If {
                cond,
                then_body: Box::new(then_body),
                else_body: None,
            });
            return (Region::sequence(prefix), None);
        }
        if Some(then_t) == stop {
            let else_body = self.structure_slice(else_t, stop, allowed, depth + 1, false);
            prefix.push(Region::If {
                cond: cond.negate(),
                then_body: Box::new(else_body),
                else_body: None,
            });
            return (Region::sequence(prefix), None);
        }

        // 2. 先检测严格后支配菱形合流点（排除单臂直达 `m == then_t || m == else_t`），
        //    若两臂共同汇入同一个下游非终结块 `m`，直接按 `if/else; m` 结构化，
        //    避免早退 Guard 启发式把共享合流尾块（如 `callDelayed(delay, callback); return`）重复拷贝进两臂！
        let mut strict_merge = self
            .analysis
            .graph
            .nearest_common_postdom(then_t, else_t)
            .filter(|&m| {
                m != cfg.exit_block
                    && self.is_forward_reachable_without_backedge(then_t, m, stop, allowed)
                    && self.is_forward_reachable_without_backedge(else_t, m, stop, allowed)
            });
        if let Some(m) = strict_merge
            && let Some(allow) = allowed
            && !allow.contains(&m)
            && Some(m) != stop
        {
            strict_merge = None;
        }
        let has_shared_downstream_merge =
            strict_merge.is_some_and(|m| m != then_t && m != else_t && Some(m) != stop);

        // 3. 早退 Guard 模式：仅当两臂未共同汇入下游合流块，且一臂在到达 `stop` 之前直线终止时，
        //    发射扁平 `if cond then <terminal> end; <continue>`
        if !has_shared_downstream_merge {
            let then_is_guard = self.is_immediate_terminal_arm(then_t, stop, allowed);
            let else_is_guard = self.is_immediate_terminal_arm(else_t, stop, allowed);
            if then_is_guard && !else_is_guard {
                let then_body = self.structure_slice(then_t, stop, allowed, depth + 1, false);
                prefix.push(Region::If {
                    cond,
                    then_body: Box::new(then_body),
                    else_body: None,
                });
                return (Region::sequence(prefix), Some(else_t));
            }
            if else_is_guard && !then_is_guard {
                let else_body = self.structure_slice(else_t, stop, allowed, depth + 1, false);
                prefix.push(Region::If {
                    cond: cond.negate(),
                    then_body: Box::new(else_body),
                    else_body: None,
                });
                return (Region::sequence(prefix), Some(then_t));
            }
        }

        // 4. 计算合流点（Post-Dominator → Soft Merge → 去早退退出子图上的单臂合流点）
        let mut merge = strict_merge;

        if merge.is_none() {
            merge = self
                .find_soft_merge(header, then_t, else_t, allowed)
                .filter(|&m| {
                    self.is_forward_reachable_without_backedge(then_t, m, stop, allowed)
                        && self.is_forward_reachable_without_backedge(else_t, m, stop, allowed)
                });
        }

        // 若严格合流点退化为 `None`（直达 `exit_block`）或退化为函数尾纯空 `return` 块，
        // 检测某一臂在剔除早退（`return`/`break`/纯空 `return` 块）后是否严格汇入另一臂，
        // 彻底避免 `if c1 then ... return end; if c2 then ... return end` 序列引发 $O(2^N)$ 指数续段复制！
        let trivial_ret_merge = merge.filter(|&m| {
            m != then_t && m != else_t && self.is_pure_empty_return_block(m)
        });
        if merge.is_none() || trivial_ret_merge.is_some() {
            if self.is_exit_pruned_arm_merge(
                header,
                then_t,
                else_t,
                stop,
                allowed,
                trivial_ret_merge,
            ) {
                merge = Some(else_t);
            } else if self.is_exit_pruned_arm_merge(
                header,
                else_t,
                then_t,
                stop,
                allowed,
                trivial_ret_merge,
            ) {
                merge = Some(then_t);
            }
        }

        // 合流点不得越出当前 allowed 区域或 stop
        if let Some(m) = merge
            && let Some(allow) = allowed
            && !allow.contains(&m)
            && Some(m) != stop
        {
            merge = stop;
        }

        // 阶梯早退消爆优化（防 $O(2^N)$ 递归爆炸，如 Luau 宽 `(a01 and a02) or (a03 and a04) ...`）：
        // 仅当存在深度 >= 4 的连续单向阶梯（`B_i -> {next_i, arm_i}` 且 `arm_i -> {next_i, m}`，
        // 若按普通双臂 `merge = m` 展开将触发指数级重复结构化）时，将 `next_i` 设为合流点以线性展开阶梯；
        // 对短小 1~3 臂三元表达式（如 `boolean_04` / `boolean_24..29`）保持标准菱形结构化，避免破坏常规三元收敛。
        let merge_is_trivial_terminal = merge.is_none()
            || merge.is_some_and(|m| {
                m != then_t
                    && m != else_t
                    && cfg.succs[m.index()].len() == 1
                    && matches!(
                        cfg.edges[cfg.succs[m.index()][0].index()].kind,
                        EdgeKind::Return | EdgeKind::TailCall
                    )
            });
        if merge_is_trivial_terminal && then_t != else_t {
            let is_ladder_step = |arm: BlockId, next: BlockId| -> bool {
                cfg.succ_blocks(arm).any(|s| s == next)
                    && !self.is_forward_reachable_without_backedge(next, arm, stop, allowed)
                    && cfg.succ_blocks(arm).all(|s| {
                        s == next || Some(s) == merge || Some(s) == stop || s == cfg.exit_block
                    })
            };
            let collect_ladder_chain = |mut cur_next: BlockId| -> Vec<BlockId> {
                let mut chain = vec![header];
                let mut seen_nodes = BTreeSet::new();
                seen_nodes.insert(header);
                while seen_nodes.insert(cur_next) {
                    let Some((te, ee)) = cfg.branch_edges(cur_next) else {
                        break;
                    };
                    let t = cfg.edges[te.index()].to;
                    let e = cfg.edges[ee.index()].to;
                    if t == e {
                        break;
                    }
                    if is_ladder_step(e, t) {
                        chain.push(cur_next);
                        cur_next = t;
                    } else if is_ladder_step(t, e) {
                        chain.push(cur_next);
                        cur_next = e;
                    } else {
                        break;
                    }
                }
                chain
            };
            if is_ladder_step(else_t, then_t) && allowed.is_none_or(|a| a.contains(&then_t)) {
                if self.ladder_blocks.contains(&header) {
                    merge = Some(then_t);
                } else {
                    let chain = collect_ladder_chain(then_t);
                    if chain.len() >= 4 {
                        self.ladder_blocks.extend(chain);
                        merge = Some(then_t);
                    }
                }
            } else if is_ladder_step(then_t, else_t)
                && allowed.is_none_or(|a| a.contains(&else_t))
            {
                if self.ladder_blocks.contains(&header) {
                    merge = Some(else_t);
                } else {
                    let chain = collect_ladder_chain(else_t);
                    if chain.len() >= 4 {
                        self.ladder_blocks.extend(chain);
                        merge = Some(else_t);
                    }
                }
            }
        }

        match merge {
            Some(m) if m == else_t => {
                let then_body = self.structure_slice(then_t, Some(m), allowed, depth + 1, false);
                prefix.push(Region::If {
                    cond,
                    then_body: Box::new(then_body),
                    else_body: None,
                });
                (Region::sequence(prefix), Some(m))
            }
            Some(m) if m == then_t => {
                let else_body = self.structure_slice(else_t, Some(m), allowed, depth + 1, false);
                prefix.push(Region::If {
                    cond: cond.negate(),
                    then_body: Box::new(else_body),
                    else_body: None,
                });
                (Region::sequence(prefix), Some(m))
            }
            Some(m) => {
                let if_region = self.structure_if_chain(
                    cond,
                    then_t,
                    else_t,
                    Some(m),
                    allowed,
                    depth,
                );
                prefix.push(if_region);
                let next = (Some(m) != stop).then_some(m);
                (Region::sequence(prefix), next)
            }
            None => {
                // 两臂均独立终止（如各自 return / break）
                let if_region = self.structure_if_chain(
                    cond,
                    then_t,
                    else_t,
                    stop,
                    allowed,
                    depth,
                );
                prefix.push(if_region);
                (Region::sequence(prefix), None)
            }
        }
    }

    /// 迭代展开共享同一 `arm_stop` 的尾部 `elseif` 链（避免 257+ 臂 `elseif` 消耗递归深度或静默丢代码）。
    fn structure_if_chain(
        &mut self,
        first_cond: CondExpr,
        first_then: BlockId,
        first_else: BlockId,
        arm_stop: Option<BlockId>,
        allowed: Option<&BTreeSet<BlockId>>,
        depth: usize,
    ) -> Region {
        const MAX_ELSEIF_CHAIN: usize = 512;

        let first_then_body = self.structure_slice(first_then, arm_stop, allowed, depth + 1, false);
        let mut arms: Vec<(CondExpr, Region)> = vec![(first_cond, first_then_body)];
        let mut cur_else = first_else;
        let mut inserted_active: Vec<BlockId> = Vec::new();
        let mut final_else: Option<Region> = None;

        let fold_allowed_buf: Option<BTreeSet<BlockId>> = if let Some(s) = arm_stop {
            if let Some(allow) = allowed {
                if allow.contains(&s) {
                    let mut trimmed = allow.clone();
                    trimmed.remove(&s);
                    Some(trimmed)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        };
        let fold_allowed = fold_allowed_buf.as_ref().or(allowed);

        loop {
            let cfg = self.cfg();
            if Some(cur_else) == arm_stop || cur_else == cfg.exit_block {
                break;
            }
            if arms.len() >= MAX_ELSEIF_CHAIN {
                self.hit_depth_limit = true;
                break;
            }
            let can_chain = self.check_enclosing_tbc_boundary(cur_else, arm_stop).is_none()
                && self
                    .check_enclosing_loop_boundary(cur_else, arm_stop, false)
                    .is_none()
                && allowed.is_none_or(|a| a.contains(&cur_else))
                && !self
                    .innermost_loop()
                    .is_some_and(|l| l.numeric_latches.contains(&cur_else))
                && !self.active_slice_blocks.contains(&cur_else)
                && !(self.caps.goto_label
                    && self.label_ids.contains_key(&cur_else)
                    && !self.emitted_labels.contains(&cur_else))
                && !self.numeric_for_by_init.contains_key(&cur_else)
                && !self.generic_for_by_entry.contains_key(&cur_else)
                && self.find_unentered_irreducible_scc(cur_else, allowed).is_none()
                && self.next_unentered_natural_loop(cur_else, allowed).is_none()
                && !self.cfg().blocks[cur_else.index()]
                    .instrs
                    .iter()
                    .any(|ir| matches!(self.proto.instrs[ir.index()], LowInstr::Tbc(_)))
                && self.block_prefix_region(cur_else).is_none()
                && cfg.branch_edges(cur_else).is_some();

            let next_folded = if can_chain {
                fold_condition(self.proto, self.analysis, cur_else, fold_allowed).filter(|f| {
                    f.then_target != f.else_target
                        && self.try_fold_bool_materialize(cur_else, f).is_none()
                })
            } else {
                None
            };

            let Some(folded) = next_folded else {
                let tail = self.structure_slice(cur_else, arm_stop, allowed, depth + 1, false);
                if !tail.is_empty() {
                    final_else = Some(tail);
                }
                break;
            };

            let t = folded.then_target;
            let e = folded.else_target;
            if Some(e) == arm_stop {
                self.active_slice_blocks.insert(cur_else);
                inserted_active.push(cur_else);
                let tb = self.structure_slice(t, arm_stop, allowed, depth + 1, false);
                arms.push((folded.cond, tb));
                break;
            }
            if Some(t) == arm_stop {
                self.active_slice_blocks.insert(cur_else);
                inserted_active.push(cur_else);
                let eb = self.structure_slice(e, arm_stop, allowed, depth + 1, false);
                arms.push((folded.cond.negate(), eb));
                break;
            }
            // 仅当两臂共同汇聚到同一 `arm_stop`（如经典 `elseif x == k then ...` 链）时继续迭代展平；
            // 否则交由 `structure_slice` 按常规合流点/早退逻辑处理。
            let shares_arm_stop = if let Some(m) = arm_stop {
                self.analysis.graph.nearest_common_postdom(t, e) == Some(m)
                    && self.is_forward_reachable_without_backedge(t, m, arm_stop, allowed)
                    && self.is_forward_reachable_without_backedge(e, m, arm_stop, allowed)
            } else {
                self.analysis
                    .graph
                    .nearest_common_postdom(t, e)
                    .is_none_or(|m| m == cfg.exit_block)
                    && !self.is_immediate_terminal_arm(e, arm_stop, allowed)
            };
            if !shares_arm_stop {
                let tail = self.structure_slice(cur_else, arm_stop, allowed, depth + 1, false);
                if !tail.is_empty() {
                    final_else = Some(tail);
                }
                break;
            }

            self.active_slice_blocks.insert(cur_else);
            inserted_active.push(cur_else);
            let tb = self.structure_slice(t, arm_stop, allowed, depth + 1, false);
            arms.push((folded.cond, tb));
            cur_else = e;
        }

        for b in inserted_active {
            self.active_slice_blocks.remove(&b);
        }

        let mut acc = final_else;
        for (cond, then_body) in arms.into_iter().rev() {
            acc = Some(Region::If {
                cond,
                then_body: Box::new(then_body),
                else_body: acc.map(Box::new),
            });
        }
        acc.unwrap_or(Region::Empty)
    }

    /// 判断某分支臂是否为简洁的直接早退（在命中当前 `stop` 之前直接 Break/Return/TailCall）。
    /// 关键不变量：一旦在终止前先命中 `stop`，`structure_slice(start, stop)` 将在 `stop` 处停止而不会发出
    /// 终止语句，若误判为 guard 会导致控制流穿透到另一臂，因此遇到 `stop` 必须返回 `false`！
    fn is_immediate_terminal_arm(
        &self,
        start: BlockId,
        stop: Option<BlockId>,
        allowed: Option<&BTreeSet<BlockId>>,
    ) -> bool {
        let cfg = self.cfg();
        if Some(start) == stop {
            return false;
        }
        if self.is_tbc_early_exit(start) {
            return true;
        }
        if let Some(innermost) = self.innermost_loop()
            && innermost.exit == Some(start)
        {
            return true;
        }
        if start == cfg.exit_block {
            return true;
        }
        let mut cur = start;
        for _ in 0..3 {
            if Some(cur) == stop || self.is_tbc_fallthrough_exit(cur) {
                return false;
            }
            if self.is_tbc_early_exit(cur) {
                return true;
            }
            if let Some(allow) = allowed
                && !allow.contains(&cur)
            {
                let innermost_exit = self.innermost_loop().and_then(|l| l.exit);
                return innermost_exit == Some(cur)
                    || self.can_inline_external_exit_pad(cur, innermost_exit);
            }
            match cfg.succs[cur.index()].as_slice() {
                [edge_id] => {
                    let edge = cfg.edges[edge_id.index()];
                    if matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall) {
                        return true;
                    }
                    if Some(edge.to) == stop {
                        return false;
                    }
                    if self.innermost_loop().is_some_and(|l| l.exit == Some(edge.to)) {
                        return true;
                    }
                    cur = edge.to;
                }
                _ => return false,
            }
        }
        false
    }

    /// 当严格后支配点退化为 `exit_block` 时，在两臂共同支配边界中寻找最近的 Soft Merge。
    fn find_soft_merge(
        &self,
        header: BlockId,
        then_t: BlockId,
        else_t: BlockId,
        allowed: Option<&BTreeSet<BlockId>>,
    ) -> Option<BlockId> {
        let cfg = self.cfg();
        let graph = &self.analysis.graph;
        let else_df: BTreeSet<BlockId> = graph.dom_frontier[else_t.index()].iter().copied().collect();
        let mut candidates: Vec<BlockId> = graph.dom_frontier[then_t.index()]
            .iter()
            .copied()
            .filter(|&b| {
                b != cfg.exit_block
                    && b != header
                    && graph.dominates(header, b)
                    && else_df.contains(&b)
                    && allowed.is_none_or(|a| a.contains(&b))
            })
            .collect();
        candidates.sort_by_key(|&b| graph.dom.preorder_index[b.index()].unwrap_or(usize::MAX));
        candidates.into_iter().next()
    }

    /// 判断基本块是否为无返回值的单指令纯空 `return` 块（如函数尾共享隐式 `RETURN 0 1`）。
    fn is_pure_empty_return_block(&self, block: BlockId) -> bool {
        let cfg = self.cfg();
        let range = cfg.blocks[block.index()].instrs;
        if range.len != 1 {
            return false;
        }
        matches!(
            &self.proto.instrs[range.start.index()],
            LowInstr::Return(ret)
                if matches!(ret.values, crate::transformer::ValuePack::Fixed(r) if r.len == 0)
        )
    }

    /// Exit-pruned 单臂后支配合流检测（$O(|V_{\text{arm}}|)$）：
    /// 判断 `arm` 在剔除早退（`Return`/`TailCall`/`exit_block`/纯空 `return` 块/循环退出边界）后的所有非终结路径，
    /// 是否严格封闭于 `arm` 所支配的局部子图内并汇聚到兄弟分支 `target`。
    ///
    /// 由支配性质可得：若 `arm` 支配从 `arm` 出发到 `target` 围栏之前可达的每一个非终结块，
    /// 则 `target` 绝不可能绕回 `arm` 子图，且 `arm` 绝不可能绕过 `target` 泄漏到 `target` 之后的任何共享续段，
    /// 从而 `Some(target)` 是 100% 精确的单臂合流点，根治连续早退 `if` 序列的 $O(2^N)$ 指数代码膨胀。
    fn is_exit_pruned_arm_merge(
        &self,
        header: BlockId,
        arm: BlockId,
        target: BlockId,
        stop: Option<BlockId>,
        allowed: Option<&BTreeSet<BlockId>>,
        extra_terminal: Option<BlockId>,
    ) -> bool {
        let cfg = self.cfg();
        let graph = &self.analysis.graph;
        if arm == target
            || target == cfg.exit_block
            || target == header
            || Some(target) == stop
            || Some(target) == extra_terminal
            || self.is_loop_boundary_block(target)
        {
            return false;
        }
        if let Some(allow) = allowed
            && !allow.contains(&target)
        {
            return false;
        }
        if !graph.dominates(header, target) {
            return false;
        }

        let innermost_exit = self.innermost_loop().and_then(|l| l.exit);
        let mut work = vec![arm];
        let mut seen = BTreeSet::new();
        let mut reached_target = false;

        while let Some(b) = work.pop() {
            if !seen.insert(b) {
                continue;
            }
            // 核心支配不变量：从 `arm` 出发在遇到 `target` 围栏之前可达的每个非终结块都必须被 `arm` 支配，
            // 否则说明存在从 `target` 或外部绕入的合流点（不能把 `target` 当作单臂合流点）。
            if !graph.dominates(arm, b) {
                return false;
            }
            for &eid in &cfg.succs[b.index()] {
                let edge = cfg.edges[eid.index()];
                if matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall) {
                    continue;
                }
                let succ = edge.to;
                if succ == target {
                    // 必须是正向边（非回边）
                    if !graph.dominates(succ, b) {
                        reached_target = true;
                        continue;
                    }
                    return false;
                }
                if succ == cfg.exit_block
                    || Some(succ) == extra_terminal
                    || self.is_pure_empty_return_block(succ)
                    || innermost_exit == Some(succ)
                    || self.is_tbc_early_exit(succ)
                {
                    continue;
                }
                // 仅当回边目标位于 `arm` 自身支配的子图内部时才属于 `arm` 内部子循环回边；
                // 若跳回外层活跃循环头（`continue` 边）或外层 `stop`，在 `merge = target` 下会穿透至 `target` 或被迫注入 `goto`，必须拒绝！
                if graph.dominates(succ, b) {
                    if graph.dominates(arm, succ) {
                        continue;
                    }
                    return false;
                }
                if Some(succ) == stop || self.is_loop_boundary_block(succ) {
                    return false;
                }
                if let Some(allow) = allowed
                    && !allow.contains(&succ)
                {
                    if innermost_exit == Some(succ)
                        || self.can_inline_external_exit_pad(succ, innermost_exit)
                    {
                        continue;
                    }
                    return false;
                }
                if !seen.contains(&succ) {
                    work.push(succ);
                }
            }
        }

        reached_target
    }

    /// 检查从 `start` 出发在不跨过 `stop`、不沿回边重入任何活跃循环头、不越出 `allowed`
    /// 的前提下，能否正向到达候选合流点 `target`。
    fn is_forward_reachable_without_backedge(
        &self,
        start: BlockId,
        target: BlockId,
        stop: Option<BlockId>,
        allowed: Option<&BTreeSet<BlockId>>,
    ) -> bool {
        if start == target {
            return true;
        }
        let cfg = self.cfg();
        let mut work = vec![start];
        let mut seen = BTreeSet::new();
        while let Some(b) = work.pop() {
            if !seen.insert(b) {
                continue;
            }
            if Some(b) == stop || b == cfg.exit_block {
                continue;
            }
            if let Some(allow) = allowed
                && !allow.contains(&b)
            {
                continue;
            }
            for &eid in &cfg.succs[b.index()] {
                let edge = cfg.edges[eid.index()];
                if matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall) {
                    continue;
                }
                let succ = edge.to;
                if succ == target {
                    // 仅当不是回边（succ 不支配 b）时才算正向到达
                    if !self.analysis.graph.dominates(succ, b) {
                        return true;
                    }
                    continue;
                }
                if Some(succ) == stop
                    || succ == cfg.exit_block
                    || self.is_active_loop_header(succ)
                    || self.analysis.graph.dominates(succ, b)
                {
                    continue;
                }
                if !seen.contains(&succ) {
                    work.push(succ);
                }
            }
        }
        false
    }

    /// 切除外层循环回边后，在循环体 `scope` 内检测嵌套的多入口不可规约子 SCC（例如 `repeat` 内嵌套双向 `goto` 环），
    /// 并将其沿公共支配块提升为局部单入口超区域压栈，彻底消除递归展开爆炸。
    fn push_nested_irreducible_regions(
        &mut self,
        scope: &BTreeSet<BlockId>,
        cut_header: BlockId,
    ) -> usize {
        let prev_len = self.irreducible_regions.len();
        if scope.len() < 2 {
            return prev_len;
        }
        let nested = find_nested_irreducible_super_regions(self.analysis, scope, cut_header);
        for reg in nested {
            if !self
                .irreducible_regions
                .iter()
                .any(|existing| existing.entry == reg.entry && existing.blocks == reg.blocks)
            {
                self.irreducible_regions.push(reg);
            }
        }
        prev_len
    }

    fn find_unentered_irreducible_scc(
        &self,
        block: BlockId,
        allowed: Option<&BTreeSet<BlockId>>,
    ) -> Option<usize> {
        self.irreducible_regions
            .iter()
            .enumerate()
            .find_map(|(idx, reg)| {
                (reg.entry == block && allowed.is_none_or(|a| reg.blocks.is_subset(a)))
                    .then_some(idx)
            })
    }

    /// Phase 2 完备兜底：对单入口化后的不可规约超区域按 `ControlFlowCaps` 降级。
    /// - 支持 `goto`（Lua 5.2+ / LuaJIT）：按 RPO 发射带 `Labeled`/`Goto` 的同级平铺区域；
    /// - 不支持 `goto`（Lua 5.1 / Luau）：发射局部 `StateMachine`（100% 合法可编译）。
    fn structure_irreducible_scc(
        &mut self,
        region_idx: usize,
        entry: BlockId,
        stop: Option<BlockId>,
        depth: usize,
    ) -> (Region, Option<BlockId>) {
        let scc_blocks = self.irreducible_regions[region_idx].blocks.clone();
        self.structure_block_set_flat(&scc_blocks, entry, stop, depth)
    }

    /// 函数级完备兜底：若结构化后仍残余跨作用域不可见 `goto`，退回单级平铺表示（100% 合法）。
    fn structure_flat_proto_fallback(&mut self) -> Region {
        let cfg = self.cfg();
        self.loop_stack.clear();
        self.active_slice_blocks.clear();
        self.label_ids.clear();
        self.emitted_labels.clear();
        let all_blocks: BTreeSet<BlockId> = cfg
            .block_order
            .iter()
            .copied()
            .filter(|&b| b != cfg.exit_block)
            .collect();
        let (region, _) =
            self.structure_block_set_flat(&all_blocks, cfg.entry_block, Some(cfg.exit_block), 0);
        region
    }

    /// 计算极性无关的局部 RPO：条件分支按非取反（正极性）目标优先探索，避免重编译翻转条件极性导致平铺块序两轮震荡。
    fn canonical_rpo_for_block_set(
        &self,
        scc_blocks: &BTreeSet<BlockId>,
        entry: BlockId,
    ) -> Vec<BlockId> {
        let cfg = self.cfg();
        let mut visited = BTreeSet::new();
        let mut postorder = Vec::with_capacity(scc_blocks.len());

        let mut stack: Vec<(BlockId, Vec<BlockId>, usize)> = Vec::new();
        let succs_of = |b: BlockId| -> Vec<BlockId> {
            if let Some((te, fe)) = cfg.branch_edges(b)
                && let Some(LowInstr::Branch(br)) = cfg.terminator(self.proto, b)
            {
                let then_t = cfg.edges[te.index()].to;
                let else_t = cfg.edges[fe.index()].to;
                let (first, second) = if br.cond.negated {
                    (then_t, else_t)
                } else {
                    (else_t, then_t)
                };
                let mut out = Vec::with_capacity(2);
                if scc_blocks.contains(&first) {
                    out.push(first);
                }
                if second != first && scc_blocks.contains(&second) {
                    out.push(second);
                }
                return out;
            }
            cfg.succ_blocks(b)
                .filter(|s| scc_blocks.contains(s))
                .collect()
        };

        let push_root = |root: BlockId,
                             visited: &mut BTreeSet<BlockId>,
                             stack: &mut Vec<(BlockId, Vec<BlockId>, usize)>,
                             postorder: &mut Vec<BlockId>| {
            if !visited.insert(root) {
                return;
            }
            stack.push((root, succs_of(root), 0));
            while let Some((b, succs, idx)) = stack.last_mut() {
                if *idx < succs.len() {
                    let s = succs[*idx];
                    *idx += 1;
                    if visited.insert(s) {
                        stack.push((s, succs_of(s), 0));
                    }
                } else {
                    postorder.push(*b);
                    stack.pop();
                }
            }
        };

        if scc_blocks.contains(&entry) {
            push_root(entry, &mut visited, &mut stack, &mut postorder);
        }
        for &b in &cfg.block_order {
            if scc_blocks.contains(&b) {
                push_root(b, &mut visited, &mut stack, &mut postorder);
            }
        }
        postorder.reverse();
        if let Some(pos) = postorder.iter().position(|&b| b == entry)
            && pos != 0
        {
            postorder.remove(pos);
            postorder.insert(0, entry);
        }
        postorder
    }

    fn structure_block_set_flat(
        &mut self,
        scc_blocks: &BTreeSet<BlockId>,
        entry: BlockId,
        stop: Option<BlockId>,
        depth: usize,
    ) -> (Region, Option<BlockId>) {
        let cfg = self.cfg();

        // 收集区域外部主出口（过滤掉直达外层循环边界或经纯 Close pad 跳出循环的出口）
        let is_direct_loop_transfer = |b: BlockId| -> bool {
            let eff = self
                .pure_generic_for_close_pad_target(b, Reg(0))
                .unwrap_or(b);
            self.loop_stack.iter().any(|l| {
                l.exit == Some(eff)
                    || (!l.is_fence && (l.continue_target == eff || l.header == eff))
            })
        };
        let mut external_targets = BTreeSet::new();
        for &b in scc_blocks {
            for succ in cfg.succ_blocks(b) {
                if !scc_blocks.contains(&succ)
                    && succ != cfg.exit_block
                    && !is_direct_loop_transfer(succ)
                {
                    external_targets.insert(succ);
                }
            }
        }
        let continuation = external_targets
            .iter()
            .copied()
            .next()
            .filter(|&t| Some(t) != stop);

        // 按极性无关的 RPO 排序区域内部块（对条件分支固定按非取反方向优先探索，消除 `if a then goto` <-> `if not a then goto` 的两轮震荡）
        let ordered = self.canonical_rpo_for_block_set(scc_blocks, entry);

        if self.caps.goto_label {
            if self.emitted_labels.contains(&entry) {
                let lbl = self.label_for(entry);
                return (Region::Goto(lbl), None);
            }
            // 为本次区域向 `continuation` 的跳出分配专属的局部尾标签，
            // 绝不提前把 `continuation` 块本身标记为 `emitted_labels`（否则紧随其后的下一段 SCC 会误以为自己已发射而死循环 goto 自身！）
            let mut cont_exit_lbl: Option<usize> = None;
            let mut stmts = Vec::new();
            let mut consumed_by_for = BTreeSet::new();
            for (pos, &block) in ordered.iter().enumerate() {
                if consumed_by_for.contains(&block) || !self.emitted_labels.insert(block) {
                    continue;
                }
                let next_in_order = ordered
                    .iter()
                    .skip(pos + 1)
                    .copied()
                    .find(|b| !consumed_by_for.contains(b));
                let lbl = self.label_for(block);

                // 若区域内部完整包含显式 NumericFor/GenericFor，尽量保留原 for 结构
                if let Some(&proto_idx) = self.numeric_for_by_init.get(&block)
                    && let Some(for_blocks) = self.collect_for_blocks_if_contained(proto_idx, scc_blocks)
                    && let Some((for_reg, after_for)) = self.structure_numeric_for(proto_idx, depth + 1)
                {
                    consumed_by_for.extend(for_blocks);
                    let mut body_parts = vec![for_reg];
                    if after_for != cfg.exit_block && Some(after_for) != next_in_order {
                        body_parts.push(self.scc_jump_region(
                            after_for,
                            next_in_order,
                            continuation,
                            &mut cont_exit_lbl,
                        ));
                    }
                    stmts.push(Region::Labeled(lbl, Box::new(Region::sequence(body_parts))));
                    continue;
                }
                if let Some(&proto_idx) = self.generic_for_by_entry.get(&block)
                    && let Some(for_blocks) = self.collect_for_blocks_if_contained(proto_idx, scc_blocks)
                    && let Some((for_reg, after_for)) = self.structure_generic_for(proto_idx, depth + 1)
                {
                    consumed_by_for.extend(for_blocks);
                    let mut body_parts = vec![for_reg];
                    if after_for != cfg.exit_block && Some(after_for) != next_in_order {
                        body_parts.push(self.scc_jump_region(
                            after_for,
                            next_in_order,
                            continuation,
                            &mut cont_exit_lbl,
                        ));
                    }
                    stmts.push(Region::Labeled(lbl, Box::new(Region::sequence(body_parts))));
                    continue;
                }

                let mut body_parts = Vec::new();
                if let Some((te, fe)) = cfg.branch_edges(block)
                    && let Some(LowInstr::Branch(br)) = cfg.terminator(self.proto, block)
                {
                    let then_t = cfg.edges[te.index()].to;
                    let else_t = cfg.edges[fe.index()].to;
                    let single_folded = FoldedCondition {
                        cond: CondExpr::Atom {
                            block,
                            cond: br.cond,
                        },
                        then_target: then_t,
                        else_target: else_t,
                        consumed_blocks: BTreeSet::new(),
                    };
                    let can_fold_bool = scc_blocks.contains(&then_t)
                        && scc_blocks.contains(&else_t)
                        && then_t != else_t
                        && !consumed_by_for.contains(&then_t)
                        && !consumed_by_for.contains(&else_t)
                        && !self.emitted_labels.contains(&then_t)
                        && !self.emitted_labels.contains(&else_t)
                        && cfg.reachable_preds(then_t).all(|e| e.from == block)
                        && cfg.reachable_preds(else_t).all(|e| e.from == block);
                    if can_fold_bool
                        && let Some((bool_reg, join_b)) =
                            self.try_fold_bool_materialize(block, &single_folded)
                    {
                        if let Some(pref) = self.block_prefix_region(block) {
                            body_parts.push(pref);
                        }
                        consumed_by_for.insert(then_t);
                        consumed_by_for.insert(else_t);
                        body_parts.push(bool_reg);
                        let next_after = ordered
                            .iter()
                            .skip(pos + 1)
                            .copied()
                            .find(|b| !consumed_by_for.contains(b));
                        if join_b != cfg.exit_block && Some(join_b) != next_after {
                            body_parts.push(self.scc_jump_region(
                                join_b,
                                next_after,
                                continuation,
                                &mut cont_exit_lbl,
                            ));
                        }
                    } else {
                        if self.has_non_branch_prefix(block) && self.block_has_non_cond_stmts(block) {
                            body_parts.push(Region::BlockPrefix(block));
                        }
                        let then_r =
                            self.scc_jump_region(then_t, next_in_order, continuation, &mut cont_exit_lbl);
                        let else_r =
                            self.scc_jump_region(else_t, next_in_order, continuation, &mut cont_exit_lbl);
                        body_parts.push(Region::If {
                            cond: CondExpr::Atom {
                                block,
                                cond: br.cond,
                            },
                            then_body: Box::new(then_r),
                            else_body: (!else_r.is_empty()).then(|| Box::new(else_r)),
                        });
                    }
                } else {
                    body_parts.push(Region::Block(block));
                    if let [eid] = cfg.succs[block.index()].as_slice() {
                        let edge = cfg.edges[eid.index()];
                        if !matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall)
                            && Some(edge.to) != next_in_order
                        {
                            body_parts.push(self.scc_jump_region(
                                edge.to,
                                next_in_order,
                                continuation,
                                &mut cont_exit_lbl,
                            ));
                        }
                    }
                }
                let block_region = Region::sequence(body_parts);
                let block_region = if self.block_tbc_closes_on_all_exits(block) {
                    Region::DoScope(Box::new(block_region))
                } else {
                    block_region
                };
                stmts.push(Region::Labeled(lbl, Box::new(block_region)));
            }
            if let Some(exit_lbl) = cont_exit_lbl {
                stmts.push(Region::Labeled(exit_lbl, Box::new(Region::Empty)));
            }
            return (Region::sequence(stmts), continuation);
        }

        // Lua 5.1 / Luau：局部状态机分发器（100% 合法可编译，零非法 goto）
        let state_by_block: BTreeMap<BlockId, usize> = ordered
            .iter()
            .enumerate()
            .map(|(i, &b)| (b, i + 1))
            .collect();
        let entry_state = state_by_block[&entry];
        let mut states = Vec::with_capacity(ordered.len());

        for &block in &ordered {
            let state_id = state_by_block[&block];
            if let Some((te, fe)) = cfg.branch_edges(block)
                && let Some(LowInstr::Branch(br)) = cfg.terminator(self.proto, block)
            {
                let then_t = cfg.edges[te.index()].to;
                let else_t = cfg.edges[fe.index()].to;
                let body = if self.has_non_branch_prefix(block)
                    && self.block_has_non_cond_stmts(block)
                {
                    Region::BlockPrefix(block)
                } else {
                    Region::Empty
                };
                states.push(StateArm {
                    state_id,
                    block,
                    body,
                    next: StateTransition::Branch {
                        cond: CondExpr::Atom {
                            block,
                            cond: br.cond,
                        },
                        then_state: state_by_block.get(&then_t).copied(),
                        else_state: state_by_block.get(&else_t).copied(),
                    },
                });
            } else {
                let next = match cfg.succs[block.index()].as_slice() {
                    [eid] => {
                        let edge = cfg.edges[eid.index()];
                        match edge.kind {
                            EdgeKind::Return | EdgeKind::TailCall => StateTransition::Terminated,
                            _ => state_by_block
                                .get(&edge.to)
                                .copied()
                                .map_or(StateTransition::Exit, StateTransition::Jump),
                        }
                    }
                    _ => StateTransition::Terminated,
                };
                states.push(StateArm {
                    state_id,
                    block,
                    body: Region::Block(block),
                    next,
                });
            }
        }

        (
            Region::StateMachine {
                entry_state,
                states,
            },
            continuation,
        )
    }

    fn collect_for_blocks_if_contained(
        &self,
        proto_idx: usize,
        container: &BTreeSet<BlockId>,
    ) -> Option<BTreeSet<BlockId>> {
        let cfg = self.cfg();
        let (entry, body_entry, exit_block, stop_extra) = match &self.analysis.cfg.loop_protocols[proto_idx] {
            LoopProtocolHint::NumericFor {
                init_block,
                body_entry,
                exit_block,
                latch_blocks,
                ..
            } => (*init_block, *body_entry, *exit_block, latch_blocks.clone()),
            LoopProtocolHint::GenericFor {
                prep_block,
                header_block,
                body_entry,
                exit_block,
                ..
            } => (
                prep_block.unwrap_or(*header_block),
                *body_entry,
                *exit_block,
                vec![*header_block],
            ),
        };
        let mut blocks = BTreeSet::new();
        blocks.insert(entry);
        let mut work = vec![body_entry];
        for &b in &stop_extra {
            blocks.insert(b);
        }
        while let Some(b) = work.pop() {
            if b == exit_block || b == cfg.exit_block || !blocks.insert(b) {
                continue;
            }
            for succ in cfg.succ_blocks(b) {
                if succ != exit_block
                    && !blocks.contains(&succ)
                    && self.analysis.graph.dominates(body_entry, succ)
                {
                    work.push(succ);
                }
            }
        }
        // 确认外部没有边直接跳入 for 循环内部（仅允许进入 entry）
        if !blocks.is_subset(container) {
            return None;
        }
        for &b in &blocks {
            if b == entry {
                continue;
            }
            if cfg.reachable_preds(b).any(|e| !blocks.contains(&e.from)) {
                return None;
            }
        }
        Some(blocks)
    }

    fn scc_jump_region(
        &mut self,
        target: BlockId,
        next_in_order: Option<BlockId>,
        continuation: Option<BlockId>,
        cont_exit_lbl: &mut Option<usize>,
    ) -> Region {
        if Some(target) == next_in_order
            || (next_in_order.is_none() && Some(target) == continuation)
        {
            return Region::Empty;
        }
        if Some(target) == continuation {
            let lbl = *cont_exit_lbl.get_or_insert_with(|| self.alloc_fresh_label());
            return Region::Goto(lbl);
        }
        let resolved = self
            .pure_generic_for_close_pad_target(target, Reg(0))
            .unwrap_or(target);
        if self
            .innermost_loop()
            .is_some_and(|l| l.exit == Some(target) || l.exit == Some(resolved))
        {
            return Region::Break;
        }
        if let Some(innermost) = self.innermost_loop()
            && (innermost.continue_target == target
                || innermost.header == target
                || innermost.continue_target == resolved
                || innermost.header == resolved)
            && !innermost.is_fence
        {
            if self.caps.continue_stmt {
                return Region::Continue;
            }
            if self.caps.goto_label {
                let lbl = self.innermost_continue_label();
                return Region::Goto(lbl);
            }
        }
        if self.loop_stack.len() > 1 {
            for idx in (0..self.loop_stack.len() - 1).rev() {
                if (self.loop_stack[idx].exit == Some(target)
                    || self.loop_stack[idx].exit == Some(resolved))
                    && self.caps.goto_label
                {
                    let lbl = self.outer_exit_label(idx);
                    return Region::Goto(lbl);
                }
            }
        }
        let lbl = self.label_for(target);
        Region::Goto(lbl)
    }
}

/// 切除外层循环 `cut_header` 的入边后，在 `scope` 诱导子图上运行迭代 Tarjan SCC，
/// 找出嵌套的多入口不可规约子 SCC，并沿公共支配块提升为 `scope` 内的单入口超区域。
fn find_nested_irreducible_super_regions(
    analysis: &ProtoAnalysis,
    scope: &BTreeSet<BlockId>,
    cut_header: BlockId,
) -> Vec<IrreducibleSuperRegion> {
    let cfg = &analysis.cfg;
    let graph = &analysis.graph;

    let nodes: Vec<BlockId> = scope.iter().copied().collect();
    let mut index_of: BTreeMap<BlockId, usize> = BTreeMap::new();
    let mut lowlink: BTreeMap<BlockId, usize> = BTreeMap::new();
    let mut on_stack: BTreeSet<BlockId> = BTreeSet::new();
    let mut tarjan_stack: Vec<BlockId> = Vec::new();
    let mut next_index = 0usize;
    let mut sccs: Vec<BTreeSet<BlockId>> = Vec::new();

    for &start in &nodes {
        if index_of.contains_key(&start) {
            continue;
        }
        let mut dfs: Vec<(BlockId, usize)> = vec![(start, 0)];
        index_of.insert(start, next_index);
        lowlink.insert(start, next_index);
        next_index += 1;
        tarjan_stack.push(start);
        on_stack.insert(start);

        while let Some((v, edge_i)) = dfs.last_mut() {
            let v = *v;
            let succ_edges = &cfg.succs[v.index()];
            if *edge_i < succ_edges.len() {
                let eid = succ_edges[*edge_i];
                *edge_i += 1;
                let edge = cfg.edges[eid.index()];
                if matches!(edge.kind, EdgeKind::Return | EdgeKind::TailCall) {
                    continue;
                }
                let w = edge.to;
                if w == cut_header || !scope.contains(&w) {
                    continue;
                }
                if let std::collections::btree_map::Entry::Vacant(e) = index_of.entry(w) {
                    e.insert(next_index);
                    lowlink.insert(w, next_index);
                    next_index += 1;
                    tarjan_stack.push(w);
                    on_stack.insert(w);
                    dfs.push((w, 0));
                } else if on_stack.contains(&w) {
                    let w_idx = index_of[&w];
                    let v_low = lowlink.get_mut(&v).unwrap();
                    *v_low = (*v_low).min(w_idx);
                }
            } else {
                dfs.pop();
                if let Some(&(parent, _)) = dfs.last() {
                    let v_low = lowlink[&v];
                    let p_low = lowlink.get_mut(&parent).unwrap();
                    *p_low = (*p_low).min(v_low);
                }
                if lowlink[&v] == index_of[&v] {
                    let mut comp = BTreeSet::new();
                    while let Some(w) = tarjan_stack.pop() {
                        on_stack.remove(&w);
                        comp.insert(w);
                        if w == v {
                            break;
                        }
                    }
                    if comp.len() > 1 {
                        sccs.push(comp);
                    }
                }
            }
        }
    }

    let mut regions: Vec<IrreducibleSuperRegion> = Vec::new();
    for comp in sccs {
        let mut entries = Vec::new();
        for &b in &comp {
            let has_external_pred = cfg
                .reachable_preds(b)
                .any(|e| !comp.contains(&e.from) && (scope.contains(&e.from) || e.from == cut_header));
            if has_external_pred {
                entries.push(b);
            }
        }
        if entries.len() < 2 {
            continue;
        }
        let mut lca = entries[0];
        for &next in &entries[1..] {
            if let Some(d) = graph.nearest_common_dom(lca, next) {
                lca = d;
            }
        }
        if !scope.contains(&lca) {
            continue;
        }
        let blocks = expand_single_entry_closure_in_scope(cfg, graph, lca, &comp, scope);
        regions.push(IrreducibleSuperRegion { entry: lca, blocks });
    }

    merge_overlapping_irreducible_regions(cfg, graph, &mut regions, Some(scope));
    regions
}

/// 将所有不可规约多入口 SCC 沿 `nearest_common_dom(entries)` 提升为单入口超区域并合并相交区域。
///
/// 这保证分发入口与所有 SCC 入口发射在同一平级词法块中，彻底消除跨 `if/else` 臂的 `InvisibleGotoLabel`
/// 以及 Lua 5.1 下的多份重复状态机。
fn build_irreducible_super_regions(analysis: &ProtoAnalysis) -> Vec<IrreducibleSuperRegion> {
    let cfg = &analysis.cfg;
    let graph = &analysis.graph;
    let mut regions: Vec<IrreducibleSuperRegion> = Vec::new();

    for scc in &graph.sccs {
        if !scc.is_irreducible() {
            continue;
        }
        let mut iter = scc.entries.iter().copied();
        let Some(first) = iter.next() else {
            continue;
        };
        let mut lca = first;
        for next in iter {
            if let Some(d) = graph.nearest_common_dom(lca, next) {
                lca = d;
            }
        }
        let blocks = expand_single_entry_closure(cfg, graph, lca, &scc.blocks);
        regions.push(IrreducibleSuperRegion { entry: lca, blocks });
    }

    // 合并相交的超区域（重新计算合并后入口的 LCA）
    merge_overlapping_irreducible_regions(cfg, graph, &mut regions, None);

    regions
}

fn merge_overlapping_irreducible_regions(
    cfg: &Cfg,
    graph: &crate::analysis::GraphFacts,
    regions: &mut Vec<IrreducibleSuperRegion>,
    scope: Option<&BTreeSet<BlockId>>,
) {
    loop {
        let mut merge_pair: Option<(usize, usize)> = None;
        'outer: for i in 0..regions.len() {
            for j in (i + 1)..regions.len() {
                if !regions[i].blocks.is_disjoint(&regions[j].blocks) {
                    merge_pair = Some((i, j));
                    break 'outer;
                }
            }
        }
        let Some((i, j)) = merge_pair else {
            break;
        };
        let other = regions.remove(j);
        let new_entry = graph
            .nearest_common_dom(regions[i].entry, other.entry)
            .unwrap_or(regions[i].entry);
        let mut combined_seed = regions[i].blocks.clone();
        combined_seed.extend(other.blocks);
        let blocks = match scope {
            Some(sc) => expand_single_entry_closure_in_scope(cfg, graph, new_entry, &combined_seed, sc),
            None => expand_single_entry_closure(cfg, graph, new_entry, &combined_seed),
        };
        regions[i] = IrreducibleSuperRegion {
            entry: new_entry,
            blocks,
        };
    }
}

/// 收集由 `entry` 支配且能到达 `seed` 集合的 `scope` 内所有块，构成单入口超区域。
fn expand_single_entry_closure_in_scope(
    cfg: &Cfg,
    graph: &crate::analysis::GraphFacts,
    entry: BlockId,
    seed: &BTreeSet<BlockId>,
    scope: &BTreeSet<BlockId>,
) -> BTreeSet<BlockId> {
    let mut blocks = seed.clone();
    blocks.insert(entry);
    let mut work: Vec<BlockId> = seed.iter().copied().collect();
    while let Some(b) = work.pop() {
        if b == entry {
            continue;
        }
        for pred in cfg.reachable_preds(b) {
            let p = pred.from;
            if scope.contains(&p) && graph.dominates(entry, p) && blocks.insert(p) {
                work.push(p);
            }
        }
    }
    blocks
}

/// 收集由 `entry` 支配且能到达 `seed` 集合的所有块，构成单入口超区域。
fn expand_single_entry_closure(
    cfg: &Cfg,
    graph: &crate::analysis::GraphFacts,
    entry: BlockId,
    seed: &BTreeSet<BlockId>,
) -> BTreeSet<BlockId> {
    let mut blocks = seed.clone();
    blocks.insert(entry);
    let mut work: Vec<BlockId> = seed.iter().copied().collect();
    while let Some(b) = work.pop() {
        if b == entry {
            continue;
        }
        for pred in cfg.reachable_preds(b) {
            let p = pred.from;
            if graph.dominates(entry, p) && blocks.insert(p) {
                work.push(p);
            }
        }
    }
    blocks
}

/// 轻量检验 `Region` 树中所有 `Goto(lbl)` 目标的存在性、唯一性与 Lua 块级可见性。
fn region_gotos_are_valid(root: &Region) -> bool {
    let mut block_parents: Vec<Option<usize>> = Vec::new();
    let mut labels: BTreeMap<usize, usize> = BTreeMap::new();
    let mut gotos: Vec<(usize, usize)> = Vec::new();
    let mut ok = true;

    fn visit_block(
        reg: &Region,
        parent: Option<usize>,
        block_parents: &mut Vec<Option<usize>>,
        labels: &mut BTreeMap<usize, usize>,
        gotos: &mut Vec<(usize, usize)>,
        ok: &mut bool,
    ) {
        let block_id = block_parents.len();
        block_parents.push(parent);
        visit_in_block(reg, block_id, block_parents, labels, gotos, ok);
    }

    fn visit_in_block(
        reg: &Region,
        block_id: usize,
        block_parents: &mut Vec<Option<usize>>,
        labels: &mut BTreeMap<usize, usize>,
        gotos: &mut Vec<(usize, usize)>,
        ok: &mut bool,
    ) {
        match reg {
            Region::Sequence(items) => {
                for item in items {
                    visit_in_block(item, block_id, block_parents, labels, gotos, ok);
                }
            }
            Region::Labeled(lbl, inner) => {
                if labels.insert(*lbl, block_id).is_some() {
                    *ok = false;
                }
                visit_in_block(inner, block_id, block_parents, labels, gotos, ok);
            }
            Region::Goto(lbl) => gotos.push((*lbl, block_id)),
            Region::If {
                then_body,
                else_body,
                ..
            } => {
                visit_block(then_body, Some(block_id), block_parents, labels, gotos, ok);
                if let Some(eb) = else_body {
                    visit_block(eb, Some(block_id), block_parents, labels, gotos, ok);
                }
            }
            Region::While { body, .. }
            | Region::Repeat { body, .. }
            | Region::NumericFor { body, .. }
            | Region::GenericFor { body, .. }
            | Region::DoScope(body) => {
                visit_block(body, Some(block_id), block_parents, labels, gotos, ok);
            }
            Region::StateMachine { states, .. } => {
                for arm in states {
                    visit_block(&arm.body, Some(block_id), block_parents, labels, gotos, ok);
                }
            }
            Region::Empty
            | Region::Block(_)
            | Region::BlockPrefix(_)
            | Region::BlockSlice { .. }
            | Region::BoolAssign { .. }
            | Region::Break
            | Region::Continue => {}
        }
    }

    visit_block(root, None, &mut block_parents, &mut labels, &mut gotos, &mut ok);
    if !ok {
        return false;
    }
    for (target_lbl, src_block) in gotos {
        let Some(&lbl_block) = labels.get(&target_lbl) else {
            return false;
        };
        // Lua 块级可见性：label 所在块必须是 goto 所在块的祖先（或同一块）
        let mut cur = Some(src_block);
        let mut visible = false;
        while let Some(b) = cur {
            if b == lbl_block {
                visible = true;
                break;
            }
            cur = block_parents[b];
        }
        if !visible {
            return false;
        }
    }
    true
}
