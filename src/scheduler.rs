//! Invalidation 驱动的 fixed-point pass 调度器。
//!
//! AST Readability 和 HIR Simplify 都存在"前面的 pass 暴露了新形状，后面某个 pass
//! 需要重跑"的场景。此前靠手动在序列中重复放置同一 pass（如 statement-merge 出现两次）
//! 来解决，每次新增 pass 都要手动推演和谁有顺序依赖，容易漏。
//!
//! 这个模块提供了一个泛型调度器 `InvalidationRunner`，让每个 pass 声明"我修改什么"
//! (`invalidates`) 和"我关心什么"(`depends_on`)，调度器根据 dirty set 自动决定
//! 哪些 pass 需要重跑、何时收敛。
//!
//! ## 核心概念
//!
//! - **Tag**：一组粗粒度变化标签（如 `StatementAdjacency`、`TempChain`），由各层自行定义。
//! - **Phase**：可选的阶段分区。标记为 `Deferred` 的 pass 只在所有 `Normal` pass
//!   收敛后才执行；如果 `Deferred` pass 又产出新 invalidation，会触发 `Normal` pass 重跑。
//! - **收敛**：当一轮遍历中没有任何 pass 返回 `changed=true` 时收敛。

use std::collections::BTreeSet;
use std::fmt;

/// pass 的阶段归属。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PassPhase {
    /// 正常阶段：每轮 fixed-point 都参与。
    Normal,
    /// 延迟阶段：等 Normal pass 全部收敛后才执行。
    /// 如果执行后产出新 invalidation，会触发 Normal pass 再次收敛。
    Deferred,
}

/// 一个 pass 的静态描述。
///
/// `T` 是 invalidation tag 的枚举类型（由各层定义）。
pub struct PassDescriptor<T: InvalidationTag> {
    pub name: &'static str,
    pub phase: PassPhase,
    /// 当这些 tag 中的任意一个处于 dirty 状态时，本 pass 才有可能需要执行。
    pub depends_on: &'static [T],
    /// 当本 pass 实际产生了变化时，会把这些 tag 标记为 dirty。
    pub invalidates: &'static [T],
}

/// invalidation tag 需要实现的 trait 约束。
pub trait InvalidationTag: Copy + Eq + Ord + fmt::Debug + 'static {
    /// 返回该枚举的所有变体，用于初始化全量 dirty set。
    fn all() -> &'static [Self];
}

/// 调度器的运行时入口。
///
/// 接受一组 pass 描述和对应的执行函数，按固定点策略执行。
/// `run_pass(index, name)` 执行第 `index` 个 pass，返回是否产生了变化。
///
/// 调度顺序：
/// 1. 反复执行所有 `Normal` phase 的 pass，直到 dirty set 清空（Normal 收敛）。
/// 2. 执行一遍所有 `Deferred` phase 的 pass。
/// 3. 如果 Deferred 产出了新的 dirty tag，回到步骤 1；否则整体收敛。
pub fn run_invalidation_loop<T, F>(
    passes: &[PassDescriptor<T>],
    mut run_pass: F,
    max_rounds: usize,
) -> bool
where
    T: InvalidationTag,
    F: FnMut(usize, &str) -> bool,
{
    // 初始：所有 tag 都 dirty（第一轮每个 pass 都要跑）
    let mut dirty: BTreeSet<T> = T::all().iter().copied().collect();
    let mut any_change_overall = false;
    let mut rounds = 0;

    loop {
        // ── Normal phase: 固定点收敛 ──
        let normal_changed = run_phase_until_converged(
            passes,
            PassPhase::Normal,
            &mut dirty,
            &mut run_pass,
            max_rounds,
            &mut rounds,
        );
        any_change_overall |= normal_changed;

        // ── Deferred phase: 单遍执行 ──
        // Normal 收敛后 dirty set 通常为空（没有 pass 再产出变化）。但 Deferred pass
        // 还没跑过，必须给它们至少一次执行机会，因此在 Deferred round 前把所有 tag
        // 重新标记为 dirty。
        dirty = T::all().iter().copied().collect();
        let deferred_changed = run_single_round(
            passes,
            PassPhase::Deferred,
            &mut dirty,
            &mut run_pass,
        );
        any_change_overall |= deferred_changed;

        if deferred_changed {
            rounds += 1;
        }

        if !deferred_changed || rounds >= max_rounds {
            break;
        }
        // Deferred 产出了新 dirty → 回到 Normal 重新收敛
    }

    any_change_overall
}

/// 反复执行某个 phase 的所有 pass 直到 dirty set 中没有该 phase 关心的 tag。
fn run_phase_until_converged<T, F>(
    passes: &[PassDescriptor<T>],
    phase: PassPhase,
    dirty: &mut BTreeSet<T>,
    run_pass: &mut F,
    max_rounds: usize,
    rounds: &mut usize,
) -> bool
where
    T: InvalidationTag,
    F: FnMut(usize, &str) -> bool,
{
    let mut any_change = false;

    loop {
        if *rounds >= max_rounds {
            break;
        }

        let round_changed = run_single_round(passes, phase, dirty, run_pass);
        any_change |= round_changed;

        if round_changed {
            *rounds += 1;
        } else {
            break;
        }
    }

    any_change
}

/// 对某个 phase 的所有 pass 遍历一遍。
///
/// 逻辑：
/// - 遍历前，快照当前 dirty set 作为本轮的"可消费 tag"。
/// - 每个 pass 检查 depends_on 是否和快照有交集，有则执行。
/// - 执行产生变化时，将 invalidates 写入一个单独的 `newly_dirty` 集合。
/// - 遍历结束后，dirty set = newly_dirty（快照中的旧 tag 已被消费掉）。
fn run_single_round<T, F>(
    passes: &[PassDescriptor<T>],
    phase: PassPhase,
    dirty: &mut BTreeSet<T>,
    run_pass: &mut F,
) -> bool
where
    T: InvalidationTag,
    F: FnMut(usize, &str) -> bool,
{
    // 快照：本轮可消费的 dirty tag
    let snapshot = dirty.clone();
    let mut newly_dirty: BTreeSet<T> = BTreeSet::new();
    let mut round_changed = false;

    for (index, desc) in passes.iter().enumerate() {
        if desc.phase != phase {
            continue;
        }

        // 只在 depends_on 和（快照 ∪ 本轮新产出）有交集时才执行
        let relevant = desc
            .depends_on
            .iter()
            .any(|tag| snapshot.contains(tag) || newly_dirty.contains(tag));
        if !relevant {
            continue;
        }

        let changed = run_pass(index, desc.name);
        if changed {
            round_changed = true;
            for tag in desc.invalidates {
                newly_dirty.insert(*tag);
            }
        }
    }

    // 本轮结束：dirty set 只保留新产出的 tag
    *dirty = newly_dirty;

    round_changed
}
