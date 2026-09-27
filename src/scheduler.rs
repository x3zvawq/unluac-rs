//! HIR/AST 共用的失效标签与事实消费顺序调度器。
//!
//! pass 通过 depends_on/invalidates 声明形状依赖，调度器管理执行与收敛，不拥有
//! 表达式改写或生命周期证明。consumer 还可要求更早的 owner 在消费前保持最新；
//! 例如 temp-inline 暴露 constructor 后，locals 不能先合并其不同 SSA producer。
//!
//! owner 在本轮输入失效时即时刷新，其它 pass 保持阶段及相对执行顺序；不需要重复
//! 登记同一 pass，也不把身份消费推迟到所有不相关改写完成之后。
//!
//! ## 核心概念
//!
//! - **Tag**：一组粗粒度变化标签（如 `StatementAdjacency`、`TempChain`），由各层自行定义。
//! - **Phase**：可选的阶段分区。标记为 `Deferred` 的 pass 只在所有 `Normal` pass
//!   收敛后才执行；如果 `Deferred` pass 又产出新 invalidation，会触发 `Normal` pass 重跑。
//!   `Final` 等这两个阶段均稳定后才消费不可逆的高层事实；有变化仍回到同一收敛循环。
//! - **收敛**：当一轮遍历中没有任何 pass 返回 `changed=true` 时收敛。
//! - **上限**：达到轮数上限不等于收敛；调用层必须把它作为显式错误处理，不能继续消费
//!   可能仍处于中间态的产物。

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
    /// 最终阶段：Normal/Deferred 联合稳定后才执行，避免提前降低仍可消费的事实。
    /// 首个改写后立即回到 Normal，再审理后续 Final；不另设或重置收敛预算。
    Final,
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

/// fixed-point 调度的终止状态。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InvalidationConvergence {
    Converged,
    LimitExceeded { rounds: usize },
}

/// 调度器的运行时入口。
///
/// 接受一组 pass 描述和对应的执行函数，按固定点策略执行。
/// `run_pass(index, name)` 执行第 `index` 个 pass，返回是否产生了变化。
/// `prerequisites` 按声明顺序刷新 consumer 的直接 owner；owner 可继续声明更早的依赖。
///
/// 调度顺序：
/// 1. 反复执行所有 `Normal` phase 的 pass，直到 dirty set 清空（Normal 收敛）。
/// 2. 执行一遍所有 `Deferred` phase 的 pass。
/// 3. 如果 Deferred 有变化，回到步骤 1；否则执行 Final。
/// 4. Final 有变化仍回到步骤 1；否则整体收敛。
pub fn run_invalidation_loop<T, F>(
    passes: &[PassDescriptor<T>],
    prerequisites: &[(&str, &str)],
    mut run_pass: F,
    max_rounds: usize,
) -> InvalidationConvergence
where
    T: InvalidationTag,
    F: FnMut(usize, &str) -> bool,
{
    // 依赖只能指向同阶段更早的 owner，排除循环并保留既有阶段顺序。
    let mut required = vec![Vec::new(); passes.len()];
    for &(consumer, owner) in prerequisites {
        let consumer = passes
            .iter()
            .position(|pass| pass.name == consumer)
            .expect("consumer pass exists");
        let owner = passes
            .iter()
            .position(|pass| pass.name == owner)
            .expect("owner pass exists");
        assert!(
            owner < consumer && passes[owner].phase == passes[consumer].phase,
            "pass prerequisites must be earlier owners in the same phase"
        );
        assert!(
            !required[consumer].contains(&owner),
            "consumer must not repeat a prerequisite owner"
        );
        required[consumer].push(owner);
    }
    // 初始：所有 tag 都 dirty（第一轮每个 pass 都要跑）
    let mut dirty: BTreeSet<T> = T::all().iter().copied().collect();
    let mut rounds = 0;

    loop {
        // ── Normal phase: 固定点收敛 ──
        if !run_phase_until_converged(
            passes,
            &required,
            PassPhase::Normal,
            &mut dirty,
            &mut run_pass,
            max_rounds,
            &mut rounds,
        ) {
            return InvalidationConvergence::LimitExceeded { rounds };
        }

        // ── Deferred phase: 单遍执行 ──
        // Normal 收敛后 dirty set 通常为空（没有 pass 再产出变化）。但 Deferred pass
        // 还没跑过，必须给它们至少一次执行机会，因此在 Deferred round 前把所有 tag
        // 重新标记为 dirty。
        dirty = T::all().iter().copied().collect();
        let deferred_changed = run_single_round(
            passes,
            &required,
            PassPhase::Deferred,
            &mut dirty,
            &mut run_pass,
        );
        if !deferred_changed {
            // Deferred 无变化会消费掉所有 dirty tag；Final 仍须获得首次审理机会。
            // 用 changed 而非 tag 是否为空判断稳定：有些语法终结 pass 不发布形状 tag。
            dirty = T::all().iter().copied().collect();
            if !run_single_round(
                passes,
                &required,
                PassPhase::Final,
                &mut dirty,
                &mut run_pass,
            ) {
                return InvalidationConvergence::Converged;
            }
        }
        rounds += 1;
        if rounds >= max_rounds {
            return InvalidationConvergence::LimitExceeded { rounds };
        }
        // Deferred/Final 有变化 → 回到 Normal，继续使用同一个总轮数预算。
    }
}

/// 反复执行某个 phase 的所有 pass 直到 dirty set 中没有该 phase 关心的 tag。
fn run_phase_until_converged<T, F>(
    passes: &[PassDescriptor<T>],
    required: &[Vec<usize>],
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
    loop {
        if *rounds >= max_rounds {
            return false;
        }

        let round_changed = run_single_round(passes, required, phase, dirty, run_pass);

        if round_changed {
            *rounds += 1;
        } else {
            return true;
        }
    }
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
    required: &[Vec<usize>],
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
    let mut current = vec![false; passes.len()];

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

        round_changed |= run_current_pass(
            passes,
            required,
            index,
            &mut current,
            &mut newly_dirty,
            run_pass,
        );
        // Final 的后续 pass 可能不可逆地降低事实；先让前层消费刚恢复的
        // 作用域/表达式，不能在同一轮先丢掉它们仍需要的 SETLIST 等来源。
        if phase == PassPhase::Final && round_changed {
            break;
        }
    }

    // 本轮结束：dirty set 只保留新产出的 tag
    *dirty = newly_dirty;

    round_changed
}

/// owner 执行后若又有输入变化，必须在身份消费前刷新；不提前重跑其它 pass。
fn run_current_pass<T, F>(
    passes: &[PassDescriptor<T>],
    required: &[Vec<usize>],
    index: usize,
    current: &mut [bool],
    newly_dirty: &mut BTreeSet<T>,
    run_pass: &mut F,
) -> bool
where
    T: InvalidationTag,
    F: FnMut(usize, &str) -> bool,
{
    if current[index] {
        return false;
    }
    let mut changed = false;
    for &owner in &required[index] {
        changed |= run_current_pass(passes, required, owner, current, newly_dirty, run_pass);
    }
    let desc = &passes[index];
    if run_pass(index, desc.name) {
        changed = true;
        newly_dirty.extend(desc.invalidates);
        for (other, pass) in passes.iter().enumerate() {
            if pass
                .depends_on
                .iter()
                .any(|tag| desc.invalidates.contains(tag))
            {
                current[other] = false;
            }
        }
    }
    current[index] = true;
    changed
}
