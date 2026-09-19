//! control_flow 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;

// Lua 5.5 的首个 generic-for binding 为 const，其余方言允许源码重赋值。
const MUTABLE_GENERIC_KEY_DIALECTS: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua51,
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Luajit,
    LuaCaseDialect::Luau,
];

pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_28_preserved_predicates.lua",
        &["short-circuit", "path-condition", "source-fidelity"],
        "保留原字节码的重复条件检查，不依据前一条路径事实删除。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_27_short_circuit_capture_scope.lua",
        &["short-circuit", "closure-capture", "close", "metamethod"],
        "短路复合条件与闭包 scope 共存时保持单入口结构、字段读取顺序及 close 后捕获身份。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_43_nested_generic_key.lua",
        &["generic-for", "numeric-for", "phi"],
        "内层循环重赋值外层可见 key/value 时，外层迭代器的隐藏 control 仍按原顺序推进。",
        &[
            LuaCaseConfiguration::new(MUTABLE_GENERIC_KEY_DIALECTS),
            LuaCaseConfiguration::new(MUTABLE_GENERIC_KEY_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_42_nested_generic_binding.lua",
        &["generic-for", "numeric-for", "phi", "metamethod"],
        "外层 generic-for 的可见迭代变量进入内层循环并重赋值，不误判成 VM 控制槽或改写隐藏 control。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_26_condition_value_boundary.lua",
        &["short-circuit", "numeric-for", "metamethod", "phi"],
        "嵌套 or 取值先形成独立 ValueDecision，再由外层条件消费，保持字段读取和循环累加。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_16_short_circuit_open_call.lua",
        &["short-circuit", "multiret", "metamethod"],
        "短路值 DAG 沿开放参数追踪嵌套调用依赖，保持共享 fallback、字段读取及转换次数。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_01_guarded_return_chain.lua",
        &["callbacks", "multiret", "short-circuit"],
        "固定 Lua 5.1 中 guarded return 链的分支所有权以及 handled 路径三返回值中的 nil 槽。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_01_if_else_short_circuit_shared_body.lua",
        &["early-return", "generic-for", "short-circuit"],
        "恢复长 elseif 链中 bubble/bossBubble 共享 body、pig 嵌套分支和 stop 早退，而不引入闭包模拟。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/repeat_01_nested_repeat_continue_flag.lua",
        &["break", "repeat", "state-machine"],
        "在保留 debug 的全方言实例中，用 continue_inner 标志串联嵌套 repeat 的 break/继续状态机。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_02_lua51_event_guard_goto_recovery.lua",
        &["debug-flow", "early-return", "method-call"],
        "将事件 guard、默认 delay 值与多个早退恢复为结构化分支，避免 Lua 5.1 生成 goto/label。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/entry_01_adjacent_loop_redefining_header_state.lua",
        &["numeric-for", "phi", "repeat"],
        "验证 numeric-for 结束后相邻 repeat 重定义同一 x 时，第二个 loop header 仍继承前一循环的 live-out。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/entry_02_implicit_else_loop_backedge.lua",
        &["nested-loop", "repeat", "structure-only", "while"],
        "分别覆盖共享 header 的内外循环 owner，以及直接回 header 的分支臂作为内层空下一轮路径。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/tail_01_repeat_nested_loop_shared_tail.lua",
        &["break", "repeat", "structure-only", "while"],
        "固定内层 repeat 的非 break 路径与外层 repeat 共享 tail 时，while 和 break 仍归各自结构 owner。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_01_luau_repeat_skip_numeric_for.lua",
        &["continue", "numeric-for", "structure-only"],
        "恢复 Luau repeat 条件 continue 跳过完整 numeric-for 的结构，并避免伪造 else 或畸形 generic-for 参数。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_01_luau_same_header_loop_path_owner.lua",
        &["numeric-for", "repeat", "structure-only", "while"],
        "按入口区分共享 header 的 numeric-for、while 与外层 repeat，防止三个 loop 候选争用同一 owner。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_02_luau_repeat_current_iteration_tail.lua",
        &["continue", "repeat"],
        "固定 O2 下 early continue 只能跳过当前迭代，不能跨迭代抢占 repeat 与嵌套循环的共享 tail。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/exit_01_luau_linear_break_exit_pad.lua",
        &["break", "numeric-for"],
        "证明 O2 展开的独占线性块仍属于同一个 break exit pad，并恢复 until false 载体。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_01_luau_repeat_optimized_core_tail.lua",
        &["numeric-for", "repeat"],
        "在 O2 展开块中恢复 repeat 的原始 tail guard，而不反转为额外 if 壳。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_02_luau_generic_for_exit_break_pad.lua",
        &["break", "generic-for"],
        "让 generic-for 的透明退出 pad 汇入立即 break body，同时跨 Luau O2 与 Lua 5.1/LuaJIT 默认配置保留协议。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS),
            LuaCaseConfiguration::new(LUA_51_AND_LUAJIT),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/tail_02_luau_short_continue_shared_tail.lua",
        &["continue", "generic-for"],
        "区分短路 continue 与后续 break 对当前 generic-for tail 的共享与所有权。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_03_luau_continue_merge_state_owner.lua",
        &["continue", "nested-loop"],
        "在 O0/O1/O2 全优化档中让多个 continue merge pad 保留各自嵌套 loop state owner。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_03_luau_short_circuit_outer_break.lua",
        &["break", "short-circuit"],
        "证明短路真臂跨过完整内层 numeric-for 后的 break 归属外层 generic-for。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_04_luau_repeat_continue_pad_shared_tail.lua",
        &["continue", "repeat"],
        "确保 repeat continue pad 不吞掉共享 body tail 与 until condition。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_05_luau_early_continue_nested_loop_tail.lua",
        &["continue", "generic-for"],
        "阻止 early-continue guard 抢占后续 nested generic-for 的 tail 与 x 更新。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_03_luau_repeat_continue_pad_owner.lua",
        &["continue", "repeat"],
        "确认 repeat 的透明 continue pad 由分支臂消费而不会变成 goto。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/tail_04_loop_break_shared_continuation.lua",
        &["binary-like", "generic-for", "while"],
        "在两层循环和字符解码逻辑中恢复带短路条件的 while break continuation，不产生 unresolved/goto。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/tail_03_luau_short_continue_nested_tail_break.lua",
        &["continue", "metamethod", "repeat"],
        "分离短路 continue、nested repeat 与 tail break 的 owner，同时观察跨轮索引读取。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/break_01_luau_short_circuit_immediate_repeat_break.lua",
        &["break", "eval-count", "repeat"],
        "保持 repeat body 短路失败出口的立即 break，并防止条件调用次数因重构变化。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_04_luau_same_header_loop_break_owner.lua",
        &["generic-for", "repeat", "returned-function"],
        "防止 same-header loop 的条件 header 被前置短路吞并，并明确该字节码不应恢复 continue。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_04_luau_dual_early_return_soft_merge.lua",
        &["early-return", "phi"],
        "确保 if 两臂早退后，共同尾部仍取得各臂赋给 x 的正确值。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/repeat_02_luau_repeat_condition_side_effect.lua",
        &["repeat", "returned-function", "side-effect"],
        "保证 repeat 条件前的 print 副作用不会被伪造 continue 跳过。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_05_header_plain_nested_loops.lua",
        &["break", "repeat", "while"],
        "证明共用 header 的普通 while/repeat 仍恢复为两个严格嵌套 loop。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/break_02_lua51_nonempty_backedge_pad.lua",
        &["backedge", "early-return", "while"],
        "确认回边上的 a=true 赋值属于 while body，而不是 repeat 条件 pad。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_02_then_merge_ownership.lua",
        &["eval-order", "shared-tail", "short-circuit"],
        "区分短路 else pad 与嵌套 if 的共享 tail 所有权。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_06_same_header_sibling_latches.lua",
        &["break", "loop-owner", "while"],
        "防止单个 while 的 sibling latch 被误拆为嵌套 loop。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_07_generic_for_nested_continue.lua",
        &["early-return", "generic-for", "nested-loop"],
        "三层 generic-for 在找到目标时跨层早退，未命中时完整遍历并返回 nil。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_05_luau_repeat_recompile_state_owner.lua",
        &["phi", "repeat", "returned-function"],
        "repeat再编译产生的中间phi仍归外层loop state。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_06_lua51_single_arm_nested_generic_for.lua",
        &["generic-for", "while"],
        "单臂if内的空body generic-for仍保留完整owner。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_03_generic_for_terminal_guard.lua",
        &["generic-for", "terminal-guard"],
        "两层generic-for内的shared terminal guard应结构化并在episode_end返回true。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_08_luau_numeric_for_branch_owner.lua",
        &["break", "continue", "numeric-for"],
        "numeric-for内continue与break分支保持互斥owner且两处x增量不被合并。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_09_luau_nested_repeat_short_circuit_merge.lua",
        &["repeat", "short-circuit"],
        "短路链尾与plain if-then共享本轮merge而不反转外层条件。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_10_luau_while_continue_break_tail.lua",
        &["break", "continue", "while"],
        "分别保护early continue后的tail break、nested repeat后的外层continue及出口state。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_02_repeat_nested_break_return.lua",
        &["break", "early-return", "repeat"],
        "嵌套break/return不能把repeat单臂误推成跨loop if-else。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_11_luau_short_circuit_break_shared_tail.lua",
        &["break", "repeat", "short-circuit"],
        "短路一臂经guard break、另一臂直达shared tail时保持owner。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_04_numeric_for_terminal_body.lua",
        &["numeric-for", "terminal-body"],
        "numeric-for body只含terminal return时仍恢复为for而非goto。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_12_same_header_repeat_short_circuit.lua",
        &["repeat", "short-circuit", "while"],
        "外层repeat的b or c尾条件不能与空body内层while合并。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_13_puc_repeat_condition_exit.lua",
        &["condition", "repeat", "while"],
        "复合尾条件简化后退出方向仍为x==3。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_14_same_header_conditional_sibling_latch.lua",
        &["break", "sibling-latch", "while"],
        "内层条件break退出整个while时不误拆same-header latch。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_16_generic_for_break_pad.lua",
        &["break", "generic-for", "method"],
        "generic-for break pad不能被误判为terminal exit，循环后particles调用必须保留。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_15_same_header_repeat_body.lua",
        &["repeat", "state", "while"],
        "outer repeat的状态body不能阻断same-header内层loop候选。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_05_sibling_latch_terminal_loop.lua",
        &["sibling-latch", "terminal", "while"],
        "多个sibling latch回到同一while header并保留三个terminal return。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_18_short_circuit_loop_shared_tail.lua",
        &["generic-for", "return", "short-circuit"],
        "bonus短路臂在generic-for命中后返回display_number，共享尾不落入goto。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_17_numeric_for_shared_tail.lua",
        &["branch", "numeric-for", "phi"],
        "分支汇入numeric-for共享尾后仍执行value增量。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/island_01_numeric_for_before_irreducible_goto.lua",
        &["goto", "irreducible", "numeric-for", "ordering"],
        "局部不可规约island不能拖垮其前置numeric-for和prefix物化。",
        &[LuaCaseConfiguration::new(LUA_GOTO_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/island_02_branch_control_forward_guards.lua",
        &["goto", "guard", "irreducible"],
        "island内多个forward guard共享done label仍保留各入口值。",
        &[LuaCaseConfiguration::new(LUA_GOTO_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/island_03_irreducible_plain_loop_owner.lua",
        &["goto", "irreducible", "numeric-for", "while"],
        "island内plain loop只保留必要goto，同时前置for保持结构化。",
        &[LuaCaseConfiguration::new(LUA_GOTO_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_06_terminal_empty_return_guard.lua",
        &["convergence", "empty-return", "pcall"],
        "空return两臂不能与尾return清理反复互换。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_07_terminal_exit_unknown_loop.lua",
        &["break", "capture", "error", "while"],
        "多terminal exit仍恢复while且每轮closure捕获value不被常量化。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_20_numeric_for_latch_shared_else.lua",
        &["elseif", "method", "numeric-for"],
        "numeric-for latch保持隐式继续并保留calendar多臂else。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/island_04_irreducible_for_owners.lua",
        &["generic-for", "goto", "numeric-for", "structure-contract"],
        "同一不可规约骨架分别保留numeric/generic-for子owner、双结构合同及四种入口结果。",
        &[
            LuaCaseConfiguration::new(LUA_GOTO_DIALECTS).with_structure_contracts(&[
                LuaCaseStructureContract::MixedUnstructuredChildLoop {
                    dialect: LuaCaseDialect::Lua54,
                    protocol: LuaCaseLoopProtocol::NumericFor,
                },
                LuaCaseStructureContract::MixedUnstructuredChildLoop {
                    dialect: LuaCaseDialect::Lua54,
                    protocol: LuaCaseLoopProtocol::GenericFor,
                },
            ]),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_19_while_true_header_guard.lua",
        &["header-guard", "while"],
        "while true正文header guard不能误成repeat尾条件。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_08_shared_terminal_return.lua",
        &["branch", "terminal"],
        "多层访问判断共享true/false terminal不退回goto。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_21_repeat_multileaf_backedges.lua",
        &["break", "repeat", "short-circuit"],
        "短路条件每个leaf拥有repeat backedge，with/without break保持边界。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_22_if_then_continuation.lua",
        &["generic-for", "implicit-else", "while"],
        "while/generic-for的implicit else必须绕过gated tail。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/island_06_irreducible_linear_exit.lua",
        &["closure", "goto", "irreducible"],
        "island拥有其单入口observable IIFE安装出口链。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_52)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_03_or_guard_shared_tail.lua",
        &["or-guard", "shared-tail"],
        "多层析取guard的false edges共享else tail。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_04_shared_continuation.lua",
        &["early-return", "shared-tail"],
        "branch body与未进入臂共享非terminal :tail continuation。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_27_while_true_latch_tail.lua",
        &["latch", "while"],
        "while true跳转latch tail保持结构化。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_29_lua51_loop_branch_recovery.lua",
        &["generic-for", "naming-variants"],
        "同一文件保护for guard、while header、nil live value和iterator前debug scope。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)
            .with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            })
            .with_variants(ALL_NAMING_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_09_numeric_for_terminal_branch_coverage.lua",
        &["numeric-for", "terminal"],
        "for体共享terminal return保持结构化。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_32_generic_for_immediate_break.lua",
        &["break", "generic-for"],
        "generic-for immediate break保持for。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_09_short_circuit_exit_jump_pad.lua",
        &["jump-pad", "method", "short-circuit"],
        "短路出口空pad随条件消费并保留state:add。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_37_loop_branch_merge.lua",
        &["branch", "coroutine", "while", "yield"],
        "无限循环内部分支合流须保留每轮状态并可持续yield。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/tail_08_tail_loop_path_check.lua",
        &["branch", "return", "shared-tail", "while"],
        "拥有while退出的分支之后仍须落到共同尾部而非生成goto。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_38_exit_generic_owner.lua",
        &["break", "generic-for", "owner", "state"],
        "generic-for的break退出值必须归属正确外层结构。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_22_degenerate_numeric_for.lua",
        &["break", "numeric-for", "return", "unreachable-latch"],
        "首轮必break使latch不可达时仍须识别numeric-for并保留终端body返回。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_23_luau_empty_generic_for.lua",
        &["continue", "generic-for", "repeat"],
        "continue-only generic-for折叠到header后仍须保留外层迭代与repeat退出。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/break_06_loop_nested_break_continuation.lua",
        &["continuation", "nested-break", "repeat", "while"],
        "嵌套break不能遮蔽repeat或while各自的局部continuation。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/entry_07_adjacent_loop_state_handoff.lua",
        &["adjacent-loops", "metatable", "order", "state"],
        "相邻循环间共享状态必须按前一循环结束值交给后一循环。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_20_generic_for_short_break.lua",
        &["ast", "break", "generic-for", "short-circuit"],
        "generic-for中的短路条件应拥有break而不能被识别为循环continuation。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/tail_09_same_header_nested_loops.lua",
        &["continue", "numeric-for", "while"],
        "共享body header的外层numeric-for与内层while必须还原成两个嵌套循环。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/exit_04_degenerate_numeric_for_exit_pad.lua",
        &["break", "exit-pad", "nested-loop", "numeric-for"],
        "立即break的内层numeric-for退出pad必须归属于外层迭代body。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_24_numeric_for_control_pad.lua",
        &["generic-for", "numeric-for", "pad", "while"],
        "numeric-for控制pad与相邻generic-for/while分支不得错误互相吸收。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/break_07_nested_break_exit_pad.lua",
        &["break", "exit-pad", "generic-for", "while"],
        "while内嵌generic-for之后的break退出pad必须回到正确外层。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/repeat_08_nested_numeric_body.lua",
        &["numeric-for", "repeat", "while"],
        "repeat中的numeric-for入口不能被误判为相邻while退出。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_15_numeric_for_duplicated_return_state.lua",
        &["duplicated-exit", "numeric-for", "while"],
        "复制的return出口不能分裂numeric-for的唯一外层状态。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/repeat_09_short_condition_in_degenerate_generic_for.lua",
        &["generic-for", "repeat", "short-circuit"],
        "退化generic-for中的repeat短路条件及零迭代状态必须保持。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_14_repeat_degenerate_continue_branch.lua",
        &["degenerate", "generic-for", "repeat"],
        "repeat内等目标continue分支应归入循环尾而非生成goto。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/exit_05_loop_break_terminal_split.lua",
        &["break", "generic-for", "while"],
        "break终点同时分裂到循环后块和复制return时仍须保持一个终端状态。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/tail_10_degenerate_numeric_for_nested_while.lua",
        &["numeric-for", "unreachable-latch", "while"],
        "不可达numeric-for latch与内层while header共享节点时仍应保留两层循环。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_39_repeat_single_condition_and_generic_break.lua",
        &["all-opts", "continue", "generic-for", "repeat"],
        "单节点repeat条件、前缀continue和generic-for立即break三种退化边必须各自保持。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/exit_06_exit_loop_terminal_state.lua",
        &["break", "repeat", "terminal"],
        "repeat body与循环后块共享终端时多个break出口仍须保留x状态。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_15_luau_shared_continue_edge_owner.lua",
        &["continue", "numeric-for", "repeat", "while"],
        "间接continue pad应归属外层while而非内层repeat或numeric-for。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_25_luau_loop_exit_bounded_branch.lua",
        &["break", "continue", "generic-for", "while"],
        "局部break只能界定内层分支，不能把外层分支合流推到循环出口。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/break_08_repeat_header_break_pad.lua",
        &["break", "repeat", "while"],
        "repeat body的break pad不能被提升成外层while的post块。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/repeat_03_candidate_identity.lua",
        &["nested-loop", "phi", "repeat", "short-circuit"],
        "锁定 repeat 在内嵌 numeric-for 后仍消费同一完整短路条件候选，并把循环更新值直接作为返回值。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/tail_05_short_circuit_dag.lua",
        &["break", "repeat", "shared-node", "short-circuit"],
        "证明多前驱共享的条件节点仍属于 repeat 尾部短路 DAG，而不会被拆成残余跳转。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/repeat_04_shared_condition_break.lua",
        &["break", "repeat", "short-circuit"],
        "锁定 repeat 尾条件和 body 提前 break 共享 continuation 时仍恢复单个复合 until 条件。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/repeat_05_direct_break_condition_owner.lua",
        &["ast", "break", "condition-owner", "repeat"],
        "确认直接 body break 不会错误取得 repeat 尾条件的结构 owner。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_07_short_condition_body_backedge.lua",
        &["backedge", "short-circuit", "while"],
        "防止 while body 回边被误分类为 repeat 的尾部 pad，并保持复合 while 条件。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_08_for_cleanup_shared_continuation.lua",
        &[
            "cleanup",
            "early-return",
            "generic-for",
            "shared-continuation",
        ],
        "保证 generic-for 的隐式 Close pad 能归一到循环后的共享 continuation，而不产生残余跳转。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/repeat_06_refine_exit_phi_owner.lua",
        &["break", "live-out", "repeat", "while-true"],
        "同时固定 while-true 精化为 repeat 和原生 repeat 在多 break 出口处对同一 live-out phi 的所有权。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_09_loop_owner_exit.lua",
        &["generic-for", "goto", "normal-exit", "restart"],
        "保证外部 goto 重启穿过 generic-for 时，内层 owner 仍保留外层正常退出与 loop break 结构。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_52)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_10_repeat_nested_break_shared_fallthrough.lua",
        &["break", "nested-if", "repeat", "shared-tail"],
        "确认嵌套 if 的 break 不会把正常共享 fallthrough 错误并入外层分支。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/island_07_if_else_no_merge.lua",
        &["if-else", "infinite-loop", "postdominator", "terminal"],
        "固定一臂终止、一臂无限或两臂都无限时不存在可伪造的 postdom merge。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/entry_03_retry_terminal_state.lua",
        &["generic-for", "latch", "nested-loop", "repeat"],
        "固定 direct sibling latch 回到外层 header 时保留 done/round/count 的终态。",
        &[LuaCaseConfiguration::new(LUA_51_AND_LUAJIT)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_05_nested_loop_header_arm.lua",
        &["branch-arm", "early-return", "header", "nested-while"],
        "证明 branch arm 可直接进入唯一 nested-loop header，而不需残余跳转或机械局部。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_23_enclosing_loop_escape_fence.lua",
        &["break", "nested-branch", "single-pass", "while"],
        "防止外层 while 的两个 break 被误识别为 single-pass fence 的出口。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_11_lua55_degenerate_generic_shared_exit.lua",
        &["generic-for", "repeat", "shared-exit"],
        "固定 Lua5.5 generic-for 零次迭代出口与 body break 出口共享 continuation 时的结构恢复。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/tail_06_branch_shared_continuation_nearest.lua",
        &["branch", "goto", "layout", "postdominator"],
        "要求共享 continuation 按 CFG 距离选择 near，而非按物理布局先遇到 far。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_52)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_24_loop_nearest_merge.lua",
        &["goto", "infinite-loop", "postdominator", "structure-only"],
        "固定无限循环内分支同样按 CFG 近端选 merge。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_52)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/entry_04_loop_exit_state.lua",
        &["entry-header", "exit-phi", "nested-while", "repeat"],
        "保证 entry-header loop 为所有来源都在循环内的 exit phi 建立初值。",
        &[LuaCaseConfiguration::new(LUA_51_AND_LUAJIT)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_06_short_circuit_nonempty_continue_reentry.lua",
        &[
            "consumed-header",
            "continue-target",
            "short-circuit",
            "while",
        ],
        "防止非空 continue target 下多节点短路退化为重入已消费 header 的 plain if/else。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_25_repeat_condition.lua",
        &["continue", "repeat", "state-writeback"],
        "保证 Luau repeat 的 early continue 不丢尾条件状态写回。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/break_03_loop_break_soft_phi.lua",
        &["break", "effect-order", "phi", "repeat", "while"],
        "用三种循环分支族证明 effectful break 不把本轮 branch-value merge 推出循环。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_12_loop_body_scope_exit.lua",
        &["break", "generic-for", "numeric-for", "repeat"],
        "保证展开的嵌套 body 内部 core 出口不会制造跨 loop goto。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_26_generic_body_region.lua",
        &["body-prefix", "generic-for", "repeat", "shared-state"],
        "确认 branch 前缀与 nested repeat 同属退化 generic-for body 状态。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/repeat_07_short_body_scope_break.lua",
        &["break", "nested-loop", "repeat", "short-circuit"],
        "保证 repeat 短路 body 臂可进入内层 repeat 后再 break 外层。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_13_loop_break_shared_tail.lua",
        &["break", "repeat", "structure-only", "while"],
        "固定 active-loop break 与 sibling 路径共享 repeat tail 时的 owner。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_14_while_nested_loop_outer_break.lua",
        &["break", "nested-loop", "while"],
        "验证进入内层 while 后仍由 break 退出外层 natural loop。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_28_short_bvm_terminal_loop.lua",
        &["generic-for", "short-circuit", "terminal"],
        "防止 terminal guard 使短路 BVM 丢失本轮共享 tail。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_15_short_circuit_nested_break_tail.lua",
        &["break", "numeric-for", "short-circuit"],
        "证明双臂 branch 不是 same-header loop control，并保留共享尾。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_07_luau_continue_bvm_shared_tail.lua",
        &["continue", "numeric-for", "while"],
        "确保显式 continue 与 BVM 共享 tail 时分别归 numeric-for 和 while owner。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_08_luau_continue_nested_loop_tail.lua",
        &["continue", "nested-for", "shared-tail"],
        "保证 continue 前的嵌套循环 tail 由外层分支共享而不被吞掉。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_16_luau_numeric_for_early_continue_tail.lua",
        &["break", "continue", "numeric-for"],
        "防止 early continue 吞掉 numeric-for 外层共享 tail。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_30_luau_inlined_loop_stateful_exit.lua",
        &["inlining", "normal-exit", "o2"],
        "保证 O2 内联 loop 的 normal-only 出口不在 early return 前执行。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_06_lua51_short_while_break_shared_tail.lua",
        &["break", "short-circuit", "while"],
        "保证短路 while 的 early break 不抢占非空共享 tail。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_17_puc_nested_repeat_break_live_out.lua",
        &["break", "numeric-for", "repeat"],
        "验证 nested repeat 条件写回和 early break 共同决定 live-out。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_09_luau_continue_shared_break_tail.lua",
        &["continue", "repeat", "while"],
        "确保 if/elseif continue 不抢占 while/repeat 的共享 break tail。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_07_luau_decision_guard_mutation.lua",
        &["guard", "if-expression", "mutation"],
        "保证 decision 所选臂改变 guard 后不会误执行另一臂。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_31_lua51_loop_region_ownership.lua",
        &["else", "numeric-for", "short-circuit"],
        "防止短路if的else数值循环把退出边归给外层branch。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_18_lua51_nested_break_loop_owner.lua",
        &["break", "constant-guard", "while"],
        "保证内层恒真guard的break回边仍在loop containment内。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_08_connector_ownership.lua",
        &["call-order", "require", "short-circuit"],
        "固定条件connector对渠道/status/level短路调用的所有权。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_10_luau_nested_continue_owner.lua",
        &["numeric-for", "owner", "repeat"],
        "保证nested continue归内层for，同时不阻止外层repeat尾条件折叠。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/goto_01_direct_goto_parallel_assignment.lua",
        &["branch", "call", "parallel-assignment"],
        "要求direct goto壳恢复两臂call及平行value-pack而无残余跳转。",
        &[LuaCaseConfiguration::new(LUA_GOTO_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/goto_02_terminal_else_single_goto.lua",
        &["cycle", "fallback", "terminal-else"],
        "允许单个fallback goto恢复为terminal else arm。",
        &[LuaCaseConfiguration::new(&[
            LuaCaseDialect::Lua54,
            LuaCaseDialect::Lua55,
            LuaCaseDialect::Luajit,
        ])],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_11_repeat_nested_continue_owner.lua",
        &["numeric-for", "owner", "repeat"],
        "保证内层for continue不跳过外层repeat尾条件owner。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/goto_03_repeat_closed_goto_owner.lua",
        &["closed-graph", "repeat", "tail"],
        "保证封闭goto子图不绕过repeat tail。",
        &[LuaCaseConfiguration::new(LUA_GOTO_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_10_repeat_prefix_decision.lua",
        &["nested-loop", "prefix", "repeat"],
        "证明未触碰prefix Decision不拥有repeat tail。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_11_path_condition_clean_islands.lua",
        &["goto", "island", "label", "path-fact"],
        "保留 clean prefix/arm/run 与唯一 label predecessor 后的原条件，路径事实不授权删除检查。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_52).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/break_04_constant_if_loop_control.lua",
        &["constant-if", "owner", "while"],
        "保证移除恒真if后所选break仍归原while。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_12_luau_constant_if_continue.lua",
        &["constant-if", "owner", "while"],
        "保证移除恒真if后所选continue仍归原while。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_O0_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/tail_07_single_pass_empty_continuation.lua",
        &["break", "cleanup", "single-pass"],
        "允许cleanup后两条fallthrough臂无共享tail时移除single-pass repeat。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_10_nested_terminal_fallback_return.lua",
        &["empty-return", "nested-if", "terminal"],
        "保证显式空return关闭nested terminal guard，使selected body可提升。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_11_guarded_local_return_shell.lua",
        &["false-path", "guarded-local", "shell"],
        "保证结构化return壳终结guarded local的false path。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/goto_04_nested_goto_parallel_assignment.lua",
        &["event-order", "fallback", "goto", "parallel-assignment"],
        "验证嵌套goto恢复为互斥分支时整组并行返回值只在选中路径求值一次。",
        &[LuaCaseConfiguration::new(LUA_GOTO_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_12_naturalize_unbounded.lua",
        &["boolean-chain", "truthiness", "unbounded"],
        "验证超过固定小阈值的18臂and/or决策链仍能整体自然化。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_13_environment_partition.lua",
        &["boolean-chain", "environment", "partition"],
        "验证共享a条件但环境不同的内外决策区仍恢复为嵌套布尔表达式。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_13_luau_repeat_continue_scope_latch.lua",
        &["closure-scope", "condition-order", "continue"],
        "固定 Luau repeat 的 continue 先退出嵌套 closure 作用域，再从非稳定 if-expression condition 的正确 latch 边求值；第一轮必须调用 selected，不能走 fallback。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_O0_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_14_shell_flow_old_values.lua",
        &["backedge", "closure-cell", "coroutine", "goto"],
        "系统覆盖 boolean shell 删除所需旧值事实：前向跨 goto、资源回边、双入口循环、并行 closure observer、删除后的 occurrence 路径、无出口协程读取及 relay 捕获。",
        &[LuaCaseConfiguration::new(&[
            LuaCaseDialect::Lua52,
            LuaCaseDialect::Lua53,
            LuaCaseDialect::Lua54,
            LuaCaseDialect::Lua55,
        ])],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_19_flow_paths.lua",
        &["loop", "multi-return", "parallel-assignment", "writeback"],
        "覆盖 branch 早退、并行旧值、numeric/repeat break、generic-for factory与早退、repeat latch 五类 writeback flow，区分初始化、回边和终止读取。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55])
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_12_return_identity.lua",
        &["branch-fold", "evaluation-count", "return"],
        "证明无cleanup身份的相等return分支可合并，同时 effectful predicate 仍须恰好求值一次。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_33_cleanup_label.lua",
        &["break", "close-binding", "goto", "numeric-for"],
        "固定numeric-for continue式goto必须先关闭inner资源再到latch，break则关闭inner后退出，outer只在循环后关闭。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/island_08_cleanup_order.lua",
        &["close-binding", "exit-pad", "goto", "repeat"],
        "比较nested repeat正常condition路径与goto outside路径，防止退出pad标签插入已关闭资源仍被当作活跃的正常岛。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_34_loop_iteration_branch_join.lua",
        &["break", "postdom", "repeat", "while"],
        "证明下一迭代postdom不是当前迭代分支join，嵌套repeat、break与后续while必须恢复为结构化循环而非goto标签。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_20_incoming_edge_identity.lua",
        &["entry-edge", "parallel-edge", "phi", "while"],
        "区分while phi的函数entry输入与经过空if形成的并行物理边，避免按块身份合并不同incoming slot。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/entry_05_copy_root_entry_epoch.lua",
        &["backedge", "copy", "entry", "goto"],
        "回边重入首块时reset初始化不是后方copy producer支配的覆盖端点。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_52),
            LuaCaseConfiguration::new(PUC_LUA_GE_52).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/ownership_21_alias_control_flow.lua",
        &["break", "nested-loop", "parameter", "return"],
        "参数alias跨8层numeric-for、双loop break/return、repeat latch和while early return只收集一次CFG事实。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/entry_06_nil_nested_flow.lua",
        &["gc", "lookup-count", "nested-loop", "nil"],
        "entry nil跨8层loop与分支保持证明，同时非nil后显式清零不能被当冗余copy。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_15_luau_alternative_read_sources.lua",
        &["alternative", "lookup-count", "scratch"],
        "互斥同形GETTABLE可合并，scratch不同则必须保留if。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LuaCaseOptions {
                luau_optimization_level: Some(0),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_13_nested_identical_read_returns.lua",
        &[
            "evaluation-count",
            "lookup",
            "return-merge",
            "return-frame",
            "truthiness",
        ],
        "相同读取返回仅执行一次；同槽提前返回恢复完整表达式，nil/false叶保留选择语义与返回数量。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LuaCaseOptions {
                luau_optimization_level: Some(0),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_35_numeric_for_conversion.lua",
        &["coercion", "evaluation-order", "numeric-for", "pcall"],
        "数值for的字符串初值/上界/步长转换覆盖正向、反向与非法步长，并固定三个header表达式的求值顺序。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                })
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_16_preserved_nil_branch_orientation.lua",
        &["condition", "metamethod", "nil-guard", "short-circuit"],
        "两项nil guard的否定合取必须保持or短路方向，避免条件规约改变全局查找次数。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_17_evaluation_entry.lua",
        &["comparison", "evaluation-order", "gc", "numeric-for"],
        "七种if条件操作数在跳过数值for及scope释放之后求值，覆盖嵌套call、全局、四类比较、参数和table key的entry准备。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/exit_02_loop_private_exit_results.lua",
        &["break", "coroutine", "shared-suffix", "while"],
        "协程私有退出、公共后缀、零次迭代与提前 break 的结果和声明可读性。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/exit_03_loop_private_exit_scope.lua",
        &["close-binding", "goto", "shared-suffix", "while"],
        "私有break离开迭代close scope时先执行__close再进入公共后缀，并对照外部goto从零次/循环内进入共享标签。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/return_14_return_decision_result_home.lua",
        &["decision", "metamethod", "snapshot", "while"],
        "循环后Decision继续更新原result home，同时带旧值快照的条件赋值不得误授予新旧值共址。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/break_05_nested_repeat_break_condition.lua",
        &["break", "repeat", "short-circuit", "while"],
        "内层repeat的两处break都必须跳过until条件，外层有限while使任何多余__index读取可精确观察。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_18_nested_exit_condition_owner.lua",
        &["break", "nested-repeat", "while"],
        "两层repeat共享入口和外层while latch时，内层出口仍属于内层条件，不能提前归为祖先continue。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_36_shared_repeat_body_branch.lua",
        &["branch", "break", "nested-repeat"],
        "内层入口两臂都应留在内层，break pad与正常完成先进入外层尾条件。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_19_shared_repeat_short_exit.lua",
        &["break", "exhaustive", "nested-repeat", "short-circuit"],
        "共享入口的所有内层出口先汇入外层短路尾条件，完整枚举a/b/c/d四布尔量防止末叶归属错误。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_40_flow.lua",
        &["break", "if", "numeric-for", "while"],
        "九组基础控制流覆盖提前return、while/for、嵌套break、分支phi、call条件、参数重赋值和目标搜索。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/repeat_10_until.lua",
        &["break", "closure", "repeat", "while"],
        "五组repeat覆盖基础尾条件、表索引条件、循环内capture、break值流及与while交错的闭包cell。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/loop_41_for.lua",
        &["break", "closure", "generic-for", "ipairs"],
        "基础ipairs协议、循环内break closure和迭代时三路table读取的早return。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_21_regression.lua",
        &["degenerate-guard", "inline", "short-circuit", "side-effect"],
        "收纳共享主语、相邻sink、自赋值壳、副作用or和退化TEST guard五类已知布尔恢复回归。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_22_conditions.lua",
        &[
            "capture",
            "loop-exit",
            "path-condition",
            "write-invalidation",
        ],
        "七组路径事实覆盖参数写失效、闭包改写、truthy原值、effectful条件、可变字段、析取事实及break退出。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/goto_05_loop_lexical_arms.lua",
        &["return", "scope", "sibling-loop", "while"],
        "while中的纯return arm保持词法归属，闭合后继while不得被收进前一个loop body。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/exit_07_loop_exit_observations.lua",
        &["break", "exhaustive", "nested-repeat", "oracle"],
        "内外repeat的break、尾条件事件与外层while回边状态以early/inner/stop三布尔量完整组合验证。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/goto_06_goto.lua",
        &["goto", "irreducible", "label", "path-condition"],
        "五组goto覆盖回边、模拟break/continue、不可规约网格和label合流后的路径事实失效。",
        &[LuaCaseConfiguration::new(LUA_GOTO_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/continue_16_loop_continue_actions.lua",
        &["continue", "oracle", "repeat"],
        "while continue跳入口而repeat continue仍执行尾条件，并覆盖可由O0/O1还原if与O2必须保留continue的差异。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_23_stale_transfer_requirement.lua",
        &["path-condition", "short-circuit", "exit-requirement"],
        "HIR 删除矛盾分支后退役过期 goto 要求，Lua 5.1 Strict 仍生成可执行源码。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_51),
            LuaCaseConfiguration::new(PUC_LUA_51).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_24_nested_branch_escape.lua",
        &["early-return", "short-circuit", "forward-guard"],
        "嵌套前导退出折入外层条件，八种布尔组合保留返回值与后继分支。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_51),
            LuaCaseConfiguration::new(PUC_LUA_51).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_control_flow/branch_25_alternative_guard_routes.lua",
        &["short-circuit", "forward-guard", "shared-tail"],
        "交替成功与失败 guard 保留条件选择及共同尾部的一次执行。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_51),
            LuaCaseConfiguration::new(PUC_LUA_51).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
];
