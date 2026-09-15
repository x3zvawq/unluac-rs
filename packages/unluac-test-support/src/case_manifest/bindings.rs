//! bindings 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;
pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_01_repeat_inner_ref.lua",
        &["repeat", "scope", "short-circuit"],
        "证明 repeat 体内声明的 a、b 在 until 条件中仍可见，并保持两个局部计算参与短路退出。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/phi_01_goto_loop_phi_seed.lua",
        &["entry-state", "goto", "loop", "phi"],
        "证明 goto 首次进入 label 的 i=0 初值不能被回边 i+1 快照覆盖。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_53)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_02_capture_range.lua",
        &["closure-capture", "loadnil"],
        "固定 Lua 5.2/5.3 LOADNIL 从 A 起算的范围，使尾部 d、e 两个 nil local 均进入表与闭包捕获。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_52)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/phi_02_branch_into_loop_header_phi.lua",
        &["branch-entry", "phi", "repeat"],
        "证明 if 外部臂写入与 repeat 回边共同拥有 header phi，初次进入时保留分支后的 x。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_01_luau_repeat_condition_entry_state.lua",
        &["generic-for", "repeat"],
        "使短路 until 条件入口保留局部 tail 的 loop state owner。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/assignment_01_luau_branch_mixed_entry_update_owner.lua",
        &["branch", "bvm"],
        "使 BVM 合流中的 preserved 与 update 两类入口继承正确 state owner。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/phi_03_luau_loop_break_header_phi_owner.lua",
        &["break", "phi"],
        "让 nested break 分支的入口 phi 继承 active loop state owner，而不错误合并短路条件。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_02_loop_state.lua",
        &["capture", "parameter", "snapshot"],
        "同时保护循环参数入口状态、循环前 value 快照和被闭包捕获参数不被可变 state 覆盖。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/alias_01_luajit_prior_handoff_target.lua",
        &["handoff", "repeat", "state-machine"],
        "前置分支写过的临时槽不能被误认作后续 handoff target。",
        &[LuaCaseConfiguration::new(LUAJIT_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_03_multi_exit_downstream_value_merge.lua",
        &["break", "live-out", "phi"],
        "两个 break pad 的共同下游 merge 必须读取同一个 loop live-out x。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_04_parameter_entry_value.lua",
        &["numeric-for", "parameter"],
        "空 outside-def 集合仍应从函数参数 n 为 loop header 提供入口值。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_03_lua55_generic_for_binding_scope.lua",
        &["binding", "close", "generic-for"],
        "自动关闭迭代器的物理出口不能扩张index/value词法域。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_05_outer_for_binding_inner_loops.lua",
        &["generic-for", "repeat", "while"],
        "内层while/repeat写回外层generic-for binding时保持同一可变local。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_06_numeric_for_binding_inner_loop.lua",
        &["mutable-binding", "numeric-for", "while"],
        "同header内层while复用可写numeric-for binding owner而不产生copy。",
        &[LuaCaseConfiguration::new(
            MUTABLE_NUMERIC_FOR_BINDING_DIALECTS,
        )],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/debug_01_global_name_binding_shadow.lua",
        &["capture", "method"],
        "debug重命名不能让参数print/self遮蔽同函数全局引用，父binding改名还需沿capture传播。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_52).with_options(LuaCaseOptions {
                retain_debug: true,
                naming_mode: Some(NamingMode::Simple),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_07_lua55_generic_for_live_out.lua",
        &["close", "generic-for", "live-out"],
        "break与正常cleanup共同后继须持有left/right双live-out。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_08_generic_for_branch_phi.lua",
        &["generic-for", "method-call", "phi"],
        "generic-for body的局部分支phi归本轮soft merge，不伪造continue。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_09_repeat_live_out.lua",
        &["live-out", "multivalue", "repeat"],
        "repeat内i/min/max更新在退出后仍沿同一binding。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_10_short_circuit_repeat_state_init.lua",
        &["repeat", "short-circuit", "state"],
        "branch value初始化覆盖每个repeat入口。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_11_numeric_for_short_circuit_assignment.lua",
        &["numeric-for", "short-circuit", "state"],
        "loop owner保留每轮short-circuit写flag。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_12_repeat_short_circuit_state.lua",
        &["repeat", "short-circuit", "state"],
        "已发射state更新不能再次内联。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_14_lua51_retry_loop_live_out.lua",
        &["generic-for", "live-out", "while"],
        "retry while保持choice为loop内定义的live-out。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_18_multi_entry_loop_state.lua",
        &["multi-entry", "while"],
        "多入口while复用index共同初值。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/alias_08_nil_fallback_alias.lua",
        &["function", "global", "nil"],
        "nil fallback将b绑定env而不恢复else/or，并由函数引用同一alias。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/phi_05_state_and_short_prefix_escape.lua",
        &["field-write", "loop", "snapshot"],
        "branch state初值物化，RHS期间mode由loop保活且target跨轮。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/phi_06_conditional_reassign_multi_phi.lua",
        &["branch", "multivalue"],
        "条件重赋不能拆开a/b/cond同分支多输出phi。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_22_exit_state_preheader.lua",
        &["break", "generic-for", "preheader"],
        "只在exit写的found/value初值来自preheader。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/phi_07_shared_fallback_value_merge.lua",
        &["branch", "fallback", "runtime", "shared-tail"],
        "两个条件分支共享fallback时应合并为同一最终值而不串错路径。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/assignment_05_global_and_return_alias.lua",
        &["alias", "global-write", "multiret", "runtime"],
        "多返回值同时流向全局写入与返回别名时各槽身份不能交换。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/phi_08_preserved_value_guard.lua",
        &["alignment", "branch", "phi", "preserved-value"],
        "嵌套guard必须保留默认对齐值，并只在对应分支替换。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/assignment_06_branch_update_used_after_if.lua",
        &["nested-if", "pipeline", "reassignment", "return"],
        "decrypt与inflate逐步覆写的值必须在分支后传给decode。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/assignment_07_multi_value_merge_defer_to_bvm.lua",
        &["branch", "phi", "short-circuit", "two-values"],
        "条件分支同时更新offset与scale时两值须作为同一合流候选。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_28_branch_owns_nested_loop_exit_phi.lua",
        &["branch", "phi", "shared-tail", "while"],
        "外层分支应拥有嵌套while退出后的result合流。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/phi_09_bvm_priority.lua",
        &["branch-value", "priority", "short-circuit", "side-effect"],
        "等规模候选竞争时guard自身分支值应优先且短路不调用touch。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_29_branch_owned_multi_entry_loop_state.lua",
        &["branch", "numeric-for", "repeat"],
        "分支目标必须拥有嵌套repeat的多入口状态并继承前置for累积值。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_30_numeric_for_continue_pad_state.lua",
        &["carried-state", "numeric-for", "repeat"],
        "numeric-for尾部continue pad必须留在body内且外层repeat状态保持可写。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/phi_10_short_circuit_shared_return_value.lua",
        &["numeric-for", "shared-tail", "short-circuit"],
        "终端真分支之后显式共享return值和前缀必须保留。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/phi_11_nested_loop_branch_state_seed.lua",
        &["generic-for", "phi", "repeat"],
        "嵌套循环分支seed必须复用外层x而不能读取未物化header phi。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/environment_01_multiret_global_write_order.lua",
        &[
            "assignment-order",
            "environment",
            "metamethod",
            "multi-return",
        ],
        "用环境代理的 __newindex 顺序观察两个多返回局部写入不同全局时不得逆序合并。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/assignment_02_ast_inline_ordered_snapshot.lua",
        &["alias", "callee-order", "parameter-write", "snapshot"],
        "证明 binding alias 在定义点保留旧值，而副作用结果的别名链可转发且不得改变参数写后的新值。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/identity_01_short_circuit_subject_ownership.lua",
        &[
            "capture-write",
            "global-callee",
            "metamethod",
            "receiver-snapshot",
        ],
        "以六个子例覆盖 single-eval subject 的 receiver、局部、参数、upvalue、全局 callee 与未用元方法结果的所有权。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/environment_02_env_snapshot_identity.lua",
        &["environment", "global", "rebinding", "snapshot"],
        "保证保存的旧 _ENV 在重绑定后仍以表索引访问，不能改写为当前环境的 global。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_52)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_13_tail_temp_inline.lua",
        &["index", "repeat", "self-update", "temp-inline"],
        "区分可内联的 repeat 尾条件索引 temp 与不可删除的自更新状态。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/phi_04_branch_value_mutable_source_snapshot.lua",
        &[
            "branch-value",
            "generic-for",
            "mutable-binding",
            "numeric-for",
        ],
        "验证允许改写循环 binding 的方言中 branch value 读取臂内新值。",
        &[LuaCaseConfiguration::new(
            MUTABLE_NUMERIC_FOR_BINDING_DIALECTS,
        )],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/inline_01_temp_live_use_boundaries.lua",
        &["generic-for", "overwrite", "repeat", "temp-inline"],
        "覆盖 proto 级 live-use 在 repeat、generic-for 和同块覆盖写三类结构边界。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/alias_02_boundary_alias_snapshot.lua",
        &["alias", "goto", "snapshot", "state-update"],
        "保证跨 goto 边界、跨 value 更新时点的 snapshot/copied 不被合成同一状态。",
        &[LuaCaseConfiguration::new(LUA_GOTO_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_15_luau_numeric_for_multi_read_binding.lua",
        &[
            "boolean",
            "capture",
            "continue",
            "convergence",
            "numeric-for",
            "source-frame",
        ],
        "复用同一for binding，且O2展开后的Boolean预写不增加声明与后继callee副本。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LuaCaseOptions {
                recompile_rounds: Some(4),
                ..LUAU_OPTIMIZED_OPTIONS
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_16_luau_loop_carried_binding.lua",
        &["initializer", "phi", "return-frame", "state", "while"],
        "并行常量 seed 建立同槽循环绑定；观察零轮、两种步长、truthiness 和固定双返回，保留原高返回区。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/debug_02_names_all_dialects.lua",
        &["debug", "loop-binding", "naming-modes", "nested-function"],
        "保证所有 naming mode 优先采用跨方言 debug binding。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)
            .with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            })
            .with_variants(ALL_NAMING_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/assignment_03_repeat_exit_parallel_snapshot.lua",
        &["capture", "parallel-assignment", "repeat", "snapshot"],
        "保证 repeat 正常/提前退出保留平行赋值 RHS 与跨pad state快照。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/alias_03_block_direct_snapshot.lua",
        &["break", "carried-temp", "overwrite", "repeat"],
        "保证跨块 exit copy 保留 carried temp 覆写前快照。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/cleanup_01_branch_value_terminal_sink.lua",
        &["branch-value", "equality", "local-cleanup", "temp"],
        "要求 branch value 暴露的终结temp在locals前收回。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/environment_03_decl_debug.lua",
        &["debug", "global-decl", "local-identity"],
        "保证只向global传值的debug-hinted source local仍可反射观察。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_55).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/alias_04_loop_branch_state_copy.lua",
        &["generic-for", "numeric-for", "repeat", "while"],
        "证明branch state copy覆盖所有回边及捕获写后的入口关系。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/alias_05_value_flow.lua",
        &["first-read", "loop", "promotion", "repeat"],
        "保证locals promotion不吞loop头状态或首次写前读取，until按身份读取循环体内声明的条件binding。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/debug_03_branch_control_debug.lua",
        &["local-identity", "unreachable"],
        "保证branch-control不以运行不可达删除debug承载的local身份。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_04_statement_merge_debug_scope.lua",
        &["debug", "local", "statement-merge"],
        "保证顺序local逐个进入debug可见域，后续元方法和line hook能观察声明间隙。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_05_boolean_shell_lexical_scope.lua",
        &["boolean-shell", "initializer", "shadowing"],
        "禁止boolean shell把local声明跨过读取同名local的initializer。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_06_boolean_shell_local_scope.lua",
        &["boolean-shell", "debug", "local-visibility"],
        "保证condition求值前local result已进入可反射作用域。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_07_generic_for_iterator_debug_scope.lua",
        &["debug", "generic-for", "iterator-pack"],
        "保证source iterator/state/control locals在隐式迭代调用时仍具debug作用域身份。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_17_generic_for_iterator_live_out.lua",
        &["control", "generic-for", "iterator", "state"],
        "保证循环后仍读取的iterator producer及其nil pack不被删除。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/cleanup_02_temp_entry_nil.lua",
        &["entry-nil", "sibling", "while"],
        "删除已证entry-nil死写；原帧占位仅去掉无读布尔值，保留nil声明与循环后的活值。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/alias_06_param_alias_generic_iterator_callback.lua",
        &["callback", "generic-for", "parameter"],
        "保证generic-for隐式iterator调用参与参数alias flow。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_08_extended_call_debug_scope.lua",
        &["call", "debug", "local"],
        "保证extended call run保留可由callee反射观察的inspector与argument源码local。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/alias_07_mechanical_loop_condition_snapshot.lua",
        &["condition", "repeat", "while"],
        "防止mechanical alias run把定义点快照移入循环条件并重读变异源。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/inline_02_temp_inline_nested_regions.lua",
        &["call", "conditional", "constructor", "lookup"],
        "区分必达nested producer可收回与条件区/table allocation producer必须保留。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_19_numeric_for_stable_binding_source.lua",
        &["error", "gc-root", "numeric-for", "parameter", "source"],
        "以PUC异常退出和LuaJIT字段查找时额外实参的GC观察约束原帧，Luau保留直接参数循环初值。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/alias_09_loop_invariant_rhs.lua",
        &[
            "boolean",
            "gc-root",
            "invariant",
            "parameter-copy",
            "repeat",
            "while",
        ],
        "保持循环入口参数副本的原高槽及前缀；返回后 caller 覆写低槽时仍保根，并对照折叠候选的不同 GC 观察。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/cleanup_03_unused_initialized_local_prefix.lua",
        &["dead-local", "multi-return", "prefix"],
        "保证清理未使用的首槽不会把第二返回值左移到错误binding。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/cleanup_04_unused_initialized_local_suffix.lua",
        &["dead-local", "multi-return", "suffix"],
        "保证清理仅删除已初始化的尾部死槽而保留首值。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_09_statement_merge_local_attrs.lua",
        &["close", "debug", "statement-merge"],
        "约束带属性local的声明合并：debug来源不合并、Close顺序不改变。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/alias_10_stable_copy_same_stmt_multi_use.lua",
        &[
            "alias",
            "call",
            "gc-root",
            "multi-use",
            "return-frame",
            "tail-call",
        ],
        "观察返回/尾调用原高槽 COPY 的残根；同值实参仍保留原帧前缀，跨 statement 保持身份。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/alias_11_stable_copy_multi_stmt.lua",
        &["alias", "call", "return"],
        "区分caller前缀alias必须保留与RETURN连续结果区机械副本可回收。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/alias_12_stable_copy_eventless_snapshot.lua",
        &[
            "copy-chain",
            "gc-root",
            "handoff",
            "metamethod",
            "scope",
            "scratch",
            "truthiness",
        ],
        "约束 truthiness、写依赖与交接；保留参数/COPY 身份及分配前缀，观察相邻 scratch 的保活与覆盖边界。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_10_repeat_condition_binding_use.lua",
        &["body-local", "condition", "gc", "repeat", "root-retirement"],
        "保证until与repeat body共享local value作用域，完整条件调用准备退休前次方法残根。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/debug_04_tail_debug_scope.lua",
        &["close", "debug", "tail-scope"],
        "验证尾部内层local的debug区间在函数return或外层close之前已经结束。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54]).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_20_lua55_repeat_global_scope.lua",
        &["condition", "global", "repeat"],
        "验证repeat体内local延伸到until条件，同时缺失global声明能按最小集合恢复。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/inline_03_statement_merge_inline_owner.lua",
        &[
            "gc-root",
            "inline",
            "local-owner",
            "multi-return",
            "return-frame",
        ],
        "保留单次/重复返回的两个原输入 binding，完整返回帧直接复用其值，避免额外三元局部搬运。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/identity_02_target_reads.lua",
        &["alias", "function-sugar", "lvalue", "method"],
        "固定 function alias.field、function alias:method 与 function alias.nested.field 三类函数糖都保留 target base 的读取，使条件选择的 alias 后续能正确消除且写到选中对象。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/identity_03_ast_binding_identity.lua",
        &["capture", "debug", "gc-root", "iife"],
        "区分HIR capture binding与AST为IIFE installer创建的binding，三个installer及nested closure不能互串token/remembered/count/captured身份。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/cleanup_05_move_facts.lua",
        &["move", "multi-return", "precompute", "unreachable"],
        "固定return后的不可达Move即使无SSA use也不能使整个函数的预计算值根证明失败。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/parameter_01_visibility_intervals.lua",
        &["closure", "naming", "parameter", "shadow"],
        "在Simple命名下覆盖父参数避让、兄弟/退出scope不污染后续定义点、递归local、numeric/generic loop捕获及repeat condition闭包参数。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                naming_mode: Some(NamingMode::Simple),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                naming_mode: Some(NamingMode::Simple),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/parameter_02_binding_identity.lua",
        &["capture", "parameter", "rebind", "shadow"],
        "覆盖参数value经numeric-for写回、闭包捕获后再写、内层同名遮蔽、if phi重绑及提前nil后两闭包读取，要求源参数身份贯穿这些窗口。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_21_binding_decision.lua",
        &["decision", "generic-for", "writeback"],
        "三个generic-for分别让binding经函数调用替换、truthy决策替换与普通加法/条件乘法写回，要求决策叶和合并写都指向loop binding而非SSA temp。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_11_sink_write_scope.lua",
        &["generic-for", "global-write", "repeat", "scope"],
        "让generic-for binding在repeat两路径写回，检查声明下沉到一分支后仍覆盖兄弟suffix，不能生成全局写。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_12_plain_table_scope.lua",
        &["debug", "getlocal", "initializer", "metatable"],
        "表initializer求值时ids尚不可见；初始化后visible必须可被patch通过debug.getlocal找到并安装元表，不能持续视为plain table。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/assignment_04_assignment_commit.lua",
        &["capture", "if-expression", "trace"],
        "Decision终端可直接写current cell，但中间逻辑叶完成前不得提前写回。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY),
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_23_luau_numeric_for_debug_phi.lua",
        &["convergence", "debug", "numeric-for"],
        "numeric-for语法binding提供phi，但SETLIST buffer COPY及真实body写/旧快照仍保留。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_options(LuaCaseOptions {
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                })
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                })
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_24_numeric_for_writable_header.lua",
        &["assignment", "dialect", "loop-index", "numeric-for"],
        "允许写数值for索引的方言中，body内i=100不得改变隐式控制变量的下一次迭代。",
        &[
            LuaCaseConfiguration::new(MUTABLE_NUMERIC_FOR_BINDING_DIALECTS),
            LuaCaseConfiguration::new(MUTABLE_NUMERIC_FOR_BINDING_DIALECTS).with_options(
                LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                },
            ),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(&[LuaCaseVariant::LuauO0, LuaCaseVariant::LuauO2]),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                })
                .with_variants(&[LuaCaseVariant::LuauO0, LuaCaseVariant::LuauO2]),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_13_debug_phi_lexical_window.lua",
        &["debug-info", "phi", "scope"],
        "两个顺序debug局部的phi窗口不得重叠，闭包捕获应指向各自词法对象，窗口后next绑定恢复为3。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)
            .with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            })
            .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_25_numeric_for_step_normal_state.lua",
        &["debug", "numeric-for", "step", "version"],
        "循环step槽在正常迭代结束后的存活状态按PUC版本分化，防止统一套用Lua54/55或旧版本规则。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_26_luajit_for_init_binding_state.lua",
        &["binding", "gc", "numeric-for"],
        "LuaJIT数值for初值对象在正常、跳过及带prefix路径中都不应被循环初始化binding残留保活。",
        &[
            LuaCaseConfiguration::new(LUAJIT_ONLY),
            LuaCaseConfiguration::new(LUAJIT_ONLY).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/loop_27_for_loop_binding_exit_state.lua",
        &["gc", "loop-binding", "numeric-for", "scope-exit"],
        "PUC Lua51-54中数值for展示binding对象在循环退出后仍保持可达，固定与init/step临时槽不同的生命周期。",
        &[
            LuaCaseConfiguration::new(&[
                LuaCaseDialect::Lua51,
                LuaCaseDialect::Lua52,
                LuaCaseDialect::Lua53,
                LuaCaseDialect::Lua54,
            ]),
            LuaCaseConfiguration::new(&[
                LuaCaseDialect::Lua51,
                LuaCaseDialect::Lua52,
                LuaCaseDialect::Lua53,
                LuaCaseDialect::Lua54,
            ])
            .with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_14_basics.lua",
        &["alias", "multi-assignment", "numeric-for", "shadowing"],
        "基础矩阵同时覆盖多赋值初始化、do遮蔽、表alias写、嵌套遮蔽返回及for header快照。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/environment_04_lua51_legacy_environment.lua",
        &["closure", "module", "setfenv"],
        "Lua5.1基础套件覆盖setfenv函数环境、module/package.seeall及嵌套闭包的独立环境与词法capture。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/environment_05_env.lua",
        &["closure", "env", "shadowing"],
        "Lua5.2+的_ENV重定向和内外_ENV遮蔽下，词法prefix与环境value分别解析到正确来源。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_52).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/scope_15_const.lua",
        &["closure", "const", "vararg"],
        "const局部、嵌套closure capture和变参管线中的只读binding在循环与返回中保持正确值。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_bindings/environment_06_global.lua",
        &["const-gate", "function-declaration", "global"],
        "Lua5.5 global声明、global function capture及global<const>*门控在局部scope中正确解析。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
];
