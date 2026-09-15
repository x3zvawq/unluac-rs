//! stress 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;
pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_stress/controlflow_01_luau_repeat_shared_nested_loop_tail.lua",
        &["continue", "nested-loop", "repeat"],
        "在多层 for/while/repeat 压力图中保持外层 repeat 分支与嵌套 for 的共享 tail。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/controlflow_02_luau_numeric_for_shared_nested_preheader.lua",
        &["continue", "nested-loop", "numeric-for"],
        "保护 numeric-for 内层 while 的共享 preheader 在 early continue 之前归属正确。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/constants_01_luajit_wide_compare_operand.lua",
        &["compare", "generated-pressure", "wide-constant"],
        "把 compare 的 target 常量推到 16-bit D 索引边界，并防止错误使用 padding-005。",
        &[LuaCaseConfiguration::new(LUAJIT_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/constants_02_lua54_wide_env_upvalue.lua",
        &["env", "upvalue", "wide-constant"],
        "256常量压力下全局读写经GETUPVAL仍恢复裸global，并在替换_ENV后区分新旧环境。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/constants_03_lua55_wide_global_decl.lua",
        &["global-decl", "wide-constant"],
        "256常量压力下环境访问仍与ERRNNIL配对恢复global声明。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/locals_01_local_scope_limit.lua",
        &["iife", "scope-limit"],
        "101个顺序IIFE迫使机械local分段释放，生成源码仍可编译。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/locals_02_nested_local_scope_budget.lua",
        &["budget", "fastcall", "nested-scope"],
        "嵌套block扣除35个外层活跃local，后置35个local又不能倒灌早期预算。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/locals_03_luau_home_slot_compaction.lua",
        &["bit32", "home-slot"],
        "64次旋转异或链按home复用local，避免stripped源码槽膨胀。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/controlflow_03_decision_naturalize_budget.lua",
        &["budget", "short-circuit", "wide-chain"],
        "40组and/or宽链保持表达式且最早truthy值优先。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/calls_02_method_alias_wide_call_args.lua",
        &["closure", "method-alias", "wide-call"],
        "70个点号SELF调用跨过宽参数寄存器边界时不得误还原成冒号调用。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/expressions_01_short_circuit_chain.lua",
        &["ast-depth", "fixed-point", "line-length", "short-circuit"],
        "以 160 项 or 值链和条件链压测 fixed-point 传播与生成器栈深，并要求一次可读地收敛。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/controlflow_04_home_slot_local_limit.lua",
        &["home-slot", "metamethod", "phi", "wide-cfg"],
        "用200个顺序条件证明 branch phi 复用状态 binding，不随条件数累积 scratch local。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/expressions_02_long_logical_ast_depth.lua",
        &["call-count", "logical-chain", "stack-depth"],
        "以1280项调用链验证 AST build 不递归耗尽栈且短路停在尾值。",
        &[LuaCaseConfiguration::new(PUC_LUA_54).with_options(NO_RECOMPILE_STRESS_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/locals_04_large_ssa_scope_identity.lua",
        &["local-scope", "method-call", "physical-slot", "ssa"],
        "证明大量SSA定义不等于源码local压力且不同作用域身份不能按物理槽合并。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/depth_01_luau_deep_proto_chain.lua",
        &["nesting", "proto", "stack-depth"],
        "验证300层词法proto贯穿编译、反编译和AST流水线。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/roots_01_local_scope_physical_root.lua",
        &["gc", "local-budget", "physical-root"],
        "以181个IIFE制造local预算分段，保证不缩短root生命周期。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/constants_04_lua55_wide_mixed_global_rhs.lua",
        &["environment", "global", "wide-constants"],
        "以260个常量制造宽leading target，拒绝直接抽取tail_b/tail_c后缀。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])
            .with_expectation(LuaCaseExpectation::GlobalDeclResidual)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/locals_05_lua55_local_scope_crosses_global_decl.lua",
        &["global", "recursion", "scope", "wide-params"],
        "在145参数与40段local/global交替压力下保持后继CALL原声明前缀，避免为软预算提前缩域。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/controlflow_05_scope_pressure.lua",
        &["goto", "local-limit", "repetition", "scope"],
        "用33个独立、同构的不可规约 do 区域迫使旧实现若把每段 SSA carrier 空声明累积到函数入口便超过 Lua 200 活跃 local 限制，同时每段只复用一个 n。",
        &[LuaCaseConfiguration::new(LUA_GOTO_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/closures_01_nested_closure_bodies.lua",
        &["calls", "depth", "nested-closure", "stack"],
        "构造64层逐级返回的新闭包，要求AST build不按proto深度递归到栈溢出，并保留每层真实print与下一闭包。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/controlflow_06_pure_condition_chain.lua",
        &["nil", "parameters", "scale", "short-circuit"],
        "用64参数、64个and连接的纯nil比较压力链验证逐节点求值事实复用与短路结果，不依赖debug名称。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/debug_01_scope_activity.lua",
        &["debug", "register-reuse", "scope", "shadow"],
        "以32个连续do-local复用寄存器，再接同起点双local、嵌套遮蔽与闭包捕获，压力验证debug活跃区间而非仅名称集合。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/calls_01_local_call_root_events.lua",
        &["call-result", "locals", "overwrite", "reads"],
        "先创建64个仍被尾部逻辑链读取的call-result local，压力观察分析按binding事件推进；再用条件overwrite验证旧object作为下一次replace实参。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/roots_02_observation_events.lua",
        &["locals", "lookup", "observations", "scale"],
        "创建64个不同索引lookup home，在64次collectgarbage观察后仍逐一读取求和，压力验证future-read事件不会被观察语句截断。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/roots_03_local_nil_clear.lua",
        &["gc-root", "locals", "nil-clear", "scale"],
        "创建128个独立表与128个weak槽，保活跨一次GC、验证环状相邻身份均不同，再逐一nil清空并确认全部回收，压力宽local根与清根。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/locals_06_allocation_home_index.lua",
        &["allocation", "gc-root", "overwrite", "two-values"],
        "让first/second各复制到16个home，再将全部a-home改写为对应b-home，要求first释放而second继续活；清空32home后second释放。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/expressions_03_return_lookup_value_dag.lua",
        &[
            "dag",
            "evaluation-count",
            "nested-index",
            "operator",
            "scale",
        ],
        "双用算术DAG及32层未知字段链不得指数重扫；分别观察__add、__index次数并保留连续访问结构。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/expressions_04_deep_arithmetic_chain.lua",
        &["formatting", "left-associative", "metamethod", "recursion"],
        "4096个a组成4095次左结合加法，要求完整管线不截断、不重结合且格式化不产生巨行。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/roots_04_holder_reuse.lua",
        &["local-limit", "scale", "sequential", "snapshot"],
        "同一临时槽顺序产生224个源码snapshot，必须复用额外身份而不能超过Lua 200 local。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55])
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/roots_05_shared_home_root_intervals.lua",
        &["backedge", "copies", "not-chain", "scale"],
        "16个独立copy home跨64次not suffix与回边，在首块常量覆盖处分别退休。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_52),
            LuaCaseConfiguration::new(PUC_LUA_GE_52).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/expressions_05_value_chain.lua",
        &["metamethod", "multiret", "not", "truthiness"],
        "256次NOT链、callback多返回截断、比较元方法和error传播共同验证布尔化不暴露原值或额外结果。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/controlflow_07_pure_suffix_close_loop.lua",
        &["backedge", "copies", "goto", "not-chain"],
        "8个copy位于带scope回边区，128次纯suffix可共享DAG但不得改变初始入口或末端写。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_52),
            LuaCaseConfiguration::new(PUC_LUA_GE_52).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/controlflow_08_shared_short_circuit.lua",
        &["continuation", "error", "identity", "short-circuit"],
        "7776种五原子组合与六层diamond验证共享continuation不树化且保留nil/false/object身份。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/controlflow_09_pure_decision_graph.lua",
        &["decision", "factoring", "identity", "scale"],
        "共享尾在图内归约，wide四组逻辑块不得先指数树化。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/closures_02_luau_inlined_factory_activation.lua",
        &["activation", "inlining", "register-pressure"],
        "O2已内联factory effect属于caller，123个keep抬高frame后两次factory仍有相同debug.info activation。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_stress/constants_05_boundary.lua",
        &["constant-index", "loadkx", "setlist"],
        "262145项连续整数构造器同时跨越Lua5.2 SETLIST块和LOADKX常量索引边界，防止EXTRAARG解释错位。",
        &[LuaCaseConfiguration::new(PUC_LUA_52).with_options(NO_RECOMPILE_STRESS_OPTIONS)],
    ),
];
