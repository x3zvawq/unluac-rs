//! calls 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;
pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_calls/callee_06_truthy_call_chain_frame.lua",
        &["callee", "condition", "call-frame", "eval-order"],
        "条件调用链整体重发原单结果帧，保持 truthiness、求值顺序和具名结果身份。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/results_07_arithmetic_initializer_frame.lua",
        &[
            "initializer",
            "arithmetic",
            "call-frame",
            "metamethod",
            "eval-order",
        ],
        "算术声明帧保持左侧元方法先于右侧 CALL，并保留 debug 声明和结果截断。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/callee_01_short_circuit_header_call.lua",
        &["eval-count", "short-circuit", "truthiness"],
        "证明 type guard 阻止非函数调用，函数 operand 仅求值一次且 0 仍按 Lua 规则为真。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_01_receiver_single_value.lua",
        &["call-chain", "method-call", "receiver"],
        "确保 receiver-only 的链式冒号调用不会把 receiver 误当作末尾显式参数。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/inline_01_mechanical_call_and_for_inline.lua",
        &["escaped-root", "generic-for", "temp-inline"],
        "在同一模块中覆盖普通调用准备与嵌套全局表路径的 ipairs 迭代准备，防止逃逸表 root 的 overwrite endpoint 被机械删除。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/order_01_loop_header_eval_order.lua",
        &["metamethod", "numeric-for", "stress"],
        "numeric-for header 的四个副作用依序求值，宽条件前缀只在最终 while 根展开一次。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_02_direct_method_receiver_eval_count.lua",
        &["eval-count", "metamethod", "snapshot"],
        "普通点调用需先取callee再重新读取receiver argument，__index改写全局后应传入新对象。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/order_02_inline_call_alias_eval_order.lua",
        &["barrier", "temp-inline"],
        "inline sink不能重排first/second调用，保留声明keep必须阻断before/after搬运。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/returns_01_terminal_return_call_order.lua",
        &["eval-order", "snapshot"],
        "return首值state必须在末尾callee修改state前取快照。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_01_method_fixed_prefix_open_tail.lua",
        &["method", "multiret", "open-pack"],
        "method固定参数1位于multi开放尾2,3之前。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_03_short_circuit_pure_call_operand.lua",
        &["method", "numeric-for", "short-circuit"],
        "pure boolean shell后的method call不迫使goto并正确控制内层star循环。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_06_method_chain_live_receiver.lua",
        &["closure", "method-chain"],
        "method sugar不能删除后续被done closure读取的button。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_07_hint_open_arg_call.lua",
        &["method-hint", "roundtrip"],
        "重复SELF夹多返回参数仍保留method hint。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua51, LuaCaseDialect::Lua54])
                .with_options(LuaCaseOptions {
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/order_06_call_arg_eval_order.lua",
        &["eval-order", "global-metamethod"],
        "source参数producer必须先于全局sink callee查找。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/order_07_global_arg_eval_order.lua",
        &["eval-order", "global-read"],
        "全局参数source读取不能越过callee sink读取。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/order_08_loop_cond_eval_order.lua",
        &["condition", "repeat"],
        "repeat条件内联不能把guard移动到body side之前。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_11_chain_dead_local_side_effect.lua",
        &["chain", "dead-local", "side-effect"],
        "method chain不能吞前置dead local初始化side。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_12_hint_short_circuit_arg.lua",
        &["method-hint", "short-circuit"],
        "SELF后短路参数不能丢method hint。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_04_alias_sink_order.lua",
        &["callee-snapshot", "loop", "method-alias", "single-eval"],
        "保证 method alias 不跨外层 callee 变异或循环边界下沉，并保持 receiver 工厂只执行一次。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_05_generic_for_live_method_receiver.lua",
        &["closure", "generic-for", "live-out", "method-receiver"],
        "保证循环后仍被闭包使用的 method receiver 保留声明与身份。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/inline_02_temp_inline_independent_runs.lua",
        &["callee", "fixed-point", "temp-inline"],
        "确保三个独立 callee/materialization run 在同轮批量收敛。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_O0_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/multireturn_01_return_captured_snapshot.lua",
        &["callee-lookup", "metamethod", "multi-return", "snapshot"],
        "保证 open return 固定前缀在 callee lookup 副作用前快照。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/returns_02_terminal_nil_return_pack.lua",
        &["capture", "multi-return", "nil-pack"],
        "保证终态fixed nil pack直接返回两个nil且不留机械temp。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/order_03_constructor_argument_call_order.lua",
        &["argument", "call-pack", "constructor", "gc"],
        "保证重建call参数pack时表字段先于后续condition参数求值，并维持捐赠对象释放。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_02_generic_for_vararg_pack.lua",
        &["generic-for", "open-tail", "vararg"],
        "保证exact vararg producer作为generic-for head的开放尾展开。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/returns_03_mechanical_multi_return_scalars.lua",
        &["gc-root", "metamethod", "multi-return", "return-frame"],
        "区分算术结果经高槽 COPY 返回与直接表达式返回的 caller 残根，并保持比较返回的可读性。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/order_04_multi_return_call_run_order.lua",
        &["call", "return-prefix", "snapshot"],
        "证明call preparation run可跨稳定return前缀，却不能越过observed值快照。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/order_05_extended_return_call_run_order.lua",
        &["call", "event", "lookup", "return"],
        "禁止call或effectful field producer越过return prefix观察，并分别固定v/l→o→p顺序。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/returns_04_extended_return_call_run.lua",
        &["callee", "field", "method", "preparation", "return"],
        "保证call、field与method三类producer各自保留完整的非尾动态callee preparation run。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_03_adjacent_final_arg_value_arity.lua",
        &["final-argument", "multi-return", "scalar"],
        "保证从local initializer移入最终实参的call仍截断为单值。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/fastcall_01_luau_fastcall_conditional.lua",
        &["conditional", "eager", "fastcall"],
        "保证FASTCALL参数内短路RHS仍属条件区，而先前eager producer保持独立。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/returns_05_open_return_nil_after_branch.lua",
        &["branch", "nil-pack", "open-return"],
        "保证已结束root branch不阻止终态两个nil前缀收回。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_04_generic_for_exact_tail_arity.lua",
        &["extra-value", "fixed-call", "generic-for"],
        "保证只接收两个fixed call结果时不会把其余结果变成open generic-for pack。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_08_alias_nested_call_stmt.lua",
        &["alias", "call-statement", "gc", "prefix"],
        "嵌套点调用保留lookup前的r5/r7旧根；稳定receiver或前缀不授权提前SELF覆盖。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_05_method_alias_multi_return_head.lua",
        &["method", "multi-return", "scalar"],
        "保证method call位于多返回首槽时截断为单值。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_09_method_alias_numeric_for_start.lua",
        &["method", "scalar", "single-eval", "gc-root"],
        "numeric-for start只求值一次并截断结果，保留显式字段调用与SELF预写的根时序区别。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_06_method_alias_multi_assign_head.lua",
        &["method", "multi-assign", "scalar", "gc-root"],
        "首RHS字段调用截断额外返回并恢复两项参数赋值，保留分支与lookup后receiver COPY的根时序。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_07_constructor_extra_arg_order.lua",
        &["alias", "constructor", "evaluation-order", "multi-return"],
        "区分constructor handoff前后额外实参的事件证明，并保持宽参数和重复逆序别名。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/returns_06_terminal_nil_pack_unrelated_tbc.lua",
        &["close", "nil-pack", "repeat"],
        "验证无关TBC生命周期不应阻止终态nil,nil value-pack直接收回到return。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/roots_01_non_tail_callable_root.lua",
        &[
            "callable",
            "gc-root",
            "metamethod",
            "multi-return",
            "mutable-capture",
            "terminal-call",
        ],
        "固定动态 __call 对象在非尾调用前后保持 local root；兄弟闭包改写 factory 后，终端调用也不能继续使用旧的必然闭包返回证明。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_08_lookup_argument_handoff.lua",
        &["argument", "caller-home", "gc-root", "lookup"],
        "对照直接consume(weak.key)与先保存source再consume(source)：callee只接管实参home，独立caller source home必须继续保活到显式清空。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_10_call_updates.lua",
        &["callee-update", "evaluation-order", "method-call", "stress"],
        "分别连续16次执行fn=fn(mark(i))与object=object:next(mark(i))，固定callee/self在调用前读取且返回的新callee/receiver写回原home，mark只求值一次。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/roots_02_call_dispatch_root_order.lua",
        &["argument", "callee-lookup", "gc-root"],
        "对Luajit动态环境调用分别把pair结果home作为被覆盖callee或独立argument，观察callee lookup、dispatch、value清空与caller清空时根存活差异。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Luajit]),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Luajit]).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_09_call_argument_root_handoff.lua",
        &["argument", "gc-root", "handoff", "prefix"],
        "后续实参求值GC时保住前一make结果，进入use后清参数即允许回收，caller不得暗留副本。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/roots_03_debug_scope_mutable_callee.lua",
        &["callable", "debug", "gc-root", "lookup"],
        "__call内清外层callee cell时callee仍活；scope后missing global lookup期间callee与scoped也仍活，实际gc调用后两者才死。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/results_01_multi_result_frame_roots.lua",
        &["debug", "gc-root", "multi-return", "parallel-write"],
        "两个旧多返回home在replace_pair调用入口前都应退休，返回_G/1并行写入env/tag。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/callee_02_multi_result_callee_lookup.lua",
        &["callee-lookup", "gc-root", "metamethod", "multi-return"],
        "在dispatch.missing callee lookup期间第二旧root仍活，进入replace_pair实际调用并清cell后两个root才死。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/callee_03_pure_callable_chain.lua",
        &["boolean-callable", "callee", "metatable", "not-chain"],
        "64次not依赖后布尔值通过debug metatable合法__call，callee链必须整体提交。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(LUAJIT_ONLY),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_10_pure_argument_chain.lua",
        &["argument", "fastcall", "not-chain", "truthiness"],
        "FASTCALL tostring/type与普通参数链共享依赖事实，但各调用站点仍保持参数复杂度。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(LUAJIT_ONLY),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_13_chain_frame_roots.lua",
        &["callee-order", "gc-root", "method-chain", "multiret"],
        "provider:make():next():finish()链中SELF覆盖前call结果，已交callee的receiver不得留caller root，outer chain_sink须在nested method前读取。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_14_lookup_method_receiver_roots.lua",
        &["gc", "lookup", "method", "receiver"],
        "SELF覆盖低槽lookup根，首参仍活过method lookup与参数求值；对照direct与retained receiver。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/multireturn_02_call_return_values.lua",
        &["alias", "gc", "known-callee", "multi-return"],
        "覆盖已知callee各槽值域、空/可变宽度、alias重绑、branch未知callee、callee-before-args、capture、constructor、递归及second-result root。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/callee_04_argument_callee.lua",
        &["argument-order", "callee", "gc", "open-return"],
        "参数内callee必达，同时保留前序事件、条件、循环、OPEN宽度、callee重绑、captured参数及dot receiver槽。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/returns_07_native_return_frames.lua",
        &["copy", "gc", "open-width", "return"],
        "native RETURN重发参数区COPY并覆盖数字callee残留，覆盖fixed、open empty、open nil三种宽度。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/results_02_prefix_residuals.lua",
        &["alias", "boolean", "gc", "residual"],
        "低槽Boolean/alias作为caller prefix，删除声明不能改变残值位置。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_51),
            LuaCaseConfiguration::new(PUC_LUA_51).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/results_03_luau_call_result_copy.lua",
        &["call-result", "convergence", "scratch"],
        "活动低槽赋值重发callee scratch与CALL回写，避免roundtrip每轮新增scratch。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_CONVERGENCE_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/fastcall_02_luau_fastcall_boolean_fallback.lua",
        &["boolean", "fastcall", "lookup-order"],
        "FASTCALL1在参数后读取fallback；参数__index替换全局assert，当前调用必须使用被替换版本。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/roots_04_luau_comparison_call_frames.lua",
        &["call-order", "comparison", "gc"],
        "两比较的factory operands占独立结果槽，且旧对象活到__eq回调返回。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/results_04_call_result_frame.lua",
        &["boolean", "call-result", "gc", "scratch", "scope"],
        "单结果CALL保留接收宽度及原词法末端；常量覆盖与后继CALL复用均不得延长旧根或抬高帧。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/multireturn_03_luau_open_assert_lookup_order.lua",
        &["fastcall", "lookup-order", "open-return"],
        "O1/O2先求开放参数，fallback再lookup assert，参数回调替换环境assert并接收三值。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)
            .with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            })
            .with_variants(&[LuaCaseVariant::LuauO1, LuaCaseVariant::LuauO2])],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/fastcall_03_luau_mixed_fastcall_arguments.lua",
        &["constant-arg", "fastcall", "snapshot"],
        "math.max常量参数与fallback COPY共同恢复，事件参数必须先读旧value再调用setter。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_options(LuaCaseOptions {
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                })
                .with_variants(&[LuaCaseVariant::LuauO1, LuaCaseVariant::LuauO2]),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                })
                .with_variants(&[LuaCaseVariant::LuauO1, LuaCaseVariant::LuauO2]),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/fastcall_04_fastcall_direct_tables.lua",
        &[
            "fastcall",
            "lookup-order",
            "metatable",
            "short-circuit",
            "snapshot",
        ],
        "math.max/table.freeze保留direct参数次序；查表or空表在嵌套普通/FASTCALL中保持真值对象、false/nil备用表及单次元方法求值。",
        &[
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
        "tests/case_calls/results_05_puc_assignment_call_frame.lua",
        &[
            "assignment",
            "callee-copy",
            "recompile",
            "settabup",
            "upvalue",
        ],
        "保持高槽 CALL 的低槽写回及 SETTABUP 的调用后 cell 读取；重编译不得新增 callee 或错移赋值。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/callee_05_closure_callee_prefix.lua",
        &["callee-copy", "closure", "recompile", "sequence"],
        "三个顺序局部函数各调用两次print，第三组callee COPY不得在反复重编译中继续引入中转声明。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_11_table_call_frames.lua",
        &["generic-for", "open-return", "table-field", "vararg"],
        "表构造、泛型for、开放变参select与字段写共享临时槽时保持计数、首值和赋值顺序。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/results_06_callee_scratch_observation.lua",
        &["callee-copy", "gc", "proto-selector", "scratch-root"],
        "验证callee COPY、返回闭包及入口无用写的scratch观察；覆盖高槽/r0返回、无观察闭包与无后继CALL的lookup，不能凭新值无用删除物理写。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_52),
            LuaCaseConfiguration::new(PUC_LUA_GE_52).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/multireturn_04_return_and_multiret.lua",
        &["multi-return", "tail-call", "truncation", "vararg"],
        "九组返回协议覆盖固定多结果、表/参数屏障、变参尾调用、select与括号截断及多赋值旋转。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_15_and_self.lua",
        &["callee-copy", "method-call", "self", "vararg"],
        "方法链语法糖、显式self提取调用、变参方法多返回及self赋值作用域。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
];
