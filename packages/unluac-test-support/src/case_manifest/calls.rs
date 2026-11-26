//! calls 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;
pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_calls/method_18_short_circuit_arg_self_restore.lua",
        &["method-call", "short-circuit", "table-store"],
        "短路参数跨块冲刷后的三行 SELF 调用还原为方法调用，表写入短路右值与取反布尔分支保持简洁等价。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/results_14_branch_multi_result_prefix.lua",
        &["call-frame", "multi-return", "branch", "table"],
        "多返回的空接收声明仍依赖条件输入前缀，表构造与调用帧不得因此错位。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/results_13_writeback_before_callable.lua",
        &["call-frame", "writeback", "closure", "captured-cell"],
        "捕获 cell 的 CALL 写回不吞并后继低槽闭包声明；普通调用读取其返回值，观察 cell 改写、快照身份和两条结果路径。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/results_12_global_writeback.lua",
        &[
            "fixed-width",
            "global-metamethod",
            "eval-order",
            "call-frame",
        ],
        "固定 CALL 结果按原逆序直接写回环境；观察对象身份、nil/false、额外返回值、异常中断及后继表写时点。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/fastcall_12_parameter_writeback.lua",
        &["fastcall", "copy", "parameter", "call-frame"],
        "连续两次参数更新保留 CALL 低槽写回，下一 FASTCALL 的参数 COPY 不反挂到前一结果定义。",
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
        "tests/case_calls/fastcall_11_fixed_all_arguments.lua",
        &[
            "fastcall",
            "lookup-order",
            "fixed-arguments",
            "runtime-observer",
        ],
        "通用 FASTCALL 固定空参数和四参数帧保持求值顺序、单结果调整与 fallback callee 读取时点。",
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
        "tests/case_calls/fastcall_10_dynamic_lookup_message.lua",
        &[
            "fastcall",
            "dynamic-key",
            "concat",
            "metamethod",
            "snapshot",
        ],
        "索引首参数与 CONCAT 消息同帧求值，消息元方法改写原表时仍使用先前索引快照。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
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
        "tests/case_calls/results_11_writeback_before_capture.lua",
        &["multi-result", "capture", "slot-reuse", "recompile"],
        "多结果写回与同槽未来捕获区分原 Def，保持调用次数、低槽赋值和后继闭包的 cell。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/results_10_return_arithmetic_frame.lua",
        &["return", "multi-result", "metamethod", "recompile"],
        "RETURN 首项快照和后一项算术同帧恢复，保留对象身份、元方法次数及三轮收敛。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/results_09_reused_writeback_versions.lua",
        &[
            "call-frame",
            "multi-result",
            "slot-reuse",
            "eval-order",
            "recompile",
        ],
        "不同宽度 CALL 复用结果槽时按原 Def 证明低槽写回，后续新声明不继承旧 scratch 身份。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/callee_07_nested_lookup_frame.lua",
        &[
            "call-frame",
            "lookup-order",
            "metamethod",
            "callee-snapshot",
        ],
        "嵌套字段 callee 在参数改写前各读取一次，保留完整调用比较及原函数快照。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/results_08_grouped_call_declarations.lua",
        &[
            "call-frame",
            "declaration",
            "eval-order",
            "fastcall",
            "recompile",
        ],
        "并列 CALL 声明保持共同 scratch、求值顺序、单值截断及独立对象身份，反复重编译不产生 COPY 链。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/callee_06_truthy_call_chain_frame.lua",
        &["callee", "condition", "call-frame", "eval-order"],
        "条件调用链整体重发原单结果帧，保持 truthiness、求值顺序和具名结果身份。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
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
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
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
        "tests/case_calls/order_01_loop_header_eval_order.lua",
        &["metamethod", "numeric-for", "stress"],
        "numeric-for header 的四个副作用依序求值，宽条件前缀只在最终 while 根展开一次。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_02_direct_method_receiver_eval_count.lua",
        &["eval-count", "metamethod", "snapshot"],
        "普通点调用需先取callee再重新读取receiver argument，__index改写全局后应传入新对象。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
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
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_03_short_circuit_pure_call_operand.lua",
        &["method", "numeric-for", "short-circuit"],
        "pure boolean shell后的method call不迫使goto并正确控制内层star循环。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_06_method_chain_live_receiver.lua",
        &["closure", "method-chain", "constructor", "multiret"],
        "保留活跃 receiver 身份，构造器参数不截断 SELF 链，延迟闭包和尾部数组保持求值顺序。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
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
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
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
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
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
        "tests/case_calls/arguments_02_generic_for_vararg_pack.lua",
        &["generic-for", "open-tail", "vararg"],
        "保证exact vararg producer作为generic-for head的开放尾展开。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
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
        "tests/case_calls/arguments_03_adjacent_final_arg_value_arity.lua",
        &["final-argument", "multi-return", "scalar"],
        "保证从local initializer移入最终实参的call仍截断为单值。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/fastcall_01_luau_fastcall_conditional.lua",
        &["conditional", "eager", "fastcall"],
        "保证FASTCALL参数内短路RHS仍属条件区，而先前eager producer保持独立。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
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
        "tests/case_calls/arguments_05_method_alias_multi_return_head.lua",
        &["method", "multi-return", "scalar"],
        "保证method call位于多返回首槽时截断为单值。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_07_constructor_extra_arg_order.lua",
        &["alias", "constructor", "evaluation-order", "multi-return"],
        "区分constructor handoff前后额外实参的事件证明，并保持宽参数和重复逆序别名。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/returns_06_terminal_nil_pack_unrelated_tbc.lua",
        &["close", "nil-pack", "repeat"],
        "验证无关TBC生命周期不应阻止终态nil,nil value-pack直接收回到return。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55])
                .with_options(LuaCaseOptions {
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55])
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_10_call_updates.lua",
        &["callee-update", "evaluation-order", "method-call", "stress"],
        "分别连续16次执行fn=fn(mark(i))与object=object:next(mark(i))，固定callee/self在调用前读取且返回的新callee/receiver写回原home，mark只求值一次。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_17_inlined_factory_identity.lua",
        &[
            "closure-identity",
            "evaluation-order",
            "method-call",
            "inlining",
        ],
        "同形工厂的共享方法仍属不同原始模板，展开捕获更新与receiver写回保持身份、次数及debug绑定。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_16_open_tail_writeback.lua",
        &["method", "open-tail", "eval-order", "writeback"],
        "观察开放尾参数、方法 lookup 与 dispatch 的顺序，并保持多返回宽度和原 receiver 写回。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/callee_03_pure_callable_chain.lua",
        &["boolean-callable", "callee", "metatable", "not-chain"],
        "保留64次显式NOT写回，布尔值通过debug metatable合法__call且不产生callee中转。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_10_pure_argument_chain.lua",
        &["argument", "fastcall", "not-chain", "truthiness"],
        "FASTCALL tostring/type与普通参数链共享依赖事实，但各调用站点仍保持参数复杂度。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_options(LuaCaseOptions {
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                })
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    recompile_rounds: Some(3),
                    ..LuaCaseOptions::DEFAULT
                })
                .with_variants(&[LuaCaseVariant::LuauO2]),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/results_03_luau_call_result_copy.lua",
        &["call-result", "convergence", "scratch"],
        "活动低槽赋值重发callee scratch与CALL回写，避免roundtrip每轮新增scratch。",
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
        "tests/case_calls/fastcall_02_luau_fastcall_boolean_fallback.lua",
        &["boolean", "fastcall", "lookup-order"],
        "FASTCALL1在参数后读取fallback；参数__index替换全局assert，当前调用必须使用被替换版本。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)
            .with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            })
            .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/multireturn_03_luau_open_assert_lookup_order.lua",
        &["fastcall", "lookup-order", "open-return"],
        "O1/O2先求开放参数，fallback再lookup assert，参数回调替换环境assert并接收三值。",
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
        "tests/case_calls/fastcall_05_saved_builtin_aliases.lua",
        &["fastcall", "lookup-order", "open-return", "snapshot"],
        "保存的 builtin 与多级别名在参数回调替换全局后仍读取原快照，固定与开放参数保留原调用协议。",
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
        "tests/case_calls/fastcall_06_library_open_tail.lua",
        &["fastcall", "lookup-order", "open-return"],
        "保存的库表在开放尾回调后读取 fallback 字段，保留固定首参数与多返回尾宽度。",
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
        "tests/case_calls/arguments_12_constructor_capture_reuse.lua",
        &["table-field", "capture", "call-frame", "readability"],
        "构造器准备槽随后被新捕获变量复用时，保留真实cell且不重复物化早期元素。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/multireturn_04_return_and_multiret.lua",
        &["multi-return", "tail-call", "truncation", "vararg"],
        "九组返回协议覆盖固定多结果、表/参数屏障、变参尾调用、select与括号截断及多赋值旋转。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/method_15_and_self.lua",
        &["callee-copy", "method-call", "self", "vararg"],
        "方法链语法糖、显式self提取调用、变参方法多返回及self赋值作用域。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_13_conditional_call_frame.lua",
        &["short-circuit", "callee", "evaluation-order", "truncation"],
        "条件参数复用前次匿名结果；false跳过RHS，选中false/nil/0仍单值传递，RHS改写callee后继续调用此前快照。",
        &[
            LuaCaseConfiguration::new(LUAJIT_ONLY).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_calls/arguments_14_prepared_boolean_call.lua",
        &[
            "short-circuit",
            "callee",
            "evaluation-order",
            "comparison",
            "metamethod",
        ],
        "普通Boolean参数调用保留callee先读、原生NOT及四种比较的方向、短路、异常与单次交付。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)
            .with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            })
            .with_variants(LUAU_O0_ONLY)],
    ),
];
