//! lifetime 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;
pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_lifetime/overwrite_10_call_move_independent_result_home.lua",
        &[
            "call-result",
            "move",
            "gc-root",
            "multi-return",
            "overwrite",
        ],
        "CALL 结果及低槽 MOVE 目标有独立覆盖端点，后继多返回调用不能丢失任一根 owner。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/scope_11_scalar_call_prefix.lua",
        &["call-frame", "scope", "scalar", "metamethod", "recompile"],
        "单读标量保留原 CALL 前缀，前段声明及时出栈，后段构造器与短路元方法仍各求值一次。",
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
        "tests/case_lifetime/scope_10_captured_branch_close.lua",
        &["scope", "capture", "branch", "debug"],
        "捕获声明跨内部条件后在独立 CLOSE 处结束，后继调用不再看到其 debug local，闭包仍读到正确值。",
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
        "tests/case_lifetime/close_01_scope_slot_reuse.lua",
        &["capture-cell", "slot-reuse", "upvalue"],
        "区分离开 do scope 后已关闭 count cell 与后续同槽复用，并验证 RHS 闭包捕获 inner 时不污染 outer。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_53).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/snapshot_01_loop_header_snapshot.lua",
        &["call-effect", "numeric-for"],
        "side调用改写value后，for起点仍使用调用前保存的start=1。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_02_lua55_generic_for_close_break_pad.lua",
        &["break", "close", "generic-for"],
        "generic-for自动CLOSE的fallthrough出口不应抢占本轮break owner。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_55).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/snapshot_02_cross_slot_snapshot_loop_state.lua",
        &["closure", "home-slot", "loop"],
        "不同home slot间move保持赋值时original快照，不随current循环写回。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/snapshot_03_temp_inline_eval_regions.lua",
        &["eval-order", "loop", "method", "temp-inline"],
        "覆盖while/repeat条件快照、numeric header顺序、多返回顺序、method lookup顺序及upvalue快照。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_03_lua54_close_value_pack.lua",
        &["close", "generic-for", "multiret"],
        "保护close binding、多值声明、generic-for第四值及branch隐式close顺序。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_04_mixed_irreducible_explicit_close.lua",
        &["close", "goto", "irreducible"],
        "显式close cleanup出边不能吞island目标label。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_05_mixed_irreducible_generic_close.lua",
        &["capture", "close", "generic-for", "irreducible"],
        "island不能破坏外层generic-for隐式close与captured值owner。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_06_close_managed_writable_capture.lua",
        &["capture", "close-managed", "metamethod"],
        "close管理epoch内__newindex仍可写captured written。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_07_irreducible_explicit_close_owner.lua",
        &["close", "goto", "reentry"],
        "island重入/侧出口保持显式close生命周期。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/snapshot_04_temp_inline_binding_snapshot.lua",
        &["binding", "call", "temp-inline"],
        "value快照必须停在更早mutate调用之前。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/snapshot_05_inline_stmt_eval_order.lua",
        &["capture", "eval-order", "method"],
        "前置producer不能越过callee/receiver，written/captured source快照保持旧对象。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_51).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/scope_07_infinite_loop_local_merge.lua",
        &["coroutine", "local", "while", "yield"],
        "无限循环每轮局部值的合流与生命周期不能泄漏到下一轮。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_51).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/scope_08_nested_loop_scope_state.lua",
        &["break", "generic-for", "repeat", "shared-state"],
        "嵌套repeat必须留在外层for作用域并共享同一x状态。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/iterator_01_for_tbc_break.lua",
        &["break", "capture", "close", "numeric-for"],
        "观察 numeric-for 在 break 时按词法边界关闭迭代内 TBC，同时保留逃逸闭包捕获的 snapshot。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_08_tbc_iteration_scope.lua",
        &["break", "close", "iteration-scope", "repeat"],
        "证明 repeat 条件两侧的 CLOSE 属于每轮共享词法域，包括条件读取 TBC 与提前 break。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_09_repeat_nested_close_scope.lua",
        &["close", "condition-order", "do-block", "repeat"],
        "要求内层 do 的资源在每次 until 条件求值前关闭。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_10_dead_label_tbc_barrier.lua",
        &["active-set", "goto", "label", "tbc"],
        "保证raw Close收敛前机械label维持TBC active-set屏障。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_11_scope_epochs.lua",
        &["close", "epoch", "register-reuse", "return"],
        "保证顺序<close>作用域虽复用寄存器仍是不同资源epoch。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/gc_01_boolean_shell_gc_inert_old_value.lua",
        &["boolean-shell", "dead-write", "primitive"],
        "非相邻 primitive 旧值不授权删除原 truthiness 检查及布尔写回。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_12_tail_do_same_exit.lua",
        &["close", "debug", "do-block", "return", "backedge"],
        "debug尾块中的return只关闭资源一次，回边清理不能提前结束正常出口的外层资源。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_05_nested_close_common_copy.lua",
        &["branch", "close", "common-copy"],
        "允许common copy移动到已结束nested close scope之后。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_13_repeat_nested_close_owner.lua",
        &["close", "numeric-for", "owner", "repeat"],
        "保证nested loop资源在外层repeat tail guard之前关闭。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_14_repeat_tbc_condition_owner.lua",
        &["break", "repeat", "tbc"],
        "保证repeat-owner TBC在tail break guard之后关闭，不能合入until。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_55).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_15_repeat_closed_block_resource.lua",
        &["close", "do-block", "repeat", "tail"],
        "保证completed lexical block在repeat tail前关闭。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/lookup_01_method_chain_receiver_extra_use.lua",
        &["close", "extra-use", "method-chain"],
        "保证receiver作为额外实参或Close binding时不能被链式糖删除。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54]).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_17_ownership.lua",
        &["close-binding", "goto", "order", "scope"],
        "固定两种 goto 离开嵌套 close scope 与正常 fallthrough 的关闭顺序，并确保汇合后的 later sibling 即使复用槽位仍独立 acquire/close。",
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
        "tests/case_lifetime/close_18_cleanup_event_order.lua",
        &["close-binding", "goto", "iterator", "return-freeze"],
        "覆盖空scope、嵌套close、close后callee、repeat condition、iterator dispatch、goto/normal共享出口，以及RETURN冻结局部/表值/多返回/调用结果后再执行close回调的完整事件顺序。",
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
        "tests/case_lifetime/close_19_cleanup_tail.lua",
        &["backedge", "close-binding", "goto", "upvalue"],
        "用linear、branching、captured-local三条后向goto路径区分inner正常close、outer尾close和无TBC origin的upvalue close事件。",
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
        "tests/case_lifetime/close_22_return_error_order.lua",
        &[
            "close-binding",
            "const",
            "error",
            "initializer",
            "return-order",
        ],
        "完整资源初始化先于 TBC 激活；初始化抛错不 close，正常与 error 展开各 close 一次，return 值在 close 前冻结。",
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
];
