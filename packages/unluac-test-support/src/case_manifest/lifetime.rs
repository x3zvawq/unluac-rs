//! lifetime 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;
pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_01_scope_slot_reuse.lua",
        &["capture-cell", "slot-reuse", "upvalue"],
        "区分离开 do scope 后已关闭 count cell 与后续同槽复用，并验证 RHS 闭包捕获 inner 时不污染 outer。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_53)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/snapshot_01_loop_header_snapshot.lua",
        &["call-effect", "numeric-for"],
        "side调用改写value后，for起点仍使用调用前保存的start=1。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_02_lua55_generic_for_close_break_pad.lua",
        &["break", "close", "generic-for"],
        "generic-for自动CLOSE的fallthrough出口不应抢占本轮break owner。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/snapshot_02_cross_slot_snapshot_loop_state.lua",
        &["closure", "home-slot", "loop"],
        "不同home slot间move保持赋值时original快照，不随current循环写回。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/snapshot_03_temp_inline_eval_regions.lua",
        &["eval-order", "loop", "method", "temp-inline"],
        "覆盖while/repeat条件快照、numeric header顺序、多返回顺序、method lookup顺序及upvalue快照。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_03_lua54_close_value_pack.lua",
        &["close", "generic-for", "multiret"],
        "保护close binding、多值声明、generic-for第四值及branch隐式close顺序。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_04_mixed_irreducible_explicit_close.lua",
        &["close", "goto", "irreducible"],
        "显式close cleanup出边不能吞island目标label。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_05_mixed_irreducible_generic_close.lua",
        &["capture", "close", "generic-for", "irreducible"],
        "island不能破坏外层generic-for隐式close与captured值owner。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_06_close_managed_writable_capture.lua",
        &["capture", "close-managed", "metamethod"],
        "close管理epoch内__newindex仍可写captured written。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_07_irreducible_explicit_close_owner.lua",
        &["close", "goto", "reentry"],
        "island重入/侧出口保持显式close生命周期。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/snapshot_04_temp_inline_binding_snapshot.lua",
        &["binding", "call", "temp-inline"],
        "value快照必须停在更早mutate调用之前。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/snapshot_05_inline_stmt_eval_order.lua",
        &["capture", "eval-order", "method"],
        "前置producer不能越过callee/receiver，written/captured source快照保持旧对象。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/scope_07_infinite_loop_local_merge.lua",
        &["coroutine", "local", "while", "yield"],
        "无限循环每轮局部值的合流与生命周期不能泄漏到下一轮。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/scope_08_nested_loop_scope_state.lua",
        &["break", "generic-for", "repeat", "shared-state"],
        "嵌套repeat必须留在外层for作用域并共享同一x状态。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/iterator_01_for_tbc_break.lua",
        &["break", "capture", "close", "numeric-for"],
        "观察 numeric-for 在 break 时按词法边界关闭迭代内 TBC，同时保留逃逸闭包捕获的 snapshot。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_08_tbc_iteration_scope.lua",
        &["break", "close", "iteration-scope", "repeat"],
        "证明 repeat 条件两侧的 CLOSE 属于每轮共享词法域，包括条件读取 TBC 与提前 break。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_09_repeat_nested_close_scope.lua",
        &["close", "condition-order", "do-block", "repeat"],
        "要求内层 do 的资源在每次 until 条件求值前关闭。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/release_01_exit_prefix_effect.lua",
        &["clear", "gc", "unused-read", "weak-table"],
        "证明 branch-exit 快捷路径保留未使用的可观察读取、显式清空及其 GC 释放效果。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_10_dead_label_tbc_barrier.lua",
        &["active-set", "goto", "label", "tbc"],
        "保证raw Close收敛前机械label维持TBC active-set屏障。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/allocation_01_installer_iife_lifetime.lua",
        &["closure", "gc", "installer", "weak-table"],
        "保证命名安装器不延长匿名IIFE closure生命周期。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_11_scope_epochs.lua",
        &["close", "epoch", "register-reuse", "return"],
        "保证顺序<close>作用域虽复用寄存器仍是不同资源epoch。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/gc_01_boolean_shell_gc_inert_old_value.lua",
        &["boolean-shell", "dead-write", "primitive"],
        "非相邻 primitive 旧值不授权删除原 truthiness 检查及布尔写回。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/gc_02_boolean_shell_gc_lifetime.lua",
        &["boolean-shell", "call-pack", "collection", "parameter"],
        "证明参数home的boolean写释放旧对象，同时区分caller仍持有owner的情形。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/gc_03_boolean_shell_local_gc_lifetime.lua",
        &["boolean-shell", "collection", "local-home"],
        "证明同一local home中的call结果在两种boolean写后释放，且再生成保持有限收敛。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(1),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_12_tail_do_same_exit.lua",
        &["close", "debug", "do-block", "return"],
        "保证retain-debug保留tail do时函数return仍只关闭资源一次。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/iterator_02_generic_for_dead_mirror_gc_root.lua",
        &["generic-for", "mirror", "weak-table", "while"],
        "保证dead generic-for carrier local不跨弱值GC观察保留旧binding。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/roots_01_call_root_binary_binding_rhs.lua",
        &["binary", "call", "gc", "metamethod"],
        "证明直接binding RHS不会在call结果与同home二元覆写间增加事件。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/roots_02_multi_return_call_root.lua",
        &["call", "gc", "multi-return", "copy", "return-frame"],
        "保证非尾嵌套调用的callee根跨参数求值存活，并区分高返回COPY与低槽直返在caller后续GC中的残根。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/roots_03_extended_index_key_lifetime.lua",
        &["call", "gc", "index", "key"],
        "保证索引key local跨后续参数求值和GC保持methods弱键可查。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/roots_04_mechanical_return_root_lifetime.lua",
        &["concat", "gc", "lookup", "return"],
        "保证nested return use不接管已恢复root，并覆盖短路与双concat元方法窗口。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/roots_05_mechanical_run_root_lifetime.lua",
        &["gc", "lexical-block", "lookup"],
        "保证recovered lookup local作为root存活到词法块末。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_01_lookup_copy_only_root.lua",
        &["copy", "gc", "home", "lookup"],
        "证明source清空后仅copy home跨GC，copy再清空即释放。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_02_lookup_distinct_home_lifetime.lua",
        &["gc", "home", "lookup"],
        "证明lookup source与copy是两个独立GC roots。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_03_lookup_multi_nil_release.lua",
        &["gc", "lookup", "parallel-nil"],
        "保证平行nil写同时终止所有复制lookup homes。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_04_physical_root_copy_lifetime.lua",
        &["alias", "gc", "physical-root"],
        "证明更短的alias home不能替代仍活跃的source物理root。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/roots_06_temp_inline_lookup_root_lifetime.lua",
        &["gc", "global-sink", "lookup", "temp-inline"],
        "保证lookup snapshot首次赋给sink后仍作为root保活，直到自身清空。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/release_02_multi_nil_allocation_root.lua",
        &["allocation", "gc", "parallel-nil"],
        "保证并行nil overwrite终止每个已逃逸allocation物理root。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_05_nested_close_common_copy.lua",
        &["branch", "close", "common-copy"],
        "允许common copy移动到已结束nested close scope之后。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_13_repeat_nested_close_owner.lua",
        &["close", "numeric-for", "owner", "repeat"],
        "保证nested loop资源在外层repeat tail guard之前关闭。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_14_repeat_tbc_condition_owner.lua",
        &["break", "repeat", "tbc"],
        "保证repeat-owner TBC在tail break guard之后关闭，不能合入until。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_15_repeat_closed_block_resource.lua",
        &["close", "do-block", "repeat", "tail"],
        "保证completed lexical block在repeat tail前关闭。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/roots_07_dead_temp_param_home_lifetime.lua",
        &["gc", "parameter", "temp-home"],
        "保证参数覆写前的未读alias仍将旧参数对象root到函数退出。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_52)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_16_repeat_tail_closure_lifetime.lua",
        &["capture", "closure", "gc", "repeat"],
        "保证nested tail scope闭包及捕获对象在until条件前释放。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_52)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/release_03_allocation_branch_root_release.lua",
        &["allocation", "branch", "gc"],
        "保证branch两臂boolean覆写都在GC前释放escaped allocation root。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_52).with_options(LuaCaseOptions {
                // 重复生成仍须保留 TESTSET 的预写检查及旧对象根覆盖点。
                recompile_rounds: Some(2),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/release_04_lookup_branch_root_release.lua",
        &["branch", "gc", "lookup", "successor"],
        "验证lookup root在两臂覆写、terminal前释放及successor替换时的精确生死。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(1),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/overwrite_01_cleanup_full_parallel_overwrite.lua",
        &["gc", "initializer", "parallel", "root"],
        "保证fixed multi-call每个home在eventful overwrite求值期间独立root，并在精确覆写点释放。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/roots_08_generic_for_single_call_alias.lua",
        &["alias", "generic-for", "iterator"],
        "要求iterator工厂独立根保留到循环协议完成，不直接内联ipairs调用。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/scope_01_lookup_child_scope_end.lua",
        &["child-scope", "gc", "lookup"],
        "保证child lookup root在已证明home复用边界结束。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/release_05_dead_temp_stable_param_old_root.lua",
        &["copy", "gc", "parameter"],
        "保证复制稳定参数时仍释放目标slot原有对象root。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/allocation_02_branch_state_allocation_capture.lua",
        &["branch", "capture", "finalizer", "stress"],
        "保证allocation期间finalizer改写captured branch state后，选定臂仍正确覆盖。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_06_call_copy_only_root.lua",
        &["call", "closure", "gc", "home"],
        "保证copied call result在source home复用后仍作为root。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/iterator_03_method_alias_generic_for.lua",
        &["gc", "generic-for", "method", "receiver"],
        "验证首iterator可原子消费receiver alias，同时各种loop/call帧仍保留receiver根。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/calls_01_lua55_multi_global_tail_call.lua",
        &["gc", "multi-return", "write-order"],
        "验证global多赋值逆序probe逐个释放已消费结果槽。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/roots_09_method_chain_callback_root.lua",
        &["call-result", "gc", "method-chain", "repeat"],
        "防止method-chain糖跨opaque callback删除call-result root。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/lookup_01_method_chain_receiver_extra_use.lua",
        &["close", "extra-use", "method-chain"],
        "保证receiver作为额外实参或Close binding时不能被链式糖删除。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_07_callback_expiry_overwrite.lua",
        &[
            "block-scope",
            "callback",
            "explicit-nil",
            "gc",
            "local-copy",
            "method-chain",
            "stack-top",
        ],
        "分别观察未读COPY根跨回调保活、恢复stack-top后失效与显式nil前后释放，三个独立frame不共用状态。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/roots_10_dead_temp_physical_root.lua",
        &["callee", "dead-temp", "gc", "overwrite"],
        "验证HIR保留的dead physical-home copy不能被AST cleanup误删，同时无观察callee仍可内联。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/lookup_02_alias_capture_writes.lua",
        &["capture", "gc", "generic-for", "receiver"],
        "保留GETTABLE后receiver COPY的根事件，以及字段闭包安装回调对共享参数cell的改写。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54]).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54]).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_08_dead_temp_stable_local.lua",
        &[
            "callback",
            "capture",
            "gc",
            "local-copy",
            "physical-root",
            "slot-reuse",
        ],
        "区分参数副本承载的callback调用帧与对象保活；返回后观察残根覆盖窗口，保留显式覆盖与capture边界。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/release_06_cleanup_empty_physical_root.lua",
        &["block-scope", "gc", "slot-reuse", "weak-key"],
        "验证空local清理复用VM home时不会让已出块的旧对象继续成为物理根。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/release_07_repeat_tail_reassigned_root.lua",
        &["gc-root", "overwrite", "repeat", "terminal-branch"],
        "用两个弱表探针分别固定 repeat 尾部局部表在离开作用域后应先死亡，以及调用结果在终止分支覆盖旧物理 home 后不得继续保根；第二段特意区分 enabled 真分支的 nil home 与直接 return true 分支。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_09_call_root_immediate_move_overwrite.lua",
        &["call-result", "finalizer", "gc-root", "move"],
        "固定调用 replacement 的结果经紧邻 MOVE 覆盖旧可终结对象 home 时，旧对象在调用期间仍活、赋值完成后应释放，且新字符串结果继续用于字段写入。",
        &[LuaCaseConfiguration::new(&[
            LuaCaseDialect::Lua54,
            LuaCaseDialect::Lua55,
        ])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/overwrite_03_call_root_multi_home_overwrite.lua",
        &["alias", "finalizer", "gc-root", "overwrite"],
        "让 first、second 两个 home 各持有独立终结对象，再同时改为同一个 replacement，要求一次并行覆盖释放两个旧 root，且三个名字最终指向同一新对象。",
        &[LuaCaseConfiguration::new(&[
            LuaCaseDialect::Lua54,
            LuaCaseDialect::Lua55,
        ])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/allocation_03_home_owner.lua",
        &["allocation", "copy", "gc-root", "overwrite"],
        "固定同一分配值复制到多个 VM home 后，每个 home 有独立 producer/overwrite transaction；source 清空后 copy 改写为 collectgarbage 函数应释放原表。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/iterator_04_generic_for_dispatch_capture_root.lua",
        &["closure", "gc-root", "generic-for", "iterator"],
        "固定零次循环也必发生一次 iterator dispatch；iterator 捕获 repeat body 的 item 并发布弱引用，因此 item 必须活到随后 until condition 的 GC 观察。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/iterator_05_generic_for_binding_repeat_root.lua",
        &["binding", "copy-root", "generic-for", "repeat"],
        "固定 generic-for 成功 dispatch 边上未知调用结果写入 binding，binding 再复制到 saved 后，即使循环退出仍需让 saved 作为物理 root 穿过 repeat condition。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/calls_02_allocation_call_escape.lua",
        &["gc-root", "nil-overwrite", "opaque-call", "weak-reference"],
        "证明 allocation 传入 opaque publish 后，即使外部只留弱引用，原 local home 仍需保到显式 value=nil；nil overwrite 后则必须释放。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/release_08_generic_for_exit_result_home.lua",
        &["gc-root", "generic-for", "result-home", "zero-iteration"],
        "在进入 generic-for 前用宽 local 把 old 放到可能复用的结果 home，要求第一次且为退出的 iterator dispatch 前该旧 home 已停止作为 VM root。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_10_luau_copy_root_call_move_overwrite.lua",
        &["call-result", "copy-root", "gc"],
        "固定 Luau O0 中未读 root_copy 在 replacement 调用执行期间仍保住 original，直到调用结果 MOVE 覆盖该 home 后才释放。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_O0_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/allocation_04_escape_identity.lua",
        &["aggregate", "closure-effect", "gc-root", "metamethod"],
        "用四段运行探针覆盖聚合 holder 后加入 child 的持有传播、__index 暴露 key、已知 closure 的 capture escape、repeat 条件查询传递持有边，以及并行交换后的对象身份。",
        &[LuaCaseConfiguration::new(&[
            LuaCaseDialect::Lua51,
            LuaCaseDialect::Lua54,
            LuaCaseDialect::Lua55,
        ])],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/iterator_06_for_factory_root.lua",
        &["factory", "frame", "gc-root", "generic-for"],
        "区分 generic-for 初始化阶段的 iterator 工厂和值循环期间的 dispatch 函数：显式 local iterator 的 VM 槽必须在 body 内继续保住被全局清空的 ipairs wrapper，函数结束后才释放。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/lookup_03_root_overwrite_chain.lua",
        &["environment", "gc-root", "lookup", "metamethod"],
        "通过代理环境的 __index/__newindex 串联 source、key、lookup_result、hits，固定复用 owner 的 lookup 在后继写入前后保留正确释放端点，不能让 receiver 越过 hits 观察。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/scope_03_end_copy_root_coverage.lua",
        &["callback", "copy-root", "debug", "scope-end"],
        "让 source 与未读 duplicate 共享 frame-end root，先经可内联子块改变 HIR，再删除 dead copy；callback GC 时必须仍能从 source 原求值点保住对象，函数结束后释放。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54]).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/overwrite_04_state_root_overwrites.lua",
        &["backedge", "gc-root", "parallel-assignment", "snapshot"],
        "让 left/right 在 repeat 回边上交换或自复制，holder 读 right 后再以 nil/false 清空，固定 carried identity 的释放终点；另以 x,x,y 多目标写和有副作用 mutate 验证所有 RHS 读取旧快照。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55])
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_17_ownership.lua",
        &["close-binding", "goto", "order", "scope"],
        "固定两种 goto 离开嵌套 close scope 与正常 fallthrough 的关闭顺序，并确保汇合后的 later sibling 即使复用槽位仍独立 acquire/close。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_18_cleanup_event_order.lua",
        &["close-binding", "goto", "iterator", "return-freeze"],
        "覆盖空scope、嵌套close、close后callee、repeat condition、iterator dispatch、goto/normal共享出口，以及RETURN冻结局部/表值/多返回/调用结果后再执行close回调的完整事件顺序。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_19_cleanup_tail.lua",
        &["backedge", "close-binding", "goto", "upvalue"],
        "用linear、branching、captured-local三条后向goto路径区分inner正常close、outer尾close和无TBC origin的upvalue close事件。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/debug_01_scope_end.lua",
        &["debug", "function-object", "scope", "weak-key"],
        "要求块内scoped函数的debug作用域在下一个GC观察前结束，而不能仅在chunk return前结束。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_11_lookup_shared_value_windows.lua",
        &["copy-chain", "gc-root", "lookup", "release"],
        "从一次weak lookup形成a0..a31复制链，逐步清空前31个home仍须由a31保活，最后清空a31才释放，证明共享value的物理home各有独立终点。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/lookup_04_read_lookup_release.lua",
        &["gc-root", "lookup", "overwrite"],
        "最小化一次weak lookup结果home：读取后GC必须保活，value=nil后下一次GC必须释放。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_12_call_same_home_identity.lua",
        &["alias", "call-result", "gc-root", "overwrite"],
        "最小证明call结果a与重复自赋值b=a仍是同一value但不同home；a清空后b保活，b清空后释放。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/calls_03_shared_value_roots.lua",
        &["call-result", "copy-chain", "gc-root", "release"],
        "由make调用结果形成a0..a31复制链，清空前31个home后由末home保活，最终清空末home才释放，隔离call producer的共享value root窗口。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/debug_02_root_handoff.lua",
        &["debug", "gc-root", "local-window", "metamethod"],
        "借weak.__newindex回调在a2声明前检查debug.getlocal不可见，声明后再检查可见，同时a0/a1/a2共同保住first直到全清。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_20_root_handoff.lua",
        &["allocation", "call-root", "close-binding", "gc"],
        "对纯allocation和call-result资源各用a2<close>接管，a0/a1清空不应释放；离开do触发一次close并允许对象回收。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55]),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55])
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/overwrite_05_root_owner_chain.lua",
        &["gc-root", "multi-return", "owner", "scope"],
        "pair一次返回两个新对象；第一do不清a/b则跨GC存活到scope末，第二do显式双nil后在scope内就应死亡，固定grouped result各owner链。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/scope_04_debug_scope_object_cohort.lua",
        &["call-result", "debug", "gc-root", "scope"],
        "同debug scope内表与局部函数共同结束，覆盖字面表、call-result表及外层callee三种cohort，scope后对象都应回收。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/lookup_05_debug_scope_lookup_root.lua",
        &["debug", "gc-root", "global-lookup", "metamethod"],
        "debug end后下一条GGET求值期间旧root仍活，调用完成后才退；另对外层callee重复同边界。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/scope_05_debug_scope_across_branch.lua",
        &["branch", "debug", "do-block", "gc-root"],
        "同一source local跨if/else与nested分支写入时须共享一个debug do窗口，不能按producer block拆分。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/scope_06_debug_scope_loop_windows.lua",
        &["debug", "numeric-for", "repeat", "while"],
        "区分loop body每轮闭合窗口与包住整个while/repeat的窗口，scope结束后scratch必须退休。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/iterator_07_debug_scope_numeric_for.lua",
        &["debug", "do-block", "gc-root", "numeric-for"],
        "numeric-for控制phi留在debug窗口内，循环末调用退休高槽，scope后对象释放。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/iterator_08_debug_scope_generic_for.lua",
        &["debug", "do-block", "gc-root", "generic-for"],
        "generic-for iterator/result/cleanup冻结协议不得让debug名字延长外层scoped对象。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/iterator_09_debug_scope_generic_for_close.lua",
        &["debug", "generic-for", "implicit-close", "order"],
        "generic iterator第4返回guard由原生for隐式close，必须在for后代码前关闭且外层do只处理自己的root。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55]),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55])
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/overwrite_06_debug_overwrite_lookup_root.lua",
        &["debug", "gc-root", "lookup", "overwrite"],
        "新debug env声明与旧object调用结果身份分离；求值missing lookup时旧root仍活，写入env完成后旧root退休。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_13_copy_root.lua",
        &["backedge", "gc-root", "global-lookup", "while"],
        "循环跨回边copy须活过下轮global lookup，但header实参槽覆盖后应退休。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/debug_03_cyclic_copy_debug_owner.lua",
        &["assert-flow", "gc-root", "while"],
        "与537同生命周期，但用assert值物化形成label flow，要求debug source owner与跨轮copy分别退休。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55]),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55]).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_14_cyclic_copy_source_scope.lua",
        &["debug", "gc-root", "setlocal", "while"],
        "copy只在loop body可见；iteration1通过debug.setlocal清当前copy后应立即释放，但header lookup期间仍需按交接时点保活。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_21_nested_close_source_scope.lua",
        &["close-binding", "copy", "debug", "while"],
        "inner __close执行时outer copy仍在命名scope，close通过debug.setlocal清copy后不得留隐藏根。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55])
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/snapshot_06_observing_snapshot_overwrite.lua",
        &["debug", "gc-root", "lookup", "parallel-assignment"],
        "参数并行赋值的匿名snapshot活过missing lookup回调，lookup把owner写nil后，进入replacement时snapshot立即退休。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55])
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/release_09_copy_root_forward_exit.lua",
        &["branch", "copy", "debug", "gc-root"],
        "joined_exit可共享纯分支frame出口，observed_exit的GC suffix则必须先结束copy根。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
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
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55]),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55])
                .with_options(LuaCaseOptions {
                    retain_debug: true,
                    ..LuaCaseOptions::DEFAULT
                }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/roots_11_short_circuit_entry_gc.lua",
        &["call-result", "gc-root", "local", "short-circuit"],
        "对照直接入口call result被successor覆盖与独立saved local继续保根。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/roots_12_pure_decision_gc.lua",
        &["boolean", "call-effect", "gc-root", "short-circuit"],
        "纯test规范化不得删除低槽根，但discarded test result也不是独立lower home。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/lookup_06_lookup_root_callback.lua",
        &["callback", "copy", "gc", "lookup"],
        "lookup覆盖端点独立于callback是否静态识别为collectgarbage，并保留并行赋值旧callee快照。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/lookup_07_overwrite_home.lua",
        &["dynamic-key", "gc", "lookup", "overwrite"],
        "最终写回root home不代表中间GETTABLE也覆盖，比较显式local、直接表达式、动态key。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/gc_04_boolean_root.lua",
        &["boolean", "cdata", "gc"],
        "CALL与最终Boolean同槽不证明中间LEN覆盖root，比较named/inline/staged。",
        &[
            LuaCaseConfiguration::new(LUAJIT_ONLY),
            LuaCaseConfiguration::new(LUAJIT_ONLY).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/overwrite_07_write_retirement.lua",
        &["copy", "gc", "ignore-call"],
        "Ignore CALL留下callee函数时，后续COPY即使逻辑无用也决定旧函数退休；连续两个词法epoch至少保留一次物理覆盖。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_51),
            LuaCaseConfiguration::new(PUC_LUA_51).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_15_call_copy_owner_release.lua",
        &["call-frame", "copy", "gc", "weak-table"],
        "factory变量先保存函数再被其调用结果覆盖并清空，覆盖调用COPY旧owner不得在语句后继续保活。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/release_10_numeric_for_skip_index_release.lua",
        &["gc", "numeric-for", "scope-exit", "weak-table"],
        "1MiB对象进入跳过型数值for的初值槽后，在清空、prefix、嵌套、非零upvalue与连续两轮布局下验证索引槽退出时释放。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/release_11_write_groups.lua",
        &["gc", "label", "nil-write", "slot-group"],
        "九组局部布局逐步nil写入并穿过标签/后继块，验证清空分组不会因共享物理槽或控制流边界错保活。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/release_12_nil_scope_successor_frame.lua",
        &["frame", "gc", "scope-exit", "successor"],
        "局部对象在显式nil和scope结束后，跨后继for、赋值、条件、比较及while frame不得被旧frame继续持有。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_16_numeric_for_reused_frame.lua",
        &["argument", "capture", "gc", "numeric-for", "slot-reuse"],
        "九种数值for布局观察旧对象的精确存活窗口；参数holder由源码引用捕获断根，覆盖stripped与retained实例。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54]),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54]).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_17_snapshot_pure_end.lua",
        &["capture", "gc", "lookup", "parameter", "snapshot"],
        "参数对象复制到局部并登记weak，全局lookup通过源码引用捕获清空参数，副本仍保活到显式nil终点。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/roots_13_comparison_root_endpoints.lua",
        &["callee-lookup", "comparison", "gc", "metamethod"],
        "比较右操作数CALL结果须跨__eq及then callee lookup存活，到错误参数/后继调用准备后才释放。",
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
        "tests/case_lifetime/overwrite_08_overwrite_frame.lua",
        &["closure", "gc", "global-lookup", "slot-reuse"],
        "CLOSURE重用已退出scope的全局读取槽，闭包进入时旧lookup对象必须已经释放。",
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
        "tests/case_lifetime/roots_14_prefix_scratch_lifetime.lua",
        &["concat", "gc", "scratch-root", "table-key"],
        "nil声明前缀与CONCAT输入COPY共同结束旧全局读取scratch根，同时拼接结果继续作为嵌套表动态键。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/copy_18_mixed_table_old_callee_root.lua",
        &["callee-root", "control", "gc", "table-constructor"],
        "混合表NEWTABLE在首字段求值前覆盖旧callee槽；显式local对照则应继续持有同一旧callee。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_lifetime/close_23_close.lua",
        &["close-binding", "constructor", "gc"],
        "二十组Lua5.4生命周期覆盖to-be-closed多出口/重入/尾调用、const迭代及表构造与CALL root的释放和保留。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
];
