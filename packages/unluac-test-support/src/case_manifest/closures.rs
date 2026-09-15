//! closures 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;
pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_closures/identity_01_loop_closure_capture_slot.lua",
        &["capture-cell", "goto", "loop", "slot-identity"],
        "确保循环每轮 x 的 closure cell 与保存 closure 的结果槽不是同一 binding，同时 k 作为共享 capture 更新。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_52)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/identity_02_carried_closure_capture.lua",
        &["branch", "capture-cell", "readability"],
        "确保三个分支计算出的 needed 被返回闭包各自捕获，同时 level 保持对象引用而不是值快照。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/capture_01_captured_slot_receiver_eval.lua",
        &["eval-order", "for-binding", "receiver"],
        "先观察captured receiver槽重读，再覆盖numeric/generic for binding closure身份。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/identity_03_captured_alias_group_home_slot.lua",
        &["alias", "home-slot", "phi", "snapshot"],
        "phi别名组赋值须写回已捕获seed home，同时proxy记录赋值前reader快照。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/capture_02_child_writes_parent_capture.lua",
        &["close", "mutability", "nested-proto"],
        "子/后代proto写父capture必须回传mutability，nil入口和逐迭代cell也保留。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/capture_03_terminal_close_capture_epoch.lua",
        &["cell", "reader", "terminal", "writer"],
        "终结分支分别保留sibling写与parent后写的cell，观察两臂及不同构造实例的写入隔离。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/identity_04_luau_capture_value_reuse.lua",
        &["capture-val", "slot-reuse"],
        "CAPTURE VAL与后续物理register复用隔离。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/identity_05_branch_close_capture_epoch.lua",
        &["break", "per-iteration-cell", "while"],
        "每轮cell在fallthrough写10/20，break cleanup路径保持独立nil cell。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/capture_07_forward_capture_function_coalesce.lua",
        &["binding", "forward-function"],
        "closure捕获的前向second函数槽保持独立binding。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/flow_02_shared_terminal_closure_tail.lua",
        &["callback", "closure", "shared-tail"],
        "带两个closure的terminal tail不能复制进if/else双臂。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/capture_12_closure_capture_branch_write.lua",
        &["branch", "cell"],
        "capture后分支写1/2仍写同一父local。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/factory_12_method_decl_captured_owner.lua",
        &["capture", "method-decl", "runtime", "self"],
        "方法声明捕获外层owner时不能把捕获对象误认成self。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/capture_05_table_capture_writeback.lua",
        &["by-reference", "capture", "table-constructor", "writeback"],
        "保证捕获变量的新值先完成共享槽写回，再允许结果表字段折叠。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/capture_06_write_after_reference_capture.lua",
        &["by-reference", "capture", "parent-write", "snapshot"],
        "证明只读闭包的 ByReference 捕获仍观察闭包创建后的父级写入。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/loop_01_lua52_goto_capture_identity.lua",
        &["capture", "goto", "loop-iteration", "shared-slot"],
        "保证 backward goto 重复创建的闭包共享同一 capture 槽，而非逐轮局部。",
        &[LuaCaseConfiguration::new(LUA_GOTO_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/identity_06_close_capture_post_slot_reuse.lua",
        &["capture", "loop-scope", "physical-slot", "write-isolation"],
        "防止循环体 local 关闭后复用物理槽导致不同迭代闭包互相串写或泄漏全局。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/flow_01_captured_writeback.lua",
        &["capture", "conditional-write", "goto", "handoff"],
        "证明 nested 条件内捕获变量写回不是无条件 carried handoff。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_52)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/factory_01_luau_shared_proto_dag.lua",
        &["lexical-child", "o2", "proto"],
        "保证 O2 复用的 flat proto 展开到每个词法 child slot。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS),
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LuaCaseOptions {
                retain_debug: true,
                ignore_debug: true,
                ..LUAU_OPTIMIZED_OPTIONS
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/factory_02_luau_closure_creation_identity.lua",
        &["dupclosure", "identity", "newclosure"],
        "区分 O2 DUPCLOSURE 与 NEWCLOSURE 的每次创建身份。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/factory_03_luau_captured_shared_factory.lua",
        &["capture", "convergence", "factory", "o2"],
        "覆盖 O2 内联后带 capture DUPCLOSURE 的共同词法 owner、事件工厂和分支工厂。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LuaCaseOptions {
                recompile_rounds: Some(4),
                ..LUAU_OPTIMIZED_CONVERGENCE_OPTIONS
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/factory_04_luau_captured_shared_capture_free_dependency.lua",
        &["capture", "factory", "nested-proto"],
        "保证复合 factory 独占其零 capture dependency，同时闭包仍读取外层 value。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_CONVERGENCE_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/factory_05_luau_captured_shared_owner_dependency.lua",
        &["factory", "nan", "owner"],
        "防止同一 closure 同时被当作 factory owner 和复合 DAG dependency。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/loop_02_luau_captured_shared_repeat_condition.lua",
        &["factory", "repeat", "scope"],
        "保证 repeat body local factory 在 until 条件仍可见并每轮创建新闭包。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/loop_03_numeric_for_mutated_binding_capture.lua",
        &["capture", "global-leak", "mutable-binding", "numeric-for"],
        "保证赋值后的 numeric-for binding 捕获不回读 header phi。",
        &[LuaCaseConfiguration::new(
            MUTABLE_NUMERIC_FOR_BINDING_DIALECTS,
        )],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/factory_06_luau_captured_shared_diamond.lua",
        &["alias", "capture", "closure-dag"],
        "保证shared closure DAG的diamond occurrence保留leaf alias证明。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/loop_04_closure_self_capture.lua",
        &["numeric-for", "recursion", "self-capture"],
        "覆盖递归closure覆写loop binding及各迭代capture独立写回。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_51),
            LuaCaseConfiguration::new(PUC_LUA_54),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/capture_08_luau_self_value_capture.lua",
        &["overwrite", "self-value"],
        "保证CAPTURE VAL目标在后续同槽overwrite后仍保留自函数值。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_expectation(
            LuaCaseExpectation::LuauSelfValueCaptureCarrier {
                closure_pc: 7,
                save_pc: 9,
                overwrite_pc: 10,
                target_reg: 3,
            },
        )],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/capture_09_boolean_shell_distinct_capture_home.lua",
        &["boolean-shell", "capture", "home"],
        "证明另一物理槽的引用捕获不使dead loop-local boolean shell变得可观察。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/capture_10_boolean_shell_lua51_entry_capture_home.lua",
        &["boolean-shell", "entry-home", "vararg"],
        "确认Lua5.1隐式arg表的entry home不与dead loop shell混同。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/capture_11_boolean_shell_lua55_entry_capture_home.lua",
        &["boolean-shell", "entry-home", "named-vararg"],
        "确认Lua5.5 named vararg pack的entry home不与dead loop shell混同。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/factory_07_temp_inline_repeated_closure.lua",
        &["callback", "single-allocation", "while"],
        "防止loop condition的nested call参数每轮重复分配closure。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/flow_03_forwarded_lvalue_eval_order.lua",
        &["allocation", "capture", "closure", "lvalue"],
        "保证捕获32值的closure allocation发生在eventful lvalue __index前。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/loop_05_lua55_loop_carried_closure_effect.lua",
        &["fixed-point", "gc-root", "loop"],
        "在 Lua55 global 声明造成的 repeat 环境中，分别让 while、repeat、numeric-for、generic-for 和循环携带的 callee 经两次闭包调用传播 captured root effect，要求固定点在 condition GC 观察前保住 item。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/factory_08_lua55_returned_fresh_closure_effect.lua",
        &["call-effect", "factory", "gc-root"],
        "证明已知 factory 返回的新鲜闭包在跨函数投影后仍携带 initialize 的 captured-root 写效应，holder() 执行后 item 必须活到 repeat condition。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/scope_01_nested_capture_local_namespace.lua",
        &["local-id", "nested-closure", "repeat", "scope"],
        "构造父函数 outer 与子函数 child 可能编号相同的局部，要求孙闭包捕获只在所属 proto 命名空间解析，不能误把父级 local 当作跨 repeat 的捕获。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/scope_02_repeat_tail_safe_closure.lua",
        &["non-escaping", "readability", "repeat", "scope"],
        "证明 repeat 尾部的非逸出嵌套闭包不需要为了事件型 until condition额外生成 do 作用域，局部 value 与 hold 均未越过 condition。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/factory_09_child_root_effects.lua",
        &["call-effect", "capture", "factory", "gc-root"],
        "在同一已知 child 分析下区分 capture 的纯读、写替换、factory 返回 closure 的发布，以及 callee 作为 upvalue 再间接调用的写入/逃逸投影。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/identity_07_write_graph.lua",
        &["backedge", "branch", "capture-cell", "epoch"],
        "验证同一 close epoch 的多个闭包共享未来写入，repeat 回边产生的三个闭包共享可写 cell，而三个独立 do scope 的 close epoch 保持40/50/60系列身份。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/identity_08_creation_reads.lua",
        &["capture-cell", "creation", "snapshot", "truthiness"],
        "区分同一局部的直接读取、闭包创建时可内联快照和随后写入仍应被引用 cell 观察三种时机，防止 capture creation 被统一成单一 read。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/effects_01_captured_root_handoff.lua",
        &["allocation", "call-root", "capture", "gc"],
        "用纯{} allocation与setmetatable call-result两种producer，均让a2被get闭包捕获；清空a0/a1/a2后闭包应见nil且对象释放。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/identity_09_capture_closed_nil_slot.lua",
        &["capture-cell", "epoch", "nil", "register-reuse"],
        "旧nil capture cell关闭后，同寄存器新epoch分别复用为number17和function23，旧saved闭包仍必须返回nil。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/loop_06_tail_capture_cleanup.lua",
        &["capture", "cleanup", "goto", "numeric-for"],
        "body末尾布尔合流后的Close/JMP是正常迭代尾，不能误转continue。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/factory_10_luau_fresh_constant_capture.lua",
        &["constant", "newclosure", "vararg"],
        "NEWCLOSURE常量capture不能共享DUPCLOSURE，覆盖NaN/scalar/vararg root/selectors/phi/mutable。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY)
                .with_options(LuaCaseOptions {
                    // O0 第4次生成完成原帧保护后的声明规范化，第5次逐字节相同；其它配置不外推。
                    recompile_rounds: Some(4),
                    ..LuaCaseOptions::DEFAULT
                })
                .with_variants(&[LuaCaseVariant::LuauO0]),
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
                .with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/scope_03_debug_outer_nil_binding.lua",
        &["branch", "capture-cell", "debug", "epoch"],
        "原nil binding跨inner CLOSE，覆盖分支独立cell、共享cell、顺序cell、迭代cell、returned cell及numeric frame。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/factory_11_luau_nonvararg_fresh_capture.lua",
        &["float-bits", "identity", "newclosure"],
        "六类非vararg数值capture在不同activation中保持fresh closure且f64 bit不变。",
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
                    // O0 debug 只多一轮声明拆分；后续三次生成逐字符固定，不能外推其它配置。
                    recompile_rounds: Some(4),
                    ..LuaCaseOptions::DEFAULT
                })
                .with_variants(&[LuaCaseVariant::LuauO0]),
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
        "tests/case_closures/identity_10_cell_call_prefix.lua",
        &["call-prefix", "closed-cell", "numeric-for"],
        "已关闭循环cell不属于循环后build调用活动声明前缀。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/identity_11_closed_cell_frame_slots.lua",
        &["activation", "closed-cell", "identity", "slot-reuse"],
        "同一factory的两次activation各生成两个共享cell闭包，防止相同物理槽把前后epoch错误合并。",
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
        "tests/case_closures/scope_04_capture_scope.lua",
        &["capture-cell", "close-binding", "return", "scope"],
        "对照终端return自带capture关闭、显式do关闭及to-be-closed返回顺序，避免把整个chunk包入多余do。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/scope_05_capture_return.lua",
        &["capture-close", "chunk", "return", "scope"],
        "函数返回附带capture关闭不应被错误提升为chunk级独立do作用域。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/construction_01_nested_closure_constructors.lua",
        &["closure", "dynamic-key", "method-call", "table-constructor"],
        "动态key闭包与嵌套数组闭包在构造器原槽中创建，两个闭包组分别共享各自seed且不污染静态字段。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_closures/factory_13_closures.lua",
        &["factory", "metamethod", "recursion", "upvalue"],
        "十二组闭包覆盖counter、递归、工厂链、重绑定、循环capture及call-result原位覆盖。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
];
