//! tables 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;
pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_tables/fields_01_global_table_install_readability.lua",
        &["callbacks", "inline-alias", "table-constructor"],
        "把全局表字段安装恢复为直接构造器与函数字段，同时内联 make_level 的三个参数别名。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/order_01_table_checkpoint_new_pending_rollback.lua",
        &["constructor", "eval-count", "field-order"],
        "候选中新建/搬移的整数字段在失败回滚后仍保持2后1的写入边界和值快照。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/indexing_01_generic_for_break_tail_binding.lua",
        &["binding", "break", "generic-for"],
        "break tail保持index/field binding作用域并正确增删forceFields。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/multireturn_01_discarded_table_open_tail.lua",
        &["discarded-rhs", "eval-count", "open-pack"],
        "多赋值丢弃的RHS仍须求值table开放尾一次。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/order_02_table_constructor_field_order.lua",
        &["field-order", "metamethod", "snapshot"],
        "pending整数key保持binding快照与元方法求值顺序。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/setlist_03_table_setlist_trailing_short_circuit.lua",
        &["setlist", "short-circuit"],
        "SETLIST尾部短路producer折回构造器且false转0。",
        &[LuaCaseConfiguration::new(LUA_51_AND_LUAU)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/setlist_04_table_setlist_nested_producer.lua",
        &["nested-call", "setlist"],
        "SETLIST队首first的依赖与后续whilst/block共同进入构造器。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/setlist_08_table_setlist_binary_producer.lua",
        &["binary-op", "call-choice", "setlist"],
        "嵌套字段消费w*1.5 producer，函数选择表达式保持调用。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/multireturn_05_table_trailing_multivalue_boundary.lua",
        &["field-write", "multiret"],
        "开放多返回构造器结束后label字段不能被吸入同一SETLIST。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/constructor_01_table_constructor_eval_ownership.lua",
        &[
            "evaluation-order",
            "key-value",
            "shared-value",
            "table-constructor",
        ],
        "用四种 producer/field 组合证明移入构造器的值仍只求值一次且遵守原求值顺序。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/order_03_table_constructor_pending_alias.lua",
        &["alias", "numeric-key", "overwrite", "table-constructor"],
        "证明构造器待折叠的整数字段不能跨越可能别名的后续写，并保留最后写胜出。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/setlist_01_table_constructor_open_overlap.lua",
        &["call-count", "multi-return", "overlap", "setlist"],
        "验证开放多返回 list 写只有实际产出值时覆盖旧后缀，零返回时必须保留旧字段。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/indexing_02_boolean_shell_table_lvalue_order.lua",
        &[
            "boolean-shell",
            "condition-order",
            "mutation",
            "table-lvalue",
        ],
        "保证条件调用先改变 holder.target，再求值所选 arm 的 table 地址。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/setlist_02_deferred_open_setlist.lua",
        &[
            "multi-return",
            "setlist",
            "short-circuit",
            "runtime-observer",
            "gc",
            "call-frame",
        ],
        "恢复完整 open SETLIST 展开帧及必须内联的原闭包调用，保持输入覆盖端点和调用层。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/order_04_table_constructor_handoff_snapshot.lua",
        &["ast", "base-snapshot", "call-effect", "constructor"],
        "保证构造器内调用先把 target 换成新表，随后 handoff 字段写使用新的 base。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/constructor_02_table_candidate.lua",
        &["constructor", "early-stop", "nested-block"],
        "保证 block 早停后仍遍历并恢复后序嵌套表构造候选。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/order_05_lvalue_key_deferred_base.lua",
        &["evaluation-order", "length", "lvalue", "metamethod"],
        "覆盖append key与upvalue/complex base在不同方言的实际求值顺序。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/setlist_05_adjacent_uncertain_setlist.lua",
        &[
            "debug",
            "false",
            "fixed-list",
            "nil",
            "dynamic-key",
            "evaluation-order",
        ],
        "相邻 fixed SETLIST 恢复字段/动态索引构造器，保留求值次数、顺序及 nil/false 槽。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/setlist_06_adjacent_open_setlist.lua",
        &["capture", "open-list", "vararg"],
        "保证相邻open SETLIST保留vararg标量截断、尾展开和owner capture。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(LUAU_ONLY),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/fields_02_function_sugar_table.lua",
        &["constructor", "method", "receiver", "vararg", "gc-root"],
        "vararg receiver与表字段调用保留GETFIELD后COPY，不能用SELF预写改动旧scratch根。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(1),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/setlist_07_table_constructor_local_acceptance.lua",
        &["arity", "nil", "setlist"],
        "保证fixed call可返回nil时raw SETLIST不拆成SETTABLE。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/capture_01_constructor_call_capture.lua",
        &["call", "closure", "constructor"],
        "保证constructor-call folding保留由field closure捕获的local。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/fields_03_constructor_fields_other_return.lua",
        &["constructor", "field", "identity"],
        "保证折叠constructor fields不删除或改写无关return。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/multireturn_02_constructor_value_arity.lua",
        &["call", "constructor", "loop", "open-tail"],
        "系统验证constructor安装field后，标量call initializer及多返回开放尾在call/if/两类for消费者中的宽度。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/calls_01_constructor_literal_args.lua",
        &["call", "constructor", "literal"],
        "允许稳定prefix/suffix实参包围constructor handoff而不改位置。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/setlist_09_captured_open_constructor_owner.lua",
        &["capture", "local-id", "multi-return", "setlist"],
        "保证开放SETLIST折叠后，被闭包捕获的constructor owner仍保持同一LocalId。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/constructor_03_constructor_nil_local_prefix.lua",
        &["constructor", "dependency", "nil-local", "ordering"],
        "区分独立nil local与被字段读取的nil local对empty-table字段折叠的阻断能力。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/constructor_04_constructor_eventless_assignment_prefix.lua",
        &["assignment", "captured-local", "constructor", "ordering"],
        "区分eventless captured-local写与字段真实读取该local时的constructor折叠边界。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/setlist_10_open_constructor_multiple_setlists.lua",
        &["multi-return", "open-constructor", "setlist", "wide-table"],
        "验证固定SETLIST批次之后的最终开放批次仍折叠成单个table constructor。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/capacity_01_indexed_array_capacity.lua",
        &["nil-hole", "tdup", "tnew"],
        "枚举 a/b/c 的8种 nil/false/value 组合，覆盖纯数组1–3项、混合0键/record、显式整数键与模板 nil 前缀，固定 TNEW/TDUP 数组布局穿过 LowInstr→HIR→constructor commit。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Luajit])],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/multireturn_03_call_root_handoff.lua",
        &["call-result", "constructor", "gc-root", "multi-return"],
        "比较开放 list 字段与 keyed 字段消费 object() 多返回时的 root handoff：list 尾调用扩展出 index=3 到第4槽，keyed 每次只取首值；前一对象必须活过后续 object 调用。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/template_01_runtime_table_constants.lua",
        &["array-capacity", "runtime-binding", "tdup"],
        "固定 true/nil/string/arithmetic/comparison 等经 local runtime binding 进入数组时不能被误静态化为 TDUP 模板，并覆盖直接/嵌套比较与运行时 record key。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Luajit])],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/template_02_template_runtime_fields.lua",
        &["array-capacity", "string-dump", "template"],
        "通过 string.dump/load 强制源码基线也走序列化模板，检查模板初始容量不能因后续 runtime 字段被误常量化而扩大；覆盖 boolean、算术、比较、嵌套、hash template 与 record。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Luajit])],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/capacity_02_template_hash_keys.lua",
        &["hash-capacity", "sparse-key", "string-dump"],
        "区分模板原始键集合与构造后字段写入，覆盖稀疏5/8键、record键、静态nil marker、运行时name键和0槽，防止把新 key 静态化后提前改变 hash/array 扩容。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Luajit])],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/multireturn_04_table_result_nil_shape.lua",
        &[
            "constructor",
            "metamethod",
            "multiret",
            "nil-hole",
            "grouped-initializer",
            "nested-array",
        ],
        "覆盖非nil字段恢复、可能nil保留allocation hole、先dense后clear的历史、三槽与method owner、numeric records及开放多返回mixed batch；多目标声明共享缓冲的顺序、零返回和nil空洞，模板字段中的完整数组与空表。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/template_03_luau_table_template.lua",
        &["duptable", "evaluation-order", "record-field"],
        "固定DUPTABLE常量/动态record字段、nil占位、两次observe顺序，以及构造后普通/函数字段增长均不丢模板容量语义。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Luau])],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/capacity_03_luau_table_preallocation.lua",
        &["capacity", "multiret", "newtable"],
        "覆盖NEWTABLE string key命名化、function sugar扩展、numeric/sparse容量，以及call/vararg开放尾字段在enabled两态的长度与值。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Luau])],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/indexing_03_pending_integer_key_shadow.lua",
        &["integer-key", "overwrite", "scale", "unknown-key"],
        "区分未知k在整数3写入前/后及重复3写的遮蔽顺序，并以8个未知键对8个17–24待定字段压力共享位置事实。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/constructor_05_constructor_nil_prefix.lua",
        &["call-barrier", "capture", "initializer", "nil-decl"],
        "八槽nil声明随后赋值并写入result，要求捕获get cell保留更新；另证明可调用initializer阻断更早nil事实，value最终为final。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/constructor_06_constructor_run_boundaries.lua",
        &["callee", "constructor", "method", "multi-return"],
        "8个带read闭包的返回值构造run不可跨非call return或后续callee起点错误合并。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/fields_04_constructor_field_targets.lua",
        &["callee", "capture", "constructor", "function-field"],
        "8个表交替用assignment/function sugar安装read，并以captured a/b相互引用，要求同一constructor call正确消费字段target。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/constructor_07_closure_table_results.lua",
        &["constructor", "local-function", "normalization", "vararg"],
        "递归自捕获恢复local function，同时覆盖嵌套constructor、整数键、vararg/多返回及无序表摘要归一化。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/fields_05_constructor_roots.lua",
        &["constructor", "escape", "gc", "metamethod"],
        "区分可折叠私有子表、持外部resource及已escape owner；另观察index/len顺序。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/fields_06_luajit_field_observer.lua",
        &["cdata", "field-key", "metamethod"],
        "cdata __eq把key从left改right，前后字段lookup必须使用各自快照。",
        &[LuaCaseConfiguration::new(LUAJIT_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/fields_07_table_fields.lua",
        &["constructor", "escape", "parallel-write", "weak-key"],
        "深层私有字段折叠与escaped/inserted/weak/callback/neighbor/captured拒绝路径完整对照。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/template_04_template_nil_slot_order.lua",
        &["capture", "evaluation-order", "nil-slot", "template"],
        "nil槽可恢复数组字段但不得跨runtime字段重排，覆盖forward/reverse/record barrier/open empty及capture读时点。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/calls_02_constructor_call_frames.lua",
        &["call-frame", "constructor", "gc", "order"],
        "覆盖open宽度、嵌套record求值序、callee snapshot、dispatch roots、previous activation、record scratch、callable number及branch may-union。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_51),
            LuaCaseConfiguration::new(PUC_LUA_51).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/calls_03_constructor_frame.lua",
        &["callee", "constructor", "gc", "phi"],
        "callee与tag都经phi时constructor仍属于receive参数区，形参清空但call未返回的窗口可观察。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/indexing_04_luau_array_lookup_initializer.lua",
        &["callee-snapshot", "capture", "nan"],
        "数组buffer低槽初始化保留NaN capture身份、box读取、旧callee参数快照与nil槽。",
        &[
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_OPTIMIZED_OPTIONS),
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LUAU_OPTIMIZED_OPTIONS
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/template_05_luau_template_initialization_recompile.lua",
        &[
            "convergence",
            "duptable",
            "fastcall",
            "concat",
            "upvalue",
            "source-frame",
        ],
        "隐式0与显式字段不逐轮重复，覆盖上值拼接帧、重复字段顺序、观察初始化resource、fastcall alias及open assert。",
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
        "tests/case_tables/constructor_08_array_generic_header.lua",
        &["array", "generic-for", "header"],
        "六层嵌套数组中的最内层对象直接作为Luau泛型for迭代头，保护嵌套GETTABLE与迭代准备的归属。",
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
        "tests/case_tables/template_06_template_record_call_order.lua",
        &["call-order", "duplicate", "record-field"],
        "对照先构造后覆盖与同一构造器重复记录键，验证被覆盖字段的调用仍按a、b、c顺序执行。",
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
        "tests/case_tables/indexing_05_indexed_concat_snapshot.lua",
        &[
            "concat",
            "evaluation-order",
            "indexed-assignment",
            "metamethod",
        ],
        "索引赋值先算key再捕获目标表，RHS的name与tostring回调改写同名log cell时仍写入原target快照。",
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
        "tests/case_tables/indexing_06_lookup_assignment_frames.lua",
        &["arithmetic", "call-frame", "dynamic-key", "nested-index"],
        "多层目标表、动态索引、普通算术与嵌套string调用在完整原槽frame中读写正确位置。",
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
        "tests/case_tables/indexing_07_indexed_arithmetic_order.lua",
        &["gc", "indexed-assignment", "metamethod", "target-snapshot"],
        "索引赋值中目标表应在算术元方法前快照，而动态key在元方法改写后读取；另验证两级lookup算术中间根。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/constructor_09_table_initializer_after_call.lua",
        &[
            "call-frame",
            "list-field",
            "record-field",
            "table-constructor",
        ],
        "前一CALL用过的槽立即成为混合表声明目标，list、record及动态表key的同槽复用不得拆散initializer。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/constructor_10_tables.lua",
        &["closure", "constructor", "dynamic-key", "nested-index"],
        "九组表基础覆盖混合构造器、元表、深层读写、动态key、嵌套调用和构造器闭包。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/constructor_11_nested_table_before_compaction.lua",
        &["constructor", "nested-table", "local-pressure"],
        "大型嵌套构造器在物理槽复用前保留完整 producer 身份及所有数组元素。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_51),
            LuaCaseConfiguration::new(PUC_LUA_51).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_tables/capture_02_table_nil_batch.lua",
        &["capture", "nil-hole", "setlist"],
        "原全局安装与后续同槽表初始化保留分配及捕获时序，nil batch 的内容和长度保持一致。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_51),
            LuaCaseConfiguration::new(PUC_LUA_51).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
];
