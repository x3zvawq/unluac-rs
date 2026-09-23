//! operators 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;
pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_01_adversarial.lua",
        &["numeric-for", "short-circuit", "truthiness"],
        "同时固定循环元素含 nil/false 时的 and/or 值链与 elseif 中 max 三元链，避免把 Lua 真值传播简化成布尔值。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_02_short_circuit_value_merge.lua",
        &["eval-count", "short-circuit", "table-index"],
        "将 assert 参数里的三段 and 值链恢复为表达式，避免退化成嵌套 if 壳。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_52),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_ALL_OPTIMIZATION_VARIANTS),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_03_bvm_short_circuit_tail.lua",
        &["branch", "eval-order", "short-circuit"],
        "将嵌套 BVM 短路 tail 保持为结构化 if/表达式，并保存 mark 的求值顺序。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/metamethod_01_puc54_metamethod_operand_flip.lua",
        &["eval-order", "integer-op", "metamethod"],
        "覆盖 MMBINI/MMBINK flip 位，使常量与对象在算术、位运算和移位中的源码操作数顺序保持不变。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/order_01_observable_expression_reads.lua",
        &["eval-count", "metamethod", "short-circuit"],
        "不可删的global/table/comparison/while读取须保留实际次数与Lua值语义。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_04_truthy_ternary_hir_owner.lua",
        &["closure", "hir", "truthiness"],
        "truthy ternary臂交换应在HIR完成并保留两函数值。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/comparison_03_negated_relational_metamethod.lua",
        &["nan", "negation"],
        "not-less关系不能改成<=，否则NaN语义变化。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_12_decision_value_truthiness.lua",
        &["eval-order", "truthiness"],
        "value context保留nil/false/0差异及共享continuation求值次数。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_05_raw_branch_value_before_locals.lua",
        &[
            "evaluation-order",
            "mechanical-temp",
            "multi-return",
            "short-circuit",
        ],
        "要求 raw branch value 在 locals 物化前消解机械 guard temp，同时保持嵌套短路调用顺序。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_06_phi_short_value_merge.lua",
        &[
            "call-count",
            "phi",
            "return-frame",
            "shared-fallback",
            "short-circuit",
        ],
        "覆盖短路 phi、同槽条件返回帧与1296组参数值/身份，保留共享fallback和重复调用次数。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_07_value_single_eval.lua",
        &[
            "callee-snapshot",
            "method-receiver",
            "short-circuit",
            "single-eval",
        ],
        "系统观察 branch-value 折叠后每个操作数只求值一次，并在兄弟参数变异前快照 callee、普通参数和方法 receiver。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/order_02_repeat_prefix_ops.lua",
        &["evaluation-count", "metamethod", "repeat", "unused-result"],
        "证明 repeat 前缀中未使用的二元、单元和连接运算仍可能调用元方法，不能作为死结果删除。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/comparison_01_negated_compare.lua",
        &[
            "comparison",
            "metamethod",
            "nan",
            "call-order",
            "dynamic-key",
        ],
        "验证 JIT/Luau 比较极性、NaN 与元方法方向次数，并观察完整参数帧中比较、CALL 与动态索引的精确求值顺序。",
        &[
            LuaCaseConfiguration::new(LUAJIT_ONLY),
            LuaCaseConfiguration::new(LUAU_ONLY),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/equality_01_materialize_preserves_eval.lua",
        &[
            "arithmetic",
            "effectful-call",
            "equal-arms",
            "gc-root",
            "materialize",
            "recompile",
            "short-circuit",
        ],
        "确认同值条件保留求值和后继弱表根观察，完整算术调用帧不阻塞再编译后的表构造。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_08_fallback_value_merge.lua",
        &["fallback", "multi-return", "short-circuit", "single-pass"],
        "防止嵌套短路共享fallback值合流伪装single-pass break。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_09_right_associated_shared_fallback.lua",
        &["association", "logical", "shared-value"],
        "固定右结合短路式的共享fallback。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_10_simplify.lua",
        &["allocation", "number", "short-circuit", "vararg"],
        "系统覆盖occurrence级逻辑化简的轨迹、标量宽度、对象身份及Luau数值语义。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_O0_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/arithmetic_01_decision_numeric_equality.lua",
        &["equality", "float", "integer", "representation"],
        "保留整数/浮点数值相等时的两次原比较以及返回值的数值表示。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/order_03_loop_lookup_eval_count.lua",
        &["metamethod", "single-eval", "while"],
        "保证__index快照不被loop header逐轮重求值。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/discard_01_safe_truthiness.lua",
        &["dead-value", "gc-root", "truthiness", "vararg"],
        "保留原NOT、显式比较及其分支，以及and/or/vararg潜在对象根。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/bitwise_01_safe_integer_ops.lua",
        &["bitwise", "dead-value", "integer"],
        "保留原比较、短路路径与 floor/mod/bitwise 运算，不按恒值删除字节码操作。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_53)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/discard_02_safe_literal_ops.lua",
        &["arithmetic", "error", "literal"],
        "保留原 literal 算术、字符串长度与显式检查，并观察数字长度、异型排序的错误。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_O0_ONLY),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/discard_03_safe_primitive_equality.lua",
        &["dead-value", "equality", "gc-root", "nil", "primitive"],
        "保留无读纯比较及其原槽覆盖，验证旧弱表根仍在相同时点释放。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/equality_02_luajit_cdata_equality.lua",
        &["cdata", "metamethod"],
        "证明LuaJIT cdata与nil比较即使结果未用仍调用__eq，不能丢弃。",
        &[LuaCaseConfiguration::new(LUAJIT_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/bitwise_02_reject_integer_op_errors.lua",
        &["bitwise", "division-zero", "integer", "metamethod"],
        "零除数、浮点bitnot错误及动态整数运算元方法的次数和顺序不能因结果无读而删除。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_53)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/equality_03_luajit_cdata_equality_branch.lua",
        &["branch", "cdata", "metamethod"],
        "保证branch和逻辑重复读取中的cdata equality各自保留元方法调用。",
        &[LuaCaseConfiguration::new(LUAJIT_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/comparison_02_bytewise_string_order.lua",
        &["constant-fold", "ordering"],
        "保留 bytewise 方言的两个原字符串比较，运行结果仍为 false/false。",
        &[
            LuaCaseConfiguration::new(LUAJIT_ONLY),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_O0_ONLY),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/equality_04_mismatched_primitive_equality.lua",
        &["constant-fold", "primitive"],
        "保留跨 nil/boolean/string/number 类型的原 equality，并验证结果。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_O0_ONLY),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/arithmetic_02_binary64_mixed_numeric.lua",
        &["binary64", "float", "integer", "ordering"],
        "验证 binary64 方言保留 mixed numeric equality/order 与原结果。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Luajit]),
            LuaCaseConfiguration::new(LUAU_ONLY).with_variants(LUAU_O0_ONLY),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/arithmetic_03_puc_mixed_numeric.lua",
        &["float", "integer64", "rounding"],
        "防止PUC 64位整数比较通过转f64舍入错误决定。",
        &[LuaCaseConfiguration::new(&[
            LuaCaseDialect::Lua53,
            LuaCaseDialect::Lua54,
            LuaCaseDialect::Lua55,
        ])],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/order_04_call_root_effectful_rhs.lua",
        &["call-root", "capture", "metamethod", "rhs"],
        "验证same-home call root与后续有副作用RHS融合时仍保持make、rhs、add顺序和覆盖前身份。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/concat_01_operand_root_slots.lua",
        &["concat", "gc-root", "lookup-order", "metamethod"],
        "覆盖 CONCAT 右端槽、中间覆盖槽、后继表达式复用右端 temp，以及 alias compression 后 index 从左到右、concat metamethod 从右到左的顺序。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_11_shared_expression_value_facts.lua",
        &["evaluation-count", "gc-root", "metamethod", "truthiness"],
        "区分表达式正常结果事实与求值事件：保留 nil/false 差异、选择数值的 mark 次数、算术/一元/比较 metamethod 结果与次数、error 路径，以及批次临时对象跨后继比较的根。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAJIT_ONLY).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_13_shared_result_values.lua",
        &["identity", "metamethod", "nil", "truthiness"],
        "固定正常结果事实保留nil/false、object rawequal、0真值及not包裹算术/长度/元方法结果，不能统一折成boolean常量而跳过运算。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/order_05_pure_assignment_suffix.lua",
        &["assignment", "not-chain", "repeat", "snapshot"],
        "纯依赖链移入字段赋值时保留key/lookup事件前快照、capture cell及回边多读。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS),
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/folding_01_short_circuit_constant_snapshot.lua",
        &["gc-root", "metamethod", "short-circuit", "snapshot"],
        "prefix/suffix短路常量快照跨无binding suffix保持，同时错误类型、比较元方法次数与captured参数写入不变。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/metamethod_02_result_gc_roots.lua",
        &["binary", "concat", "gc-root", "metamethod"],
        "binary/unary/concat/overwrite/branch/return链的元方法结果跨后继运算和观察保持正确root终点。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_14_short_circuit_root_frontier.lua",
        &["lookup", "saved-local", "short-circuit", "trace"],
        "直接call覆盖证书不能外推到lookup或独立saved local，并保留nil/false方向。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_15_short_circuit_frontier.lua",
        &["lookup", "short-circuit", "trace", "two-calls"],
        "两个CALL间TEST不写result home，覆盖证书必须覆盖所有后续路径。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_16_logical_atoms.lua",
        &["short-circuit", "vararg", "width"],
        "五个短路位的vararg在单值位置只取入口首值。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/folding_02_indexed_logical_factors.lua",
        &["enumeration", "factoring", "identity", "short-circuit"],
        "保留非相邻分支的原比较次数与顺序，值级or也不能按索引命中交换顺序。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(LUAU_ONLY),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/concat_02_native_concat_frames.lua",
        &["concat", "gc", "metamethod", "order"],
        "concat operand左到右求值、元方法右到左合并并观察a/b/c根，比较joined/separated/stored。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/comparison_04_ordered_comparison_snapshots.lua",
        &["metamethod", "nan", "operand-order", "ordered-comparison"],
        "验证大于/大于等于降为反向小于/小于等于时元方法参数翻转正确，同时覆盖普通方向与NaN结果。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/comparison_05_comparison_upvalue_preparations.lua",
        &["call-frame", "comparison", "numeric-for", "upvalue"],
        "同一upvalue captured的两次比较读取必须各自绑定本轮原槽与make调用，不能按变量名复用准备证书。",
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
        "tests/case_operators/comparison_06_comparison_literal_preparations.lua",
        &["call-frame", "comparison", "literal", "numeric-for"],
        "比较左侧的大数值或字符串字面量占原低槽，后续tonumber/普通call准备必须覆盖此前scope观察根。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/boolean_17_operand_preparations.lua",
        &["comparison", "gc", "metamethod", "nested-index"],
        "比较左操作数的长度、算术和两级索引准备链在普通值及元方法两组中保持各自原槽，并在右侧CALL前后正确交接旧根。",
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
        "tests/case_operators/order_06_frame_preparations.lua",
        &["concat", "dynamic-key", "gc", "method-call"],
        "动态表键、拼接及SELF方法三种左操作数按原准备顺序覆盖scratch根，并以普通与元方法版本验证交接位置。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_54),
            LuaCaseConfiguration::new(PUC_LUA_GE_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/comparison_07_call_comparison_low_operand.lua",
        &["call", "comparison", "metamethod", "physical-root"],
        "IIFE CALL结果进入低槽比较时保留算术中间对象根，同时后续captured读取必须发生在替换CALL之后。",
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
        "tests/case_operators/order_07_concat_call_fallback.lua",
        &["concat", "coroutine", "open-return", "short-circuit"],
        "CONCAT操作数中的call单值结果与or/and备用值共享槽，覆盖callee副作用、快照、多返回截断和yield恢复。",
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
        "tests/case_operators/boolean_18_expr.lua",
        &[
            "identity",
            "multi-return",
            "precedence",
            "short-circuit",
            "side-effect",
            "truth-table",
            "truthiness",
        ],
        "以8/16/8组真值表及nil、0、空串和表身份验证布尔优先级、深层选择、双返回表索引与短路事件顺序。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAJIT_ONLY).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(LUAU_ONLY).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_operators/bitwise_03_lua53_integer_bitwise_matrix.lua",
        &["bitwise", "closure", "floor-division"],
        "七组Lua5.3整数能力覆盖位运算、整除、浮点混合、方法表、capture、分发循环和位非管线。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_53)],
    ),

];
