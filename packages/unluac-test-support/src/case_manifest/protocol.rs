//! protocol 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;
pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_protocol/compatibility_01_lua51_legacy_arg_table.lua",
        &["arg-table", "nested-function", "vararg"],
        "恢复 Lua 5.1 隐式 arg 表，并区分嵌套 consumed 使用 ... 后不再填充外层 arg 表的行为。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/varargs_01_lua55_anonymous_vararg.lua",
        &["ast-metric", "binding", "vararg"],
        "防止 Lua 5.5 PF_VAHID 被误恢复为带名字的 vararg binding。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/compatibility_02_global_operands.lua",
        &["binding", "global", "opcode"],
        "验证 Luau GETGLOBAL/SETGLOBAL 按 A/C 字段解码，不误生成局部声明。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/varargs_02_lua51_vararg_fixed_results.lua",
        &["fixed-width", "vararg"],
        "验证 OP_VARARG 的 B 字段按 B-1 解释，只写 first 而不覆盖 adjacent untouched。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/metadata_01_lua55_abs_line_info_layout.lua",
        &["line-info", "stress"],
        "以160项源码行跨度验证Lua5.5绝对行号表按原生int对读取。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_GE_55).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/varargs_03_explicit_value_pack.lua",
        &["generic-for", "method", "multiret", "vararg"],
        "系统覆盖open tail与括号固定值在return/table/vararg/iterator/close/method中的宽度。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/varargs_04_luau_import_open_pack.lua",
        &[
            "fastcall",
            "open-pack",
            "snapshot",
            "runtime-observer",
            "call-frame",
            "table-lookup",
            "metamethod",
        ],
        "GETIMPORT/FASTCALL保留完整返回宽度及saved argument；低槽索引结果恢复高槽CALL，外部环境核对参数与索引元方法顺序。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/varargs_05_vararg_open_pack_setup.lua",
        &["callee-setup", "vararg"],
        "VarArg open tail跨direct/captured callee setup保持参数。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/varargs_06_luau_open_pack_callee_move.lua",
        &["call", "callee-move"],
        "open producer后的单callee Move不截断owner。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/loops_01_luau_unreachable_numeric_for_control.lua",
        &["infinite-loop", "numeric-for", "unreachable"],
        "外层零迭代时内层FORNLOOP控制块不可达仍须解码为for/while。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/loops_02_degenerate_generic_scope.lua",
        &["close", "generic-for", "register-scope"],
        "固定 Lua5.5 退化 generic-for 立即 break 时，post-loop 寄存器不得被误解释为迭代绑定。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/loops_03_tforprep_swap.lua",
        &["generic-for", "iterator-pack", "tforprep"],
        "确认 Lua5.5 TFORPREP 交换前的 state/control/closing 才构成源码 iterator pack。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/close_01_errnnil_tbc.lua",
        &["close", "error-order", "global-decl"],
        "固定 Lua5.5 ERRNNIL 与 TBC 初始化在原位置即可抛错，不能被当作无效语句清除或重排。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/recovery_01_lua51_unsupported_island_contract.lua",
        &["permissive", "residual", "strict"],
        "以动态注入的双入口循环验证 Strict 拒绝和 Permissive 诊断岛最终门禁。",
        &[LuaCaseConfiguration::new(PUC_LUA_51).with_expectation(
            LuaCaseExpectation::UnsupportedIsland {
                jump_pc: 7,
                target_pc: 13,
            },
        )],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/compatibility_03_method_protocol.lua",
        &["dynamic-chunk", "method-call", "receiver-snapshot"],
        "通过专用动态 chunk 和普通源码验证 LuaJIT split method setup 的 receiver 快照与调用种类。",
        &[LuaCaseConfiguration::new(LUAJIT_ONLY)
            .with_expectation(LuaCaseExpectation::LuaJitMethodProtocol)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/metadata_02_debug_policy.lua",
        &["debug", "metadata", "naming"],
        "保证保留的 debug section 在 ignore 模式不影响命名或注释。",
        &[
            LuaCaseConfiguration::new(ALL_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ignore_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/recovery_02_ignore_debug_keeps_validation.lua",
        &["debug", "negative", "validation"],
        "确认 ignore-debug 不能绕过损坏 debug 尾段的严格校验。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)
            .with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            })
            .with_expectation(LuaCaseExpectation::InvalidDebugStillRejected)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/recovery_03_proto_failure_recovery.lua",
        &["children", "permissive", "proto", "strict"],
        "验证根HIR失败占位时Strict拒绝而Permissive保留诊断及直接子proto。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)
            .with_expectation(LuaCaseExpectation::ProtoFailureRecovery)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/globals_01_decl_guards.lua",
        &["close", "global-decl", "lifetime", "order"],
        "全面验证global声明的seed顺序、捕获身份、物理根、词法gate和collective边界。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/globals_02_branch_control_diagnostic.lua",
        &["diagnostic", "global-decl", "unreachable"],
        "保证恒定未选arm的global声明不执行且词法效力不外泄。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/globals_03_lua55_multi_global_decl.lua",
        &["metamethod", "write-order"],
        "禁止合并singleton global声明时反转环境写顺序。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/globals_04_lua55_global_nested_callee.lua",
        &[
            "environment",
            "gc",
            "multi-return",
            "tail-callee",
            "write-order",
        ],
        "根环境与局部_ENV下嵌套调用保留global双返回、逆序probe/store及重复目标报错前的求值和存活。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/globals_05_lua55_mixed_global_rhs.lua",
        &["err-nnil", "global", "mixed-rhs"],
        "要求fixed call仅作mixed global declaration后缀时不能错误抽成独立声明。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])
            .with_expectation(LuaCaseExpectation::GlobalDeclResidual)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/globals_06_merge_across_global_decl.lua",
        &["global", "multi-return", "must-def"],
        "验证Lua5.5 global声明不会抹除其后分支合流处result的must-def事实。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/close_02_lua55_repeat_collective_scope.lua",
        &["close", "gc", "global", "repeat"],
        "验证Lua5.5 repeat条件所需collective global gate仅覆盖真实根和属性，并不被无关条件事实整体禁用。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/globals_07_lua55_unselected_global_arm.lua",
        &["constant-branch", "gc", "global"],
        "验证未选中的global声明与GC根逻辑不会迫使已证明常量分支保留if壳。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/globals_08_lua55_singleton_global_hir_owner.lua",
        &["call-result", "global-decl", "hir-owner"],
        "固定 Lua55 单结果调用初始化应直接恢复为 global singleton_target = make_value()，而不是把结果留给后层拼接或 residual。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/globals_09_lua55_environment_identity.lua",
        &["environment", "global-decl", "keyword-key"],
        "固定 Lua55 中 _ENV 是环境身份而非待补 global：同时覆盖关键字键 end 的 bracket 写入与 _ENV 自指字段写入，禁止生成 global _ENV 声明。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/loops_04_lua55_repeat_collective_certificate.lua",
        &["gc-root", "global-gate", "repeat"],
        "同时固定安全 repeat 后缀可由 collective global<const> * 覆盖，而闭包逸出 item 的 unsafe 后缀仍须保根到 until 观察；还要求显式 print global gate 出现在 unsafe body 之前。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/loops_05_lua55_repeat_condition_global_gate.lua",
        &["condition", "global-gate", "repeat"],
        "证明 repeat body 内 collective global<const> * 不覆盖 until condition 对 type 的缺失 global，type 必须在 collective gate 之前单独声明。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/globals_10_ast_scope_checkpoints.lua",
        &["global", "scope", "shadow"],
        "在Lua55中串联global初始化IIFE、嵌套collective gate、递归global function、local遮蔽递归、repeat condition声明与method，固定AST scope checkpoint分隔各名称权限。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55]),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55]).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/loops_06_permission_checkpoints.lua",
        &["closure", "global-gate", "repeat"],
        "覆盖repeat body closure、其内嵌repeat、until IIFE内repeat及两个peer repeat之间的global权限checkpoint，防止权限状态跨函数或兄弟循环泄漏。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55]),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55]).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/globals_11_lua55_function_target_global_gate.lua",
        &["function-sugar", "global-gate", "method"],
        "首次全局访问从函数字段target读取开始时，collective gate必须先于box.f/box:read定义且不能额外声明box。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/globals_12_lua55_global_missing_promotion.lua",
        &["global-decl", "order", "read-before-write"],
        "先读后写的item2/item4只生成可写global并按首次写4→2排序，其余只读名归const声明。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55])],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/metadata_03_function_expression_comments.lua",
        &["comments", "function-expression", "iife", "metadata"],
        "九个函数定义入口都附着proto元信息，尤其表达式函数注释不得吞掉end、逗号或IIFE调用后缀。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/metadata_04_nested_function_comment_placement.lua",
        &["comments", "nested-function", "proto-order"],
        "单一父子函数树约束表达式父函数和局部child的proto注释归属及顺序，排除兄弟proto排序干扰。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/compatibility_04_table_remove.lua",
        &["builtin", "metamethod", "raw-access"],
        "LuaJIT LJLIB_LUA table.remove必须走raw opcode并绕过__index/__newindex，与普通Lua索引实现形成正反对照。",
        &[LuaCaseConfiguration::new(LUAJIT_ONLY)
            .with_expectation(LuaCaseExpectation::LuaJitBuiltinTableRemove)],
    ),
    LuaCaseDefinition::new(
        "tests/case_protocol/validation_01_readability_assertion_protocol.lua",
        &["ast-count", "debug-mode", "expectation", "selector"],
        "自举验证文本计数、AST节点计数、proto/dialect/debug/variant selector及table字段分类不会把字符串或子proto误计。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54),
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ignore_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
];
