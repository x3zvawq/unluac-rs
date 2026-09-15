//! runtime 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;
pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_runtime/locale_01_puc_locale_string_order.lua",
        &["locale", "ordering", "string"],
        "禁止PUC方言在可变collate locale下常量折叠字符串排序。",
        &[LuaCaseConfiguration::new(PUC_LUA_ALL)],
    ),
    LuaCaseDefinition::new(
        "tests/case_runtime/gc_01_value_predicate_gc.lua",
        &["boolean", "callee-lookup", "gc", "predicate"],
        "区分Boolean值写回与仅谓词极性，覆盖double/single/local/saved/copied/compared槽。",
        &[
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS),
            LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_runtime/errors_01_runtime.lua",
        &[
            "coroutine",
            "metamethod",
            "multi-return",
            "pcall",
            "return-frame",
            "xpcall",
        ],
        "七组运行库控制转移覆盖pcall/xpcall成功失败、混合返回帧、算术元方法的操作数身份与结果宽度、coroutine yield/resume和while退出。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_runtime/ffi_01_luajit_cdata_ffi_numeric_matrix.lua",
        &["cdata", "ffi", "goto"],
        "十组LuaJIT基础覆盖LL/ULL cdata、虚数、FFI struct/metatype、bit库、十六进制浮点、goto和jit.status。",
        &[LuaCaseConfiguration::new(LUAJIT_ONLY)],
    ),
];
