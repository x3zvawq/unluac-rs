//! syntax 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;
pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_syntax/globals_01_keyword_table_access.lua",
        &["env", "keyword", "table-index"],
        "确保环境表中的关键字 key `end` 始终以索引访问生成，不变成非法裸 global。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_52)],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/keywords_01_luajit_contextual_goto.lua",
        &["contextual-keyword", "global"],
        "证明 LuaJIT 中 goto 在标识符位置不是硬关键字。",
        &[LuaCaseConfiguration::new(LUAJIT_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/keywords_02_luau_contextual_continue.lua",
        &["contextual-keyword", "global"],
        "证明 Luau 中 continue 在标识符位置不是硬关键字。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/keywords_03_lua55_contextual_global.lua",
        &["contextual-keyword", "global"],
        "证明 Lua 5.5 中 global 在普通标识符位置仍可作为名字。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/separators_01_parenthesized_call_separator.lua",
        &["parenthesized-call", "semicolon"],
        "生成源码必须用分号隔开前一赋值与下一行括号开头IIFE，避免粘成调用链。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/methods_06_keyword_method_name.lua",
        &["colon-call", "keyword", "table-field"],
        "新版本关键字global作为方法名时仍以合法冒号语法发射并传递参数。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/methods_01_alias_and_sugar.lua",
        &["alias", "call-chain", "field", "method"],
        "验证字段糖、方法声明及链式调用只在身份已证明时恢复。",
        &[LuaCaseConfiguration::new(PUC_LUA_51)],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/methods_02_function_sugar_guards.lua",
        &["debug", "global", "method", "provenance"],
        "约束function sugar在嵌套global、自参身份、debug local及receiver改写下的接受guard。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_54).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/methods_03_function_sugar_relax.lua",
        &["evaluation", "gc", "method", "receiver", "root"],
        "覆盖普通点调用缩写及receiver根、写目标；用后继GC观察固定数值终端闭包的原槽覆盖责任。",
        &[LuaCaseConfiguration::new(PUC_LUA_54)],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/methods_04_function_sugar_nested_local_ids.lua",
        &["callback", "gc-root", "local-id", "method-chain"],
        "验证child局部身份独立，以及finish清空self后caller仍保留中间结果根。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/methods_05_method_alias_nested_write_ids.lua",
        &[
            "callback",
            "gc-root",
            "local-id",
            "lookup",
            "method",
            "nested-function",
        ],
        "验证child写入身份独立；点调用lookup期间保留额外实参的旧根，SELF预写不得提前清除。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/functions_01_upvalue_function_decl.lua",
        &["assignment", "function", "upvalue"],
        "允许plain function声明语法赋值已有upvalue binding。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/functions_02_lua55_global_function_assignment.lua",
        &["function-sugar", "global"],
        "保证已声明global的后续function值写保持赋值，不能重写成global function声明。",
        &[
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55]).with_options(LuaCaseOptions {
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
            LuaCaseConfiguration::new(&[LuaCaseDialect::Lua55]).with_options(LuaCaseOptions {
                retain_debug: true,
                recompile_rounds: Some(3),
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/tables_01_constructor_field_name_sugar.lua",
        &["byte-key", "constructor", "identifier", "keyword"],
        "保证constructor字符串key仅在合法标识符时转field-name糖。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Lua54])],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/attributes_01_statement_merge_attr_handoff.lua",
        &["close", "declaration"],
        "保证一次使用的<close>尾值进入声明合并，而不被普通表达式内联吞掉属性绑定。",
        &[LuaCaseConfiguration::new(&[
            LuaCaseDialect::Lua54,
            LuaCaseDialect::Lua55,
        ])],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/tables_02_luau_record_key_syntax.lua",
        &["bracket-key", "capacity", "function-field"],
        "要求hash-only NEWTABLE的a/b/c保持方括号字符串key，避免裸名启用顺序索引分配；覆盖普通、numeric growth、function growth。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Luau])],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/separators_02_repeat_parenthesized_call_separator.lua",
        &["iife", "parse", "repeat", "semicolon"],
        "until条件后的下一条括号IIFE必须由分号分隔，不能被解析成condition调用链。",
        &[
            LuaCaseConfiguration::new(PUC_LUA_ALL),
            LuaCaseConfiguration::new(PUC_LUA_ALL).with_options(LuaCaseOptions {
                retain_debug: true,
                ..LuaCaseOptions::DEFAULT
            }),
        ],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/functions_03_vararg.lua",
        &["closure", "multi-return", "named-vararg"],
        "六个命名变参函数覆盖pack索引/n字段、capture改写、global安装、直接返回和正负偏移索引。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_55)],
    ),
    LuaCaseDefinition::new(
        "tests/case_syntax/attributes_02_luau_typed_control_flow_matrix.lua",
        &["continue", "if-expression", "type-annotation"],
        "十组Luau基础覆盖类型标注、continue、复合赋值、if表达式、插值、泛型函数和嵌套capture。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
];
