//! literals 主题源码合同；标签描述交叉语义，配置保留原方言及专用验证边界。
use super::*;
pub(super) const CASES: &[LuaCaseDefinition] = &[
    LuaCaseDefinition::new(
        "tests/case_literals/number_07_scientific_roundtrip.lua",
        &["float", "format", "roundtrip", "sign-bit"],
        "极端 f64 的科学计数法保持有效数字、负零和浮点类型，常用量级仍用十进制。",
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
        "tests/case_literals/nonfinite_01_luajit_infinite_imaginary.lua",
        &["imaginary", "nonfinite", "numeric-token"],
        "将正负无穷虚部发射为 LuaJIT 可重编译的 `1e999i` token。",
        &[LuaCaseConfiguration::new(LUAJIT_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/number_01_literal_power.lua",
        &["negative-zero", "power", "precedence"],
        "确保负整数、负浮点和负零作为幂底数时保留括号，避免一元负号优先级改变。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/string_01_long_bracket_suffix_delimiter.lua",
        &["delimiter", "long-bracket"],
        "字符串内容后缀不能与closing delimiter跨边界提前闭合。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/number_02_luau_nan_fixed_point.lua",
        &["fixed-point", "nan"],
        "NaN自不等性不能让无改动pass误报changed。",
        &[LuaCaseConfiguration::new(LUAU_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/string_02_long_bracket_control_byte.lua",
        &["control-byte", "long-bracket", "nul"],
        "含换行字节串不能用裸NUL long-bracket发射。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/number_04_integer_float_boundaries.lua",
        &["int64-min", "float", "nonfinite", "multiret", "snapshot"],
        "整数最小值及快照、积分浮点类型与非有限数复制屏障的独立子函数边界。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_53)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/number_05_numeric_for_float_step.lua",
        &["float", "numeric-for", "type"],
        "数值for的1.0步长必须保留浮点控制变量类型。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_53)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/cdata_01_boolean_shell_luajit_constant_old_value.lua",
        &["boolean-shell", "cdata"],
        "证明LuaJIT KCDATA常量归proto所有，不构成被覆写栈槽的GC旧值。",
        &[LuaCaseConfiguration::new(LUAJIT_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/vector_01_boolean_shell_luau_vector_old_value.lua",
        &["boolean-shell", "vector"],
        "Luau vector 常量归 proto 所有，但未使用的布尔写回仍保留原检查。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_VECTOR_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/number_03_decision_signed_zero_identity.lua",
        &["identity", "ieee754", "truthiness"],
        "验证布尔自然化不能把由-0.0输入产生的正零结果错误保留为负零。",
        &[LuaCaseConfiguration::new(ALL_NON_LUAU_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/truthiness_01_literal_not_truthiness.lua",
        &["alias-cleanup", "literal", "not"],
        "验证alias清理保留原NOT，区分Luau在编译阶段已经折叠的常量结果。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/cdata_02_luajit_result_identity.lua",
        &["cdata", "multi-return", "rawequal"],
        "对1LL、1ULL、1i分别证明同一local复制返回的两个cdata rawequal，而两个独立字面量不rawequal，区分proto锚定与重新物化身份。",
        &[LuaCaseConfiguration::new(&[LuaCaseDialect::Luajit])],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/cdata_03_luajit_logical_literals.lua",
        &["cdata", "short-circuit"],
        "signed/unsigned/imaginary cdata字面量作为短路返回原子。",
        &[LuaCaseConfiguration::new(LUAJIT_ONLY)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/vector_02_luau_logical_vectors.lua",
        &["short-circuit", "vector"],
        "官方vector常量作为共享逻辑原子域分支值。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_VECTOR_OPTIONS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/string_03_encoding.lua",
        &["binary-string", "bytes", "escape", "utf8"],
        "GBK样字节、真正UTF-8、内嵌换行/引号和NUL+255后接数字均保持原字节。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/encoding_01_literal_string_bytes.lua",
        &[
            "bytes",
            "control-code",
            "escape",
            "newline",
            "nul",
            "string",
            "substring",
            "utf8",
        ],
        "三个独立函数保留NUL数字转义、开头换行及UTF-8控制字符的原字节与返回值布局。",
        &[LuaCaseConfiguration::new(ALL_DIALECTS)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/number_06_literal_negative_zero_float.lua",
        &["division", "float", "format", "sign-bit"],
        "负零浮点常量必须保留符号，使1/value产生负无穷而非正无穷。",
        &[LuaCaseConfiguration::new(PUC_LUA_GE_53)],
    ),
    LuaCaseDefinition::new(
        "tests/case_literals/vector_03_vector.lua",
        &["constant", "host-constructor", "vector"],
        "native vector常量使用配置的三参数host constructor，不能凭空补第四个零分量。",
        &[LuaCaseConfiguration::new(LUAU_ONLY).with_options(LUAU_VECTOR_OPTIONS)],
    ),
];
