-- regress_179_long_bracket_suffix_delimiter#1: 内容后缀不能与 closing delimiter 跨边界提前闭合
-- unluac: expect-contains [[[=[a]]
-- unluac: expect-contains [[[==[b]]

local zero_level_suffix = "a\n]"
local nested_closing_and_suffix = "b\n]]\n]="
assert(#zero_level_suffix == 3 and zero_level_suffix == "a\n]")
assert(#nested_closing_and_suffix == 7 and nested_closing_and_suffix == "b\n]]\n]=")

print(
    "regress_179_long_bracket_suffix_delimiter#1",
    #zero_level_suffix,
    zero_level_suffix == "a\n]",
    #nested_closing_and_suffix,
    nested_closing_and_suffix == "b\n]]\n]=",
    -- 原字符串也必须进入生成器，不能只运行被编译器折成常量的长度/比较结果。
    zero_level_suffix,
    nested_closing_and_suffix
)
