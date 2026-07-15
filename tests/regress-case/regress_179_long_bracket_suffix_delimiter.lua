-- regress_179_long_bracket_suffix_delimiter#1: 内容后缀不能与 closing delimiter 跨边界提前闭合

local zero_level_suffix = "a\n]"
local nested_closing_and_suffix = "b\n]]\n]="

print(
    "regress_179_long_bracket_suffix_delimiter#1",
    #zero_level_suffix,
    zero_level_suffix == "a\n]",
    #nested_closing_and_suffix,
    nested_closing_and_suffix == "b\n]]\n]="
)
