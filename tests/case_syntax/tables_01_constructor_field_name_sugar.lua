-- regress_414_constructor_field_name_sugar: constructor string keys share field-access legality
-- 原低槽键声明保留，完整嵌套调用不留下 callee/结果接棒。
-- unluac: expect-ast-max [[local-binding]] [[6]] [[@proto=0]]
-- unluac: expect-contains [[[string.char(255)] == 4]]
-- unluac: expect-contains [[alpha = 1]]
-- unluac: expect-not-contains [["alpha"] = 1]]
-- unluac: expect-contains [[["end"] = 2]]
-- unluac: expect-contains [[["bad-key"] = 3]]
-- unluac: expect-contains [[["\255"] = 4]]

local alpha_key, keyword_key, invalid_key, byte_key = "alpha", "end", "bad-key", "\255"
local values = {
    [alpha_key] = 1,
    [keyword_key] = 2,
    [invalid_key] = 3,
    [byte_key] = 4,
}

assert(values.alpha == 1)
assert(values["end"] == 2)
assert(values["bad-key"] == 3)
assert(values[string.char(255)] == 4)
-- 直接字面量键验证名称糖；原变量键的帧身份不能为得到名称糖而删除。
local literal_values = {["alpha"] = 1, ["end"] = 2, ["bad-key"] = 3, ["\255"] = 4}
assert(literal_values.alpha == values.alpha and literal_values["end"] == values["end"])
assert(literal_values["bad-key"] == values["bad-key"] and literal_values["\255"] == values["\255"])
print("regress_414_constructor_field_name_sugar", "OK")
