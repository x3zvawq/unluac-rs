-- 比较的条件操作数与 Boolean 结果共用原准备帧，不留下阻挡后继调用的高槽声明。
-- unluac: expect-contains [[local matched = value == (flag and yes or no)]] [[@debug=retained]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-not-contains [[__eq = 0]]
local function compare(flag, value, yes, no, expected)
    local matched = value == (flag and yes or no)
    assert(matched == expected)
    return matched
end
local comparisons = 0
local meta = {
    __eq = function(left, right)
        comparisons = comparisons + 1
        return left.value == right.value
    end,
}
local first = setmetatable({value = "yes"}, meta)
local same = setmetatable({value = "yes"}, meta)
local second = setmetatable({value = "no"}, meta)
assert(compare(true, first, same, second, true))
assert(not compare(false, first, same, second, false))
assert(comparisons == 2)
print("comparison_08_conditional_operand_frame", comparisons)
