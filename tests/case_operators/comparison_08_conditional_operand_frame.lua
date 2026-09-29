-- 比较的条件操作数与 Boolean 结果共用原准备帧，不留下阻挡后继调用的高槽声明。
-- unluac: expect-contains [[local matched = value == (flag and yes or no)]] [[@debug=retained]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-not-contains [[__eq = 0]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[7]]
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
assert(compare(0, first, same, second, true))
assert(compare("", first, same, second, true))
assert(not compare(nil, first, same, second, false))
-- yes 为假时仍选择 no；不能把 and/or 当作普通条件表达式。
assert(not compare(true, first, false, second, false))
assert(compare(true, first, nil, same, true))
assert(comparisons == 7)
assert(compare(true, nil, false, nil, true))
assert(compare(false, false, first, false, true))
assert(compare(true, 0, 0, second, true))
assert(compare(true, "", "", second, true))
assert(comparisons == 7)
assert(select("#", compare(true, first, same, second, true)) == 1)
assert(comparisons == 8)
assert(not pcall(compare, true, first, same, second, false))
assert(comparisons == 9)
