-- 比较的条件操作数与 Boolean 结果共用原准备帧，不留下阻挡后继调用的高槽声明。
-- unluac: expect-contains [[local matched = value == (flag and yes or no)]] [[@debug=retained]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-not-contains [[__eq = 0]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-count [[repeat]] [[0]]
-- unluac: expect-ast-count [[function]] [[6]]
-- unluac: expect-ast-max [[local-binding]] [[15]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=6]]
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

-- 外层短路中的算术选择臂仍是值准备；左快照必须先于 __add，再由 __eq 消费。
local trace = {}
local ordered_meta = {__eq = function(a, b)
    trace[#trace + 1] = "eq"
    return a.value == b.value
end}
local read_value = setmetatable({value = "same"}, ordered_meta)
local computed = setmetatable({value = "same"}, ordered_meta)
local record = setmetatable({}, {__index = function(_, key)
    assert(key == "time")
    trace[#trace + 1] = "read"
    return read_value
end})
local operand = setmetatable({}, {__add = function(a, b)
    assert(a == 1000 and type(b) == "table")
    trace[#trace + 1] = "add"
    read_value = false
    return computed
end})
local function nested(enabled, choose, source, input)
    return enabled and source.time == (choose and 0 or 1000 + input)
end
assert(nested(true, false, record, operand) == true)
assert(table.concat(trace, ",") == "read,add,eq" and read_value == false)
trace = {}
read_value = setmetatable({value = "different"}, ordered_meta)
assert(nested(true, false, record, operand) == false)
assert(table.concat(trace, ",") == "read,add,eq")
trace = {}
read_value = 0
assert(nested(true, true, record, operand) == true)
assert(table.concat(trace, ",") == "read" and read_value == 0)
trace = {}
assert(nested(false, false, record, operand) == false)
assert(nested(nil, false, record, operand) == nil)
assert(#trace == 0)
assert(select("#", nested(false, false, record, operand)) == 1)
assert(not pcall(nested, true, false, record, nil))
assert(table.concat(trace, ",") == "read")
print("nested-comparison-preparation", table.concat(trace, ","))
