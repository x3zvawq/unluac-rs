-- 03 的递归自捕获声明；同一 binding 的空声明和闭包赋值应恢复为 local function。
-- unluac: expect-ast-min [[local-function]] [[1]]
-- unluac: expect-contains [[local function r1_0(]]
-- unluac: expect-not-line [[local r1_0]]
-- unluac: expect-contains [[labels = { "raw", "derived" }]]
-- 独立初始化与调用参数直接表达，不为递归或返回值新增中转绑定。
-- unluac: expect-ast-count [[function]] [[5]]
-- unluac: expect-ast-count [[table-constructor]] [[7]]
-- unluac: expect-ast-max [[local-binding]] [[11]] [[@proto=0]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=4]]
-- unluac: expect-ast-max [[local-binding]] [[7]] [[@proto=5]]
local function factorial(n)
    local function loop(current, result)
        if current <= 1 then
            return result
        end
        return loop(current - 1, result * current)
    end
    return loop(n, 1)
end
assert(factorial(0) == 1 and factorial(5) == 120)

-- 04 的嵌套构造器、显式整数键、变参和多返回宽度。
local function pair(value)
    return value, value * value
end
local function collect(values, ...)
    local result = {
        count = #values,
        first = values[1],
        labels = {"raw", "derived"},
    }
    for index, value in ipairs(values) do
        result[value] = index
    end
    result.extra_count = select("#", ...)
    result.extra_first = select(1, ...)
    return result
end
local function summarize(value)
    local original, squared = pair(value)
    local inputs = {[1] = original, [2] = squared, [3] = value + 1}
    local data = collect(inputs, "note", value)
    local parts = {}
    for key, index in pairs(data) do
        if type(key) == "string" then
            parts[#parts + 1] = key .. "=" .. tostring(index)
        end
    end
    table.sort(parts)
    return table.concat(parts, ";")
end
local first, second, third = pair(3)
assert(first == 3 and second == 9 and third == nil)
local data = collect({4, 16, 5}, "note", 4)
assert(data.count == 3 and data.first == 4)
assert(data[4] == 1 and data[16] == 2 and data[5] == 3)
assert(data.labels[1] == "raw" and data.labels[2] == "derived")
assert(data.extra_count == 2 and data.extra_first == "note")
local overwritten = collect({"labels", "first"})
assert(overwritten.labels == 1 and overwritten.first == 2)
assert(overwritten.extra_count == 0 and overwritten.extra_first == nil)
-- 地址不是程序稳定输出；只归一化这一个已确认的表地址文本，表身份/字段另由上面的断言检查。
local summary = summarize(4):gsub(";labels=table: [%xxX]+$", ";labels=<table>")
assert(summary == "count=3;extra_count=2;extra_first=note;first=4;labels=<table>")
local empty = collect({}, false, nil)
assert(empty.count == 0 and empty.first == nil)
assert(empty.extra_count == 2 and empty.extra_first == false)
assert(select("#", pair(0)) == 2)
print("recursive-table-results", factorial(5), first, second, third, summary)
