-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-ast-count [[table-list-field]] [[4]] [[@proto=2]] [[@dialect=lua5.1]]
local ceil = math.ceil
local function fetch(i)
    return i * 7
end

local function run(n)
    local result = {}
    local count, first, second, third
    for i = 1, n do
        count = fetch(i)
        first = ceil(60 / count)
        second = ceil(30 / count)
        third = ceil(10 / count)
        result[i] = { count, first, second, third }
    end
    return result
end

assert(next(run(0)) == nil)
local result = run(2)
assert(table.concat(result[1], ",") == "7,9,5,2")
assert(table.concat(result[2], ",") == "14,5,3,1")
print("loop nil owners", table.concat(result[1], ","), table.concat(result[2], ","))

local max = math.max
local weights = { 0.6, 0.3, 0.1 }
local function prepare(total, counters)
    local rows = {}
    local count, first, second, third
    for i = 1, #counters do
        count = max(fetch(counters[i]), 1)
        first = ceil(total * weights[1] / count)
        second = ceil(total * weights[2] / count)
        third = ceil(total * weights[3] / count)
        rows[i] = { count, first, second, third }
    end
    return rows
end

local rows = prepare(100, { 1, 2, 0 })
assert(table.concat(rows[1], ",") == "7,9,5,2")
assert(table.concat(rows[2], ",") == "14,5,3,1")
assert(table.concat(rows[3], ",") == "1,60,30,10")
print("loop scratch", table.concat(rows[3], ","))

-- 按引用捕获的别名仍可能在参数求值中被改写，不能继承按值 builtin 许可。
local function mutable_builtin_snapshot()
    local operation = math.ceil
    local function replace()
        operation = function(value) return value + 100 end
    end
    local operand = setmetatable({}, {
        __div = function()
            replace()
            return 1.5
        end,
    })
    local function evaluate(value)
        return operation(value / 2)
    end
    return evaluate(operand), evaluate(4)
end
local before, after = mutable_builtin_snapshot()
assert(before == 2 and after == 102)
print("mutable callee", before, after)
