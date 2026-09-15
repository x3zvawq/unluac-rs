-- unluac: expect-contains [[missing_global]]
-- 可观察读取可保留为条件或独立求值；按实际次数和值验证，不固定生成语法。

local env = _VERSION == "Lua 5.1" and getfenv() or _ENV
local global_hits = 0

setmetatable(env, {
    __index = function(_, key)
        if key == "missing_global" or key == "probe" then
            global_hits = global_hits + 1
            return true
        end
    end,
})

local unused = missing_global
assert(global_hits == 1, "unused global read must execute once")
print("global-read", global_hits)

global_hits = 0
local global_value = (probe and false) or (probe and true)
assert(global_hits == 2 and global_value == true, "global logical reads changed")
print("global-logic", global_hits, global_value)

local table_hits = 0
local subject = setmetatable({}, {
    __index = function()
        table_hits = table_hits + 1
        return true
    end,
})
local table_value = (subject.probe and false) or (subject.probe and true)
assert(table_hits == 2 and table_value == true, "table logical reads changed")
print("table-logic", table_hits, table_value)

local compare_hits = 0
local mt = {
    __lt = function()
        compare_hits = compare_hits + 1
        return true
    end,
}
local left, right = setmetatable({}, mt), setmetatable({}, mt)
local compare_value = (left < right and false) or (left < right and true)
assert(compare_hits == 2 and compare_value == true, "comparison metamethod calls changed")
print("metamethod-logic", compare_hits, compare_value)

local while_hits = 0
local function false_probe()
    while_hits = while_hits + 1
    return false
end
while false_probe() do
end
while false_probe() do
end
assert(while_hits == 2, "empty loop conditions must each execute once")
print("empty-while-reads", while_hits)

local function shared_rhs(a, b, c)
    return (a and b) or (c and b)
end

local function reordered_or(c, a, b)
    return c or (a and (b or c))
end

print(
    "logical-value",
    shared_rhs(true, nil, false) == false,
    reordered_or("first", true, "later")
)
