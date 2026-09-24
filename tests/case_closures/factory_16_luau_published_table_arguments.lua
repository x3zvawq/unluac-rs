-- 发布表的整数键与 __newindex 事件先于 consumer，两个工厂调用仍分配不同对象。
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=0]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local sink = setmetatable({}, {
    __newindex = function(_, key, value)
        print("publish", key, type(value))
    end,
})

local function make()
    local value = {}
    sink[255] = value
    return value
end

local function consume(...)
    local value = ...
    print("consume", type(value))
    return value
end

local first = consume(make())
local second = consume(make())
assert(first ~= second)
print("published-distinct", first ~= second)
