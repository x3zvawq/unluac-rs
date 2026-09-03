-- aggregate 持有关系不得随着中间 binding 的覆盖丢失；外层逃逸必须传播到后加入的 child。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local weak = setmetatable({}, { __mode = "v" })
local function clear(holder)
    weak[1] = holder.inner.child
    holder.inner.child = nil
    collectgarbage("collect")
    return weak[1] ~= nil
end

local child = {}
local inner = {}
local outer = { inner = inner }
inner.child = child
inner = nil
assert(clear(outer))
child = nil
collectgarbage("collect")
assert(weak[1] == nil)
print("regress_461_aggregate_escape_identity#1")

-- 未知 receiver 的 __index 会暴露 key，不能把一次读取当作未逃逸证明。
local function lookup_escape()
    local probe = setmetatable({}, {
        __index = function(_, key)
            weak[1] = key
            return 1
        end,
    })
    local value = {}
    local holder = { value = value }
    local result = probe[value]
    holder.value = nil
    collectgarbage("collect")
    assert(weak[1] ~= nil)
    value = nil
    collectgarbage("collect")
    assert(weak[1] == nil)
    return result
end
assert(lookup_escape() == 1)

-- child effect 未汇总时，调用已知 closure 也必须保留 capture 的可能逃逸与写入。
local function capture_escape()
    local value = {}
    local holder = { value = value }
    local deliver = function() weak[1] = value end
    deliver()
    holder.value = nil
    collectgarbage("collect")
    assert(weak[1] ~= nil)
    value = nil
    collectgarbage("collect")
    assert(weak[1] == nil)
end
capture_escape()
print("regress_461_aggregate_escape_identity#2")

-- repeat 条件只能看到最外层 holder 时，也必须查询后加入的传递持有边。
local function check_alive()
    collectgarbage("collect")
    assert(weak[1] ~= nil)
    return true
end
repeat
    local child = {}
    local outer = { child = child }
    local value = {}
    child.value = value
    weak[1] = value
    value = nil
    child = nil
until check_alive()
collectgarbage("collect")
assert(weak[1] == nil)
print("regress_461_aggregate_escape_identity#3")
