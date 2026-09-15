-- 参数内调用的 callee 必达，但不能丢失更早事件、条件区域和原 callable 根。
-- 各方言的 GC 观察与自己的源码基线比较，不约定跨 VM 的残余槽存活。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[.child(5)]]
local weak = setmetatable({}, {__mode = "v"})
local trace = {}
local function observe(label)
    collectgarbage("collect")
    collectgarbage("collect")
    trace[#trace + 1] = label
    print(label, weak.value ~= nil)
    return 5
end
local provider = setmetatable({}, {__index = function(_, key)
    trace[#trace + 1] = "lookup-" .. key
    local callable = setmetatable({}, {__call = function(self, value)
        observe("call")
        assert(weak.value == self)
        return value + 7, "open-tail"
    end})
    weak.value = callable
    return callable
end})
local function sink(first, value, tail)
    trace[#trace + 1] = "sink"
    assert(first == 5 and value == 12 and tail == "open-tail")
    return value
end
local function direct()
    return sink(observe("first"), provider.child(observe("argument")))
end
local function snapshot()
    local callee = provider.child
    return sink(observe("first"), callee(observe("argument")))
end
local function conditional(flag)
    return flag and sink(observe("first"), provider.child(observe("argument")))
end
local function repeated()
    local callee = provider.child
    local count = 0
    while sink(observe("first"), callee(observe("argument"))) == 12 do
        count = count + 1
        if count == 2 then break end
    end
    return count
end
local function compact()
    return sink(5, provider.child(5))
end
collectgarbage("stop")
assert(compact() == 12)
print("compact-trace", table.concat(trace, ","))
trace = {}
assert(direct() == 12)
print("direct-trace", table.concat(trace, ","))
trace = {}
assert(snapshot() == 12)
print("snapshot-trace", table.concat(trace, ","))
trace = {}
assert(conditional(false) == false and #trace == 0)
assert(conditional(true) == 12)
print("conditional-trace", table.concat(trace, ","))
trace = {}
assert(repeated() == 2)
print("repeat-trace", table.concat(trace, ","))
-- OPEN 返回零值不证明旧 callee 槽必然覆写；整调用树仍须保留原帧和真实宽度。
local open_provider = setmetatable({}, {__index = function(_, key)
    local callable = setmetatable({}, {__call = function(self)
        observe("open-" .. key)
        assert(weak.value == self)
        if key == "empty" then return end
        return 1, nil, 3
    end})
    weak.value = callable
    return callable
end})
local function receive_open(label, ...)
    print(label, select("#", ...))
    observe("received-" .. label)
end
receive_open("empty", open_provider.empty())
receive_open("many", open_provider.many())

-- callee 来源在参数期被重绑，已经读出的旧 callable 仍须调用一次。
local source = provider
local fallback = {child = function() error("late callee read") end}
local function swap_source()
    source = fallback
    return 5
end
local function source_snapshot()
    return sink(5, source.child(swap_source()))
end
assert(source_snapshot() == 12)

local function captured_callee()
    local callee = provider.child
    local function replace()
        callee = fallback.child
        return 5
    end
    return sink(5, callee(replace()))
end
assert(captured_callee() == 12)

local function captured_argument()
    local first = 5
    local function replace()
        first = 99
        return 5
    end
    return sink(first, provider.child(replace()))
end
assert(captured_argument() == 12)
collectgarbage("restart")

-- 普通点调用的 receiver 参数在字段读取后写入；SELF 提前写该槽，即使
-- receiver 是稳定 local，也可能在 __index 的 GC 中提前覆盖上次调用残值。
-- 每个 VM 使用自己的源码输出作基线，不要求跨方言采用相同栈扫描范围。
local function dot_receiver_slot()
    local slot_weak = setmetatable({}, {__mode = "v"})
    local observed
    local function make_object()
        return setmetatable({}, {__index = function()
            collectgarbage("collect")
            collectgarbage("collect")
            observed = type(slot_weak[1]) == "table"
            return function(self) end
        end})
    end
    local function stash()
        local marker = {}
        slot_weak[1] = marker
        return 7, marker
    end
    local function run()
        local object = make_object()
        stash()
        object.lookup(object)
    end
    collectgarbage("stop")
    run()
    collectgarbage("restart")
    return observed
end
print("dot-receiver-slot", dot_receiver_slot())
