-- 原 CALL 结果在测试后、观察前已被同 home 覆盖时，可消费该事实归约共享尾。
-- 查找本条可能先触发 __index；独立 source local 也不能借调用临时槽的覆盖证明。
-- unluac: expect-not-contains [[if p1_0 then]]
-- unluac: expect-not-contains [[if a then]]
local function direct(a, probe, fallback)
    return a and not probe() or fallback()
end

local function lookup(enabled, probe, methods)
    return enabled and not probe() or methods.next()
end

local function retained(enabled, probe, fallback)
    local saved = probe()
    return enabled and not saved or fallback()
end

local weak = setmetatable({}, {__mode = "v"})
local trace = {}
local function probe()
    trace[#trace + 1] = "probe"
    local value = {}
    weak.value = value
    return value
end
local function observe()
    collectgarbage("collect")
    collectgarbage("collect")
    return weak.value ~= nil
end
local function fallback()
    trace[#trace + 1] = "fallback"
    return observe()
end
local methods = setmetatable({}, {__index = function()
    trace[#trace + 1] = "lookup"
    local alive = observe()
    return function() return alive end
end})

print("direct", direct(true, probe, fallback))
print("lookup", lookup(true, probe, methods))
print("retained", retained(true, probe, fallback))
print("disabled", direct(false, probe, fallback))
print("trace", table.concat(trace, ","))

-- nil/false 与 truthy 对象必须走同样的短路方向，不把未知结果直接当成 Boolean 返回。
local function falsy() return false end
local function absent() return nil end
print("falsy", direct(true, falsy, fallback))
print("absent", direct(true, absent, fallback))
