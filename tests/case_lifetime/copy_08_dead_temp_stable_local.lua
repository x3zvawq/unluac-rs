-- 稳定参数的副本仍承载 callback 原调用帧前缀；移动该帧会改变返回后残根的覆盖窗口。
-- unluac: expect-contains [[local r1_0 = p1_0]]
-- unluac: expect-contains [[local r1_1 = r1_0]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=1]]
-- unluac: expect-contains [[local r2_0 = p2_0]]
-- unluac: expect-contains [[local r3_0 = r0_3]]
-- unluac: expect-not-contains [[local r3_1 = r3_0]]
-- unluac: expect-ast-max [[local-decl]] [[2]] [[@proto=3]]

local function stable(value, callback)
    local source = value
    local discarded = source
    callback()
    return source
end

local function overwritten(value, callback)
    local root_copy = value
    value = nil
    callback()
end

local weak = setmetatable({}, { __mode = "v" })
local original = {}
weak.value = original

local function only_root(callback)
    local source = original
    original = nil
    local root_copy = source
    callback()
end

local captured_weak = setmetatable({}, { __mode = "v" })

local function captured(value, callback)
    local source = value
    captured_weak.value = source
    local function clear()
        source = nil
    end
    local root_copy = source
    callback(clear)
end

local stable_value = {}
assert(stable(stable_value, function() end) == stable_value)

collectgarbage("stop")
local overwritten_weak = setmetatable({}, { __mode = "v" })
local value = {}
overwritten_weak.value = value
overwritten(value, function()
    value = nil
    collectgarbage("restart")
    collectgarbage("collect")
    collectgarbage("collect")
    assert(overwritten_weak.value ~= nil, "overwritten source lost its copy root")
end)

collectgarbage("stop")
only_root(function()
    collectgarbage("restart")
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak.value ~= nil, "stable source lost its physical copy root")
end)

collectgarbage("stop")
captured({}, function(clear)
    clear()
    collectgarbage("restart")
    collectgarbage("collect")
    collectgarbage("collect")
    assert(captured_weak.value ~= nil, "reference capture alias lost its copy root")
end)

print("regress_431_dead_temp_stable_local", "OK")

-- callback 的临时对象只经弱表发布；caller 在 stable 返回后覆盖低槽，再观察残根。
-- 此时 value 本身只是数字，差异来自调用帧移动，而不是 source 的对象保活。
local callback_weak = setmetatable({}, {__mode = "v"})
local callback_observations = {}
local function remember_callback()
    local object = {}
    callback_weak.value = object
end
local callback_methods = setmetatable({}, {__index = function()
    collectgarbage("collect")
    collectgarbage("collect")
    callback_observations[#callback_observations + 1] = type(callback_weak.value)
    return function() end
end})
local function folded(value, callback)
    callback()
    return value
end
local function observe_callback(callback)
    local result = callback(17, remember_callback)
    local a, b, c, d, e = 1, 1, 1, 1, 1
    callback_methods.observe()
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}
    return result, reserve[1]
end
collectgarbage("stop")
assert(observe_callback(stable) == 17)
assert(observe_callback(folded) == 17)
collectgarbage("restart")
assert(table.concat(callback_observations, ",") == "table,nil", "callback frame lost its residual root window")
