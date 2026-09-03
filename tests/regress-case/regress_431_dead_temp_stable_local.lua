-- regress_431_dead_temp_stable_local: an entry-nil dead copy of an unmodified visible local
-- has no independent root duty, while a copy whose source binding is overwritten must remain;
-- the physical root may attach directly to the copied value instead of retaining an SSA alias.
-- unluac: expect-not-contains [[local r1_0 = p1_0]]
-- unluac: expect-contains [[local r2_0 = p2_0]]
-- unluac: expect-contains [[local r3_0 = r0_3]]
-- unluac: expect-not-contains [[local r3_1 = r3_0]]

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
