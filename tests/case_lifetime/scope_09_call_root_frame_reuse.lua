-- 旧 CALL 结果保活到原槽覆盖，后继完整调用在该槽重新准备，不延长旧对象生命。
-- unluac: expect-contains [[observe_frame_roots("after")]]
local weak = setmetatable({}, {__mode = "v"})
local events = {}

function make_frame_root(name)
    if name == "tail" then
        collectgarbage("collect")
        collectgarbage("collect")
        assert(weak.outer ~= nil, "outer root ended before its overwrite")
        events[#events + 1] = "alive"
    end
    local object = {name = name}
    weak[name] = object
    return object
end

function observe_frame_roots(stage)
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak.outer == nil, "old root survived the new call frame")
    assert(weak.tail == nil, "higher root survived argument overwrite")
    events[#events + 1] = stage
    return {stage = stage}
end

local function run()
    do
        local outer = make_frame_root("outer")
        assert(outer.name == "outer")
        local tail = make_frame_root("tail")
    end
    local after = observe_frame_roots("after")
end

run()
assert(table.concat(events, ",") == "alive,after")
print(table.concat(events, ","))
