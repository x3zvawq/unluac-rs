local weak = setmetatable({}, { __mode = "v" })

local function allocation_root()
    local first = {}
    local second = {}
    weak[1], weak[2] = first, second
    local a0 = first
    local a1 = first
    local a2 = first
    local get = function() return a2 end
    first = nil
    second = nil
    collectgarbage("collect")
    assert(weak[1] ~= nil)
    a0 = nil
    a1 = nil
    a2 = nil
    collectgarbage("collect")
    assert(get() == nil and weak[1] == nil)
end

local function call_root()
    local first = setmetatable({}, {})
    local second = {}
    weak[1], weak[2] = first, second
    local a0 = first
    local a1 = first
    local a2 = first
    local get = function() return a2 end
    first = nil
    second = nil
    collectgarbage("collect")
    assert(weak[1] ~= nil)
    a0 = nil
    a1 = nil
    a2 = nil
    collectgarbage("collect")
    assert(get() == nil and weak[1] == nil)
end

allocation_root()
call_root()
print("captured-root-handoff", "OK")
