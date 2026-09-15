local weak = setmetatable({}, { __mode = "v" })
-- unluac: expect-ast-count [[close-binding]] [[2]]
local closed = 0

local function allocation_root()
    local first = {}
    local second = {}
    setmetatable(first, { __close = function() closed = closed + 1 end })
    weak[1], weak[2] = first, second
    do
        local a0 = first
        local a1 = first
        local a2 <close> = first
        first = nil
        second = nil
        collectgarbage("collect")
        assert(a0 == a2 and a1 == a2 and weak[1] ~= nil)
        a0 = nil
        a1 = nil
    end
    collectgarbage("collect")
    assert(weak[1] == nil)
end

local function call_root()
    local first = setmetatable({}, { __close = function() closed = closed + 1 end })
    local second = {}
    weak[1], weak[2] = first, second
    do
        local a0 = first
        local a1 = first
        local a2 <close> = first
        first = nil
        second = nil
        collectgarbage("collect")
        assert(a0 == a2 and a1 == a2 and weak[1] ~= nil)
        a0 = nil
        a1 = nil
    end
    collectgarbage("collect")
    assert(weak[1] == nil)
end

allocation_root()
assert(closed == 1)
call_root()
assert(closed == 2)
print("resource-root-handoff", "OK")
