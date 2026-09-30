local weak = setmetatable({}, { __mode = "v" })
-- unluac: expect-ast-count [[close-binding]] [[2]]
-- unluac: expect-ast-max [[local-binding]] [[14]]
-- 表目标和首项 RHS 的准备只属于并列赋值，不占用后续资源声明的源码身份。
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@proto=3]]
-- unluac: expect-count [[weak[1], weak[2] = first, second]] [[2]] [[@debug=retained]]
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
        assert(weak[2] == nil)
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
        assert(weak[2] == nil)
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
