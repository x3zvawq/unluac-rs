-- 循环体内的闭合窗口不等于 SCC；包住整个循环时 scratch 必须在末端前真正退休。
-- unluac: expect-ast-min [[numeric-for]] [[1]]
-- unluac: expect-ast-min [[do-block]] [[1]] [[@debug=retained]]
-- unluac: expect-ast-count [[do-block]] [[3]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[14]]
-- unluac: expect-ast-count [[function]] [[6]]
local calls = 0
local function body_window(flag)
    local weak = setmetatable({}, { __mode = "k" })
    for i = 1, 3 do
        do
            local scoped = {}
            weak[scoped] = true
            if flag then scoped.field = 1 else scoped.field = 2 end
            local function use(value)
                collectgarbage("collect")
                assert(weak[value] == true and value.field == (flag and 1 or 2))
                calls = calls + 1
            end
            use(scoped)
        end
        collectgarbage("collect")
        assert(next(weak) == nil, "loop body scope retained object")
    end
end

local function while_window(limit)
    local weak = setmetatable({}, { __mode = "k" })
    do
        local scoped = {}
        weak[scoped] = true
        scoped.field = 0
        while scoped.field < limit do
            scoped.field = scoped.field + 1
        end
        local function use(value)
            collectgarbage("collect")
            assert(weak[value] == true and value.field == limit)
            calls = calls + 1
        end
        use(scoped)
    end
    collectgarbage("collect")
    assert(next(weak) == nil, "whole while scope retained object")
end

local function repeat_window(limit)
    local weak = setmetatable({}, { __mode = "k" })
    do
        local scoped = {}
        weak[scoped] = true
        scoped.field = 0
        repeat
            scoped.field = scoped.field + 1
        until scoped.field >= limit
        local function use(value)
            collectgarbage("collect")
            assert(weak[value] == true and value.field == limit)
            calls = calls + 1
        end
        use(scoped)
    end
    collectgarbage("collect")
    assert(next(weak) == nil, "whole repeat scope retained object")
end

body_window(true)
body_window(false)
while_window(0)
while_window(3)
repeat_window(1)
repeat_window(3)
assert(calls == 10)
print("regress_528_debug_scope_loop_windows", "closed")
