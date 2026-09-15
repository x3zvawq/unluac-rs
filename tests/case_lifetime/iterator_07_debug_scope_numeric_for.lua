-- 完整 for 的控制 phi 留在窗口内部；末尾调用退休高槽，不能延长 scoped 的源码根。
-- unluac: expect-ast-min [[numeric-for]] [[1]]
-- unluac: expect-ast-min [[do-block]] [[1]] [[@debug=retained]]
local function run(limit)
    local weak = setmetatable({}, { __mode = "k" })
    do
        local scoped = {}
        weak[scoped] = true
        scoped.field = 0
        for index = 1, limit do
            scoped.field = index
            collectgarbage("collect")
            assert(next(weak) ~= nil, "numeric body lost object")
        end
        local function use(value) assert(value.field == limit) end
        use(scoped)
    end
    collectgarbage("collect")
    assert(next(weak) == nil, "whole numeric scope retained object")
end

run(0)
run(3)
print("regress_530_debug_scope_numeric_for", "closed")
