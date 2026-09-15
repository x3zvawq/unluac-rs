-- 迭代器、dispatch 结果与清理位置来自冻结协议，debug 名字不能额外保留外层对象。
-- unluac: expect-ast-min [[generic-for]] [[1]]
-- unluac: expect-ast-min [[do-block]] [[1]] [[@debug=retained]]
local function run(values)
    local weak = setmetatable({}, { __mode = "k" })
    do
        local scoped = {}
        weak[scoped] = true
        scoped.field = 0
        for _, value in ipairs(values) do
            scoped.field = value
            collectgarbage("collect")
            assert(next(weak) ~= nil, "generic body lost object")
        end
        local function use(value) assert(value.field == #values) end
        use(scoped)
    end
    collectgarbage("collect")
    assert(next(weak) == nil, "whole generic scope retained object")
end

run({})
run({1, 2, 3})
print("regress_531_debug_scope_generic_for", "closed")
