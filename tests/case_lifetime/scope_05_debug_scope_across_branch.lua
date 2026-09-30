-- 共同结束的源码 local 跨 if/else 时仍须共享同一 do，不能按 producer 基本块拆开。
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[do-block]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[5]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[call]] [[5]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[4]] [[@proto=1]]
local calls = 0
local function run(flag, nested)
    local weak = setmetatable({}, { __mode = "k" })
    do
        local scoped = {}
        weak[scoped] = true
        if flag then
            if nested then
                scoped.field = 1
            else
                scoped.field = 2
            end
        else
            scoped.field = 3
        end
        local function use(value)
            collectgarbage("collect")
            assert(weak[value] == true)
            assert(value.field == (flag and (nested and 1 or 2) or 3))
            calls = calls + 1
        end
        use(scoped)
    end
    collectgarbage("collect")
    assert(next(weak) == nil, "branch-spanning debug scope retained its object")
end

run(true, true)
run(true, false)
run(false, true)
run(false, false)
assert(calls == 4)
print("regress_527_debug_scope_across_branch", "closed")
