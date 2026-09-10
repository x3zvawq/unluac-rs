-- 共同结束的源码 local 跨 if/else 时仍须共享同一 do，不能按 producer 基本块拆开。
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
            assert(value.field == (flag and (nested and 1 or 2) or 3))
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
print("regress_527_debug_scope_across_branch", "closed")
