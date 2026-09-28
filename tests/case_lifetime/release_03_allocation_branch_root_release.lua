-- regress_386_allocation_branch_root_release: a branch overwrite releases an escaped allocation root before GC
-- 对象根与两臂覆盖共用一个 local；再生成运行同时检验 TESTSET 的清根时点。
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]]
-- unluac: expect-count [[ and true or false]] [[1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]]
-- unluac: expect-not-contains [[goto ]]

local weak = setmetatable({}, { __mode = "v" })

local function run(condition)
    local value = {}
    weak.key = value
    if condition then
        value = true
    else
        value = false
    end
    collectgarbage("collect")
    collectgarbage("collect")
    return weak.key == nil
end

-- 独立保留源码 TESTSET 入口，避免 Boolean 规范化后只测到 NOT 路径。
local function run_testset(condition)
    local value = {}
    weak.key = value
    value = condition and true or false
    collectgarbage("collect")
    collectgarbage("collect")
    return weak.key == nil
end

assert(run(true))
assert(run(false))
assert(run_testset(true))
assert(run_testset(false))
assert(run_testset(nil))
assert(run_testset(0))
assert(run_testset(""))
