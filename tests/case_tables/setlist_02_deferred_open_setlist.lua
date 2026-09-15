-- regress_253_luau_deferred_open_setlist#1: 保留 open SETLIST 前的短路 producer
-- unluac: expect-contains [[return { table.unpack(]]
-- unluac: expect-contains [[.values or {}]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- 必须内联的模块编译要求不随展示注释关闭；禁止退回额外 IIFE 或机械声明。
-- unluac: expect-contains [[--!optimize 2]]
-- unluac: expect-ast-count [[local-function]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=0]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[call]] [[5]] [[@proto=0]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=1]]
-- 外部环境观察独立编译，避免 setfenv 进入被测模块并禁止原 O2 内联。
-- unluac-runtime: local run = ...
-- unluac-runtime: local weak = setmetatable({}, { __mode = "v" })
-- unluac-runtime: local unpack_values = table.unpack
-- unluac-runtime: local calls = 0
-- unluac-runtime: local function observe(values)
-- unluac-runtime:     calls += 1
-- unluac-runtime:     local params, vararg = debug.info(2, "a")
-- unluac-runtime:     assert(params == 0 and vararg, "unexpected unpack caller activation")
-- unluac-runtime:     if calls == 1 then
-- unluac-runtime:         weak[1] = values
-- unluac-runtime:     else
-- unluac-runtime:         collectgarbage("collect")
-- unluac-runtime:         assert(weak[1] == nil, "first input survived its original overwrite")
-- unluac-runtime:     end
-- unluac-runtime:     return unpack_values(values)
-- unluac-runtime: end
-- unluac-runtime: setfenv(run, setmetatable({ table = { unpack = observe } }, { __index = getfenv() }))
-- unluac-runtime: run()
-- unluac-runtime: assert(calls == 2)
-- unluac-runtime: print("regress_253_luau_deferred_open_setlist#2", calls, weak[1] == nil)
local function build(loaded)
    return { table.unpack(loaded.values or {}) }
end

local values = build({ values = { "a", "b" } })
local empty = build({})
assert(#values == 2 and values[1] == "a" and values[2] == "b")
assert(#empty == 0)
print("regress_253_luau_deferred_open_setlist#1", #values, values[1], values[2])
