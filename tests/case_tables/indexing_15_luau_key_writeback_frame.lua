-- 低槽 key 的长度计算与 RHS 调用共用高槽；后继覆盖不能使声明反复下沉、重建。
-- unluac: expect-ast-max [[local-binding]] [[7]] [[@variant=O2]] [[@debug=stripped]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local base, calls, seen = getfenv(), 0, {}
-- unluac-runtime: setfenv(run, setmetatable({tostring = function(value)
-- unluac-runtime:     seen[#seen + 1] = value
-- unluac-runtime:     return base.tostring(value)
-- unluac-runtime: end, print = function(body, first, second)
-- unluac-runtime:     calls = calls + 1
-- unluac-runtime:     assert(body == "x:8" and first == "x" and second == "8")
-- unluac-runtime:     print(body, first, second)
-- unluac-runtime: end}, {__index = base}))
-- unluac-runtime: run()
-- unluac-runtime: assert(calls == 1 and #seen == 2 and seen[1] == "x" and seen[2] == 8)
local values = {}
local key, scratch = 0, 0
local output = print
scratch = #values
key = scratch + 1
scratch = tostring("x")
values[key] = scratch
scratch = #values + 1
local prior = tostring(8)
values[scratch] = prior
key = 8
local template = "%*:%*"
local formatter = template.format
prior = nil
local body = formatter(template, "x", key)
output(body, values[1], values[2])
