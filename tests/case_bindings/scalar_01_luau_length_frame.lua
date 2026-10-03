-- 长度及其数值计算不能制造保活根，阻塞同槽字段读取与后继调用帧。
-- unluac: expect-ast-max [[local-binding]] [[8]] [[@variant=O2]] [[@debug=stripped]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local base, calls = getfenv(), 0
-- unluac-runtime: setfenv(run, setmetatable({print = function(value)
-- unluac-runtime:     calls = calls + 1
-- unluac-runtime:     assert(value == "[v:4] len=3")
-- unluac-runtime:     print(value)
-- unluac-runtime: end}, {__index = base}))
-- unluac-runtime: run()
-- unluac-runtime: assert(calls == 1)
local values = {}
local prior = tostring(4)
values[#values + 1] = prior
local formatter = ("%*:%*").format
prior = nil
local body = formatter
body = body("%*:%*", "v", 4)
formatter = "[%*] len=%*"
local length = #body
local body_arg, length_arg = body, length
local result = formatter:format(body_arg, length_arg)
print(result)
assert(values[1] == "4")
