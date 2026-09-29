-- 低槽表与动态键直接供比较读取，短路右臂的 GETTABLE 不额外物化为参数声明。
-- unluac: expect-contains [[assert(not ]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=0]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[if]] [[0]]
local function check(values, key, enabled)
    assert(not enabled or values[key] == 30)
end

local trace = {}
local values = setmetatable({}, {
    __index = function(_, key)
        trace[#trace + 1] = tostring(key)
        return 30
    end,
})
local checks = {check}
checks[1](values, "skipped", false)
assert(#trace == 0)
checks[1](values, "field", true)
checks[1](values, 7, true)
assert(table.concat(trace, ",") == "field,7")
print("dynamic-key-operand", table.concat(trace, ","))
-- 禁用路径连非法 base 都不能索引；0 和空字符串则仍启用动态读取。
checks[1](nil, "skipped", false)
checks[1](nil, "skipped", nil)
assert(#trace == 2)
checks[1](values, "zero", 0)
checks[1](values, "empty", "")
checks[1](values, true, true)
values.direct = 30
checks[1](values, "direct", true)
values.wrong = 31
assert(not pcall(checks[1], values, "wrong", true))
assert(not pcall(checks[1], nil, "bad-base", true))
assert(select("#", checks[1](values, "arity", true)) == 0)
assert(table.concat(trace, ",") == "field,7,zero,empty,true,arity")
