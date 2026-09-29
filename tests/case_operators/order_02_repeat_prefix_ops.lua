-- regress_245_observable_repeat_prefix_ops: 未使用的运算结果仍可调用 metamethod
-- unluac: expect-contains [[repeat]]
-- unluac: expect-ast-count [[function]] [[4]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[10]]

local binary_calls = 0
local unary_calls = 0
local concat_calls = 0
local trace = ""
local obj = setmetatable({}, {
    __add = function()
        trace = trace .. "B"
        binary_calls = binary_calls + 1
        return 0
    end,
    __unm = function()
        trace = trace .. "U"
        unary_calls = unary_calls + 1
        return 0
    end,
    __concat = function()
        trace = trace .. "C"
        concat_calls = concat_calls + 1
        return ""
    end,
})
local checks = 0
local function done()
    trace = trace .. "T"
    checks = checks + 1
    return checks == 2
end

repeat
    local unused_binary = obj + 1
    local unused_unary = -obj
    local unused_concat = obj .. "x"
until done()

assert(binary_calls == 2)
assert(unary_calls == 2)
assert(concat_calls == 2)
assert(checks == 2)
assert(trace == "BUCTBUCT", trace)

print("regress_245_observable_repeat_prefix_ops")
