-- unluac: expect-contains [[ == nil]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[if]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[8]]
-- 短路函数的两个参数比较均须保留；Boolean 物化许可不能合并或复制这些 __eq。
-- unluac: expect-count [[p1_0 == nil]] [[2]]

local ffi = require("ffi")

ffi.cdef[[
typedef struct {
    int value;
} regress_391_value;
]]

local equality_hits = 0
local value_type = ffi.metatype("regress_391_value", {
    __eq = function(value)
        equality_hits = equality_hits + 1
        return value.value ~= 0
    end,
})

local function observe_equality(value)
    if value == nil then
        return equality_hits
    else
        return equality_hits
    end
end

assert(observe_equality(value_type(1)) == 1)

local function observe_twice(value, skip)
    local result = not skip and (value == nil) and (value == nil)
    return result, equality_hits
end

equality_hits = 0
local result, hits = observe_twice(value_type(1))
assert(result == true and hits == 2)

-- 首个比较返回 false 时只执行一次；入口跳过时两次比较都不能触发。
equality_hits = 0
result, hits = observe_twice(value_type(0), false)
assert(result == false and hits == 1)
equality_hits = 0
result, hits = observe_twice(value_type(1), true)
assert(result == false and hits == 0)

-- 同值分支的 false 路径仍必须先求比较；数值 0 和空串作为 skip 均为真。
equality_hits = 0
assert(observe_equality(value_type(0)) == 1)
assert(select("#", observe_equality(value_type(1))) == 1)
assert(equality_hits == 2)
equality_hits = 0
result, hits = observe_twice(value_type(1), 0)
assert(result == false and hits == 0)
result, hits = observe_twice(value_type(1), "")
assert(result == false and hits == 0)
result, hits = observe_twice(nil, false)
assert(result == true and hits == 0)
result, hits = observe_twice(false, false)
assert(result == false and hits == 0)
assert(select("#", observe_twice(value_type(1), false)) == 2)
assert(equality_hits == 2)
