-- unluac: expect-contains [[ == nil]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[if]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[6]]
-- 参数来源与构造器事务须完整消费，不把开放返回拆为残余 SETLIST。
-- unluac: expect-contains [[local r0_4 = { r0_2(1), r0_2(2) }]]
-- unluac: expect-contains [[assert(r0_4[1] == nil and r0_4[2] == nil)]]
local ffi = require("ffi")

ffi.cdef[[
typedef struct {
    int value;
} regress_390_value;
]]

local equality_hits = 0
local value_type = ffi.metatype("regress_390_value", {
    __eq = function()
        equality_hits = equality_hits + 1
        return true
    end,
})

local function compare_with_nil(value)
    local unused = value == nil
    if 1 == 1 then
        return equality_hits
    else
        return unused
    end
end

assert(compare_with_nil(value_type(1)) == 1)

-- 表索引组成 Boolean 参数时，cdata 与 nil 的比较仍各调用一次 __eq。
-- 不得把已知原始值 RHS 当作一般无元方法比较，或跳过短路右臂。
local values = { value_type(1), value_type(2) }
equality_hits = 0
assert(values[1] == nil and values[2] == nil)
assert(equality_hits == 2)

-- 原始值不触发 cdata 元方法；传回调用次数的返回包始终只有一个结果。
equality_hits = 0
assert(compare_with_nil(nil) == 0)
assert(compare_with_nil(false) == 0)
assert(compare_with_nil(0) == 0)
assert(compare_with_nil("") == 0)
assert(select("#", compare_with_nil(value_type(-1))) == 1)
assert(equality_hits == 1)
