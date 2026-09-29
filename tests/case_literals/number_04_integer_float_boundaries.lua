-- unluac: expect-contains [[-0x8000000000000000]]
-- unluac: expect-not-contains [[end)(]]
-- 原 value 是多值 RETURN 前的低槽前缀；检查整数发射及运行类型，不要求删除该声明。
-- unluac: expect-contains [[math.type(]]
-- unluac: expect-not-contains [[local r1_1 = r1_0]]
-- unluac: expect-ast-count [[function]] [[5]]
-- unluac: expect-ast-max [[local-binding]] [[24]]
local function integer_min_literal()
    local value = -0x8000000000000000
    return value, math.type(value)
end

local state = 1
local function mutate()
    state = 2
    return 0
end

local function preserve_snapshot()
    local snapshot = state
    return mutate(), snapshot
end

local _, snapshot, snapshot_extra = preserve_snapshot()
assert(_ == 0 and snapshot == 1 and state == 2 and snapshot_extra == nil)
local integer_value, integer_type, integer_extra = integer_min_literal()
assert(integer_value == -0x8000000000000000 and integer_type == "integer" and integer_extra == nil)
print("regress_59_integer_min_literal", integer_value, integer_type)

-- unluac: expect-contains [[1.0]]
-- unluac: expect-contains [[-2.0]]
-- unluac: expect-contains [[(1/0)]]
-- unluac: expect-not-contains [[return (1/0)]]
local function integral_float_literals()
    local positive = 1.0
    local negative = -2.0
    return math.type(positive), math.type(negative), positive, negative
end

local positive_type, negative_type, positive_value, negative_value, float_extra = integral_float_literals()
assert(positive_type == "float" and negative_type == "float")
assert(positive_value == 1 and negative_value == -2 and float_extra == nil)
print("regress_60_integral_float_literal", positive_type, negative_type)

local function nonfinite_copy()
    local value = 1e999
    print("regress_60_nonfinite_barrier")
    return value
end

local nonfinite, nonfinite_extra = nonfinite_copy()
assert(nonfinite == math.huge and nonfinite_extra == nil)
print("regress_60_nonfinite_copy", nonfinite)
