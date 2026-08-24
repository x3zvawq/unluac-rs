-- unluac: expect-contains [[1.0]]
-- unluac: expect-contains [[-2.0]]
-- unluac: expect-contains [[(1/0)]]
-- unluac: expect-not-contains [[return (1/0)]]
local function run()
    local positive = 1.0
    local negative = -2.0
    return math.type(positive), math.type(negative)
end

print("regress_60_integral_float_literal", run())

local function nonfinite_copy()
    local value = 1e999
    print("regress_60_nonfinite_barrier")
    return value
end

print("regress_60_nonfinite_copy", nonfinite_copy())
