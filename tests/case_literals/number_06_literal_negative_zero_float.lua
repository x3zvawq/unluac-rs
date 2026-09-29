-- unluac: expect-contains [[-0.0]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[3]]
local function run()
    local value = -0.0
    assert(value == 0 and 1 / value == -math.huge and math.type(value) == "float")
    return tostring(1 / value)
end

local result = run()
assert(result == tostring(-math.huge))
print("regress_56_negative_zero_float", result)
