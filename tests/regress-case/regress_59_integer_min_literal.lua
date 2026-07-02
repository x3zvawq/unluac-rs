-- unluac: expect-contains [[-0x8000000000000000]]
local function run()
    local value = -0x8000000000000000
    return value, math.type(value)
end

print("regress_59_integer_min_literal", run())
