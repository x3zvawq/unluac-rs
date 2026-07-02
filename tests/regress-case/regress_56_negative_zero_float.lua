-- unluac: expect-contains [[-0.0]]
local function run()
    local value = -0.0
    return tostring(1 / value)
end

print("regress_56_negative_zero_float", run())
