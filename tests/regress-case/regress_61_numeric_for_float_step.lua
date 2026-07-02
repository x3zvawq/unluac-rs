-- unluac: expect-contains [[, 1.0 do]]
local function run()
    local last_type
    for index = 1, 3, 1.0 do
        last_type = math.type(index)
    end
    return last_type
end

print("regress_61_numeric_for_float_step", run())
