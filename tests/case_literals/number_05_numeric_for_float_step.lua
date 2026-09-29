-- unluac: expect-contains [[, 1.0 do]]
-- unluac: expect-contains [[, -1.0 do]]
-- unluac: expect-ast-count [[numeric-for]] [[2]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[10]]
local function run()
    local last_type
    local visits, sum = 0, 0
    for index = 1, 3, 1.0 do
        last_type = math.type(index)
        assert(last_type == "float")
        visits = visits + 1
        sum = sum + index
    end
    for index = 3, 1, -1.0 do
        last_type = math.type(index)
        assert(last_type == "float")
        visits = visits + 1
        sum = sum + index
    end
    return last_type, visits, sum
end

local last_type, visits, sum, extra = run()
assert(last_type == "float" and visits == 6 and sum == 12 and extra == nil)
print("regress_61_numeric_for_float_step", last_type)
