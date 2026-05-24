-- regress_11_assert_short_circuit_value_merge#1: assert 参数里的布尔短路值合流不应退化成嵌套 if 壳
-- unluac: expect-not-contains [[if ]]
-- unluac: expect-not-contains [[ = assert]]
-- unluac: expect-contains [[ and ]]
local builds = 0
local calls = 0
local function build_values()
    builds = builds + 1
    local values = {}
    values[1] = function()
        calls = calls + 1
        return 10
    end
    values[2] = function()
        calls = calls + 1
        return 20
    end
    return values
end

local values = build_values()
assert(values[1]() == 10 and values[2]() == 20 and values[3] == nil)
assert(calls == 2)
assert(builds == 1)