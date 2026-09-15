-- regress_213_numeric_for_short_circuit_assignment#1: loop owner keeps short-circuit state writes
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local function run(enabled, limit)
    local flag = 0
    for count = 1, limit do
        flag = enabled and (count + 1) or (count + 2)
    end
    return flag
end

local enabled, disabled = run(true, 4), run(false, 5)
assert(enabled == 5 and disabled == 7)
print("regress_213_numeric_for_short_circuit_assignment#1", enabled, disabled)
