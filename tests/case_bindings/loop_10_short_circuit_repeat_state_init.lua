-- regress_208_short_circuit_repeat_state_init#1: branch value init must cover every loop entry
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(enabled, limit)
    local total = 1
    local count = 0
    local delta = enabled and 1 or 0
    repeat
        count = count + 1
        total = total + delta
    until count >= limit
    return total, count
end

local false_flag, false_count = run(false, 3)
local true_flag, true_count = run(true, 4)
assert(false_flag == 1 and false_count == 3)
assert(true_flag == 5 and true_count == 4)
print("regress_208_short_circuit_repeat_state_init#1 false", false_flag, false_count)
print("regress_208_short_circuit_repeat_state_init#1 true", true_flag, true_count)
