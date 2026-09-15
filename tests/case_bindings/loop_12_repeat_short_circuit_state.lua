-- regress_215_repeat_short_circuit_state#1: emitted state update must not be inlined again
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local function run(enabled, limit)
    local flag, count = 0, 0
    repeat
        count = count + 1
        flag = enabled and (count + 1) or (count + 2)
    until count >= limit
    return flag, count
end

local true_flag, true_count = run(true, 4)
local false_flag, false_count = run(false, 5)
assert(true_flag == 5 and true_count == 4)
assert(false_flag == 7 and false_count == 5)
print("regress_215_repeat_short_circuit_state#1 true", true_flag, true_count)
print("regress_215_repeat_short_circuit_state#1 false", false_flag, false_count)
