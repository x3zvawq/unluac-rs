-- regress_87_repeat_short_condition_in_degenerate_generic_for#1: nested repeat and zero-iteration state stay structured
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[until ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    for _ in xs do
        repeat
            x = x + 1
            x = x + 1
        until a and b
        break
    end
    return x
end

local empty_result = run(true, true, {})
local one_result = run(true, true, { true })
assert(empty_result == 0 and one_result == 2)
print("regress_87_repeat_short_condition_in_degenerate_generic_for#1", empty_result, one_result)
