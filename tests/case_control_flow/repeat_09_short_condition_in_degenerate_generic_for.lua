-- regress_87_repeat_short_condition_in_degenerate_generic_for#1: nested repeat and zero-iteration state stay structured
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[until ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[break]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[8]]
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
local calls = 0
local function iterate(_, control)
    calls = calls + 1
    local next_index = (control or 0) + 1
    if next_index <= 3 then
        return next_index
    end
end
assert(run(true, true, iterate) == 2 and calls == 1)
calls = 0
assert(run(0, "", iterate) == 2 and calls == 1)
assert(run(false, true, {}) == 0)
assert(run(true, nil, {}) == 0)
print("regress_87_repeat_short_condition_in_degenerate_generic_for#1", empty_result, one_result)
