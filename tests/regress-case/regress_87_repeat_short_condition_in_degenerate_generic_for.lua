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

print(
    "regress_87_repeat_short_condition_in_degenerate_generic_for#1",
    run(true, true, {}),
    run(true, true, { true })
)
