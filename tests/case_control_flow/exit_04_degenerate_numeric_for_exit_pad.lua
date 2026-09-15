-- regress_81_degenerate_numeric_for_exit_pad#1: Luau keeps an unreachable latch exit jump pad
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[ = 1, 3 do]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[(function()]]
local function run(xs)
    for _ in xs do
        print("regress_81_degenerate_numeric_for_exit_pad#1 body")
        for _ = 1, 3 do
            break
        end
        continue
    end
end

run({ 1 })
