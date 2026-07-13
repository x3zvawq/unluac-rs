-- regress_91_branch_owned_multi_entry_loop_state#1: branch target must own a nested loop's multi-entry state
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c)
    local x = 0
    for _ = 1, 3 do
        x = x + 1
    end
    if a then
        if c then
            x = x + 1
        end
        repeat
        until b
    end
    return x
end

print(
    "regress_91_branch_owned_multi_entry_loop_state#1",
    run(true, true, true),
    run(false, true, true)
)
