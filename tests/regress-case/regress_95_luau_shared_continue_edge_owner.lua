-- regress_95_luau_shared_continue_edge_owner#1: indirect continue pad belongs to the outer while
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, should_break)
    local x = 0
    while not b do
        if a then
            continue
        end
        repeat
            for _ = 1, 3 do
                continue
            end
            x = x + 1
        until b
        if should_break then
            break
        end
    end
    return x
end

print("regress_95_luau_shared_continue_edge_owner#1", run(false, true, false))
