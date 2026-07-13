-- regress_82_numeric_for_control_pad#1: a reachable numeric latch exit pad is loop control
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, xs)
    for _ in xs do
        print("regress_82_numeric_for_control_pad#1 body")
        for _ = 1, 3 do
            while b do
                if a or c then
                    continue
                end
            end
        end
        continue
    end
end

run(false, false, false, { 1 })
