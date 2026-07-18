-- regress_285_short_circuit_nested_break_tail: 双臂branch不能伪装成same-header loop control
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-contains [[ and ]]
-- unluac: expect-contains [[ or ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c)
    local x = 0
    for _ = 1, 3 do
        if (a and b) or c then
            if c then
                break
            end
            x = x + 1
        else
            x = x + 2
        end
        x = x + 3
    end
    return x
end

print(
    "regress_285_short_circuit_nested_break_tail",
    run(false, false, false),
    run(true, true, false),
    run(false, false, true)
)
