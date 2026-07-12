-- regress_74_degenerate_numeric_for#1: unreachable latch still belongs to a numeric for
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[ = 1, 3 do]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

for _ = 1, 3 do
    break
end

print("regress_74_degenerate_numeric_for#1")

local function terminal_body(flag)
    for index = 1, 3 do
        if flag then
            break
        end
        return index
    end
    return 0
end

print("regress_74_degenerate_numeric_for#2", terminal_body(true), terminal_body(false))
