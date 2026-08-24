-- regress_176_sibling_latch_terminal_loop#1: 多个 sibling latch 共同回到 while-true header
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[until p1_1 and p1_2]]

local function run(a, b, c)
    while true do
        if a then
            if b then
                return 1
            end
        elseif c then
            return 2
        end
        if b and c then
            return 3
        end
    end
end

print("regress_176_sibling_latch_terminal_loop#1", run(false, false, true))
