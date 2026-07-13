-- regress_93_numeric_for_continue_pad_state#1: tail continue pad belongs to the numeric-for body
-- regress_93_numeric_for_continue_pad_state#2: nested loop phi use must keep the outer repeat state writable
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function empty_continue(stop)
    local x = 0
    repeat
        for _ = 1, 3 do
            continue
        end
        x = x + 1
    until stop
    return x
end

local function carried_state(stop)
    local x = 0
    repeat
        for i = 1, 3 do
            x = x + i
            continue
        end
        x = x + 1
    until stop
    return x
end

print("regress_93_numeric_for_continue_pad_state#1", empty_continue(true))
print("regress_93_numeric_for_continue_pad_state#2", carried_state(true))
