-- regress_77_loop_nested_break_continuation#1: nested break must not hide the local loop continuation
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[r1_0 = r1_1]]
-- unluac: expect-not-contains [[r2_0 = r2_1]]
local function repeat_branch(a, c)
    local x = 0
    repeat
        if x < 3 then
            if c then
                break
            end
        else
            x = x + 1
        end
    until a or c
    return x
end

local function while_branch(a, b, c)
    local x = 0
    while a do
        if b then
            x = x + 1
            if c then
                break
            end
        else
            x = x + 2
        end
    end
    return x
end

local repeat_break = repeat_branch(false, true)
local repeat_until = repeat_branch(true, false)
local repeat_both = repeat_branch(true, true)
local while_break = while_branch(true, true, true)
assert(repeat_break == 0 and repeat_until == 0 and repeat_both == 0 and while_break == 1)
print("regress_77_loop_nested_break_continuation#1", repeat_break, repeat_until, repeat_both, while_break)
