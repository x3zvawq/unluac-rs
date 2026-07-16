-- regress_226_repeat_direct_break_condition_owner#1: body break 不能消费 repeat 尾条件 owner
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function run(stop, left, right)
    local x = 0
    repeat
        x = x + 1
        if stop then
            break
        end
    until (left and right) or x > 3
    return x
end

print(run(false, false, false), run(false, true, true), run(true, false, false))
