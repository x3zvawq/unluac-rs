-- regress_226_repeat_direct_break_condition_owner#1: body break 不能消费 repeat 尾条件 owner
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-min [[repeat]] [[1]] [[@proto=1]]
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

local exhausted = run(false, false, false)
local condition = run(false, true, true)
local stopped = run(true, false, false)
assert(exhausted == 4 and condition == 1 and stopped == 1)
print(exhausted, condition, stopped)
