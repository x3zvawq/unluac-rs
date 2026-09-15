-- regress_227_while_short_condition_body_backedge#1: while body 不能冒充 repeat 回边 pad
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[while (p1_0 or p1_1) and p1_2 do]]
local function run(a, b, c)
    local count = 0
    while (a or b) and c do
        count = count + 1
        a = false
        b = false
    end
    return count
end

local left = run(true, false, true)
local right = run(false, true, true)
local blocked = run(true, true, false)
assert(left == 1 and right == 1 and blocked == 0)
print(left, right, blocked)
