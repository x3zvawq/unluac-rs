-- regress_153_lua55_generic_for_close_break_pad#1: generic-for 的 CLOSE fallthrough 出口保持本轮 break owner
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[local r1_3]]
-- unluac: expect-contains [[r1_0 = r1_0 + r1_2]]
-- unluac: expect-contains [[r1_0 = r1_0 + 7]]
local function run(xs, stop)
    local total = 0
    for i, v in ipairs(xs) do
        if v < 0 then
            if i == stop then
                break
            end
        else
            total = total + v
        end
        total = total + 7
    end
    return total
end

local stop_three = run({ 2, 0, -1, 4 }, 3)
local stop_two = run({ 2, 0, -1, 4 }, 2)
assert(stop_three == 16 and stop_two == 34)
print(
    "regress_153_lua55_generic_for_close_break_pad#1",
    stop_three,
    stop_two
)
