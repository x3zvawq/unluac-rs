-- regress_177_lua55_generic_for_live_out#1: break 与正常 cleanup 的共同后继持有双 live-out
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[in pairs(p1_0) do]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local function run(values, first, second)
    local left, right = 1, 2
    for _, value in pairs(values) do
        if first then
            left = value
        elseif second then
            right = value
        else
            left, right = right, left
        end
        if left == right then
            break
        end
    end
    return left, right
end

local normal_left, normal_right = run({ 1 }, true, false)
local break_left, break_left_right = run({ 2 }, true, false)
local break_right_left, break_right = run({ 1 }, false, true)
local swap_left, swap_right = run({ 2 }, false, false)
assert(normal_left == 1 and normal_right == 2)
assert(break_left == 2 and break_left_right == 2)
assert(break_right_left == 1 and break_right == 1)
assert(swap_left == 2 and swap_right == 1)
print("regress_177_lua55_generic_for_live_out#1", normal_left, normal_right)
print("regress_177_lua55_generic_for_live_out#break-left", break_left, break_left_right)
print("regress_177_lua55_generic_for_live_out#break-right", break_right_left, break_right)
print("regress_177_lua55_generic_for_live_out#swap", swap_left, swap_right)
