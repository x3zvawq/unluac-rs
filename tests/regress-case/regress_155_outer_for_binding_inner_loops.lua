-- regress_155_outer_for_binding_inner_loops#1: 内层while写回外层generic-for binding
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
local function run_while(values)
    local total = 0
    for _, value in ipairs(values) do
        while value > 0 do
            value = value - 1
            total = total + 1
        end
    end
    return total
end

local function run_repeat(values)
    local total = 0
    for _, value in ipairs(values) do
        repeat
            value = value - 1
            total = total + 1
        until value <= 0
    end
    return total
end

print("regress_155_outer_for_binding_inner_loops#1", run_while({ 1, 2 }))
print("regress_155_outer_for_binding_inner_loops#2", run_repeat({ 1, 2 }))
