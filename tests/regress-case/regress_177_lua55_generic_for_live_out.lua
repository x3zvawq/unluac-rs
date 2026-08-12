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

print("regress_177_lua55_generic_for_live_out#1", run({ 1 }, true, false))
print("regress_177_lua55_generic_for_live_out#break-left", run({ 2 }, true, false))
print("regress_177_lua55_generic_for_live_out#break-right", run({ 1 }, false, true))
print("regress_177_lua55_generic_for_live_out#swap", run({ 2 }, false, false))
