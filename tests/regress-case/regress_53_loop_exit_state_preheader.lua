-- regress_53_loop_exit_state_preheader#1: exit-only loop state 使用 preheader 初值
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[in ipairs(p1_0) do]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function first_large(list)
    local found = false
    local value = nil

    for _, item in ipairs(list) do
        if item > 10 then
            found = true
            value = item
            break
        end
    end

    if found then
        return value
    end
    return 0
end

print(
    "regress_53_loop_exit_state_preheader#1",
    first_large({ 1, 12, 3 }),
    first_large({ 1, 2, 3 })
)
