-- regress_260_lua55_degenerate_generic_shared_exit#1: 零次迭代出口与 body 出口共享 continuation
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[in pairs(p1_2) do]]
-- unluac: expect-contains [[while true do]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    for _ in pairs(xs) do
        repeat
            x = x + 1
            x = x + 1
        until a and b
        break
    end
    return x
end

print(
    "regress_260_lua55_degenerate_generic_shared_exit#1",
    run(true, true, {}),
    run(true, true, { true })
)
