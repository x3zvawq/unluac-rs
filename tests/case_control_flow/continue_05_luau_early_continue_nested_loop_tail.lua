-- regress_118_luau_early_continue_nested_loop_tail#1: early-continue guard 不抢占 nested generic-for tail
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[if p1_0 then]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[r1_0 = r1_3]]
local function run(a, b, c, xs)
    local x = 0
    for k, v in xs do
        repeat
            if a then
                if xs[x] then break end
            else
                repeat
                    break
                until b
                if xs[x] then break end
                if a then continue end
            end
            for inner_k, inner_v in xs do
                x = x + 1
                x = x + 1
                x = x + 1
            end
        until b
    end
    return x
end

print("regress_118_luau_early_continue_nested_loop_tail#1", run(false, true, false, { 1, 2 }))
print("regress_118_luau_early_continue_nested_loop_tail#2", run(true, true, false, { 1, 2 }))
print(
    "regress_118_luau_early_continue_nested_loop_tail#3",
    run(false, true, false, { [0] = true, 1, 2 })
)
