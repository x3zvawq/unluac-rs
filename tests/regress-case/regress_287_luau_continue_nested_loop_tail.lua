-- regress_287_luau_continue_nested_loop_tail: continue前的嵌套loop tail必须由外层branch共享
-- unluac: expect-contains [[continue]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[r1_0 = r1_0 + r1_2]]
local function run(a, c, n, inner_n)
    local x = 0
    for i = 1, n do
        if a then
            if c then
                continue
            end
        else
            x = x + i
        end
        for j = 1, inner_n do
            x = x + j
        end
    end
    return x
end

print(
    "regress_287_luau_continue_nested_loop_tail",
    run(false, false, 3, 2),
    run(false, false, 3, 0),
    run(true, false, 3, 2),
    run(true, true, 3, 2)
)
