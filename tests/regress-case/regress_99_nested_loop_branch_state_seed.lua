-- regress_99_nested_loop_branch_state_seed#1: branch seed 必须复用外层 loop state，不能读取未物化的 header phi
-- unluac: expect-contains [[local r1_0 = 0]]
-- unluac: expect-contains [[for r1_1 in p1_3 do]]
-- unluac: expect-not-contains [[local r1_2]]
-- unluac: expect-not-contains [[r1_0 = r1_2]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, xs)
    local x = 0
    repeat
        for _ in xs do
            repeat
                if a or c then
                    continue
                end
                repeat
                    x = x + 1
                    x = x + 1
                until xs[x]
                x = x + 1
            until not b
        end
        if a and b then
            break
        end
    until a
    print(x)
    return x
end

print("regress_99_nested_loop_branch_state_seed#1", run(true, true, false, {}))
