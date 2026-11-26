-- regress_99_nested_loop_branch_state_seed#1: branch seed 必须复用外层 loop state，不能读取未物化的 header phi
-- unluac: expect-not-contains [[r1_0 = r1_2]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
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

local result = run(true, true, false, {})
assert(result == 0)
print("regress_99_nested_loop_branch_state_seed#1", result)
