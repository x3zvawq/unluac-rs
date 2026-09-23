-- regress_80_same_header_nested_loops#1: Luau shares the numeric-for body header with an inner while
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- 原字节码仍执行 ADD，不能因初始化为常量而删除该运算。
-- unluac: expect-contains [[local r1_0 = 0 + 1]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function run(flag)
    local result = 0
    result = result + 1
    print("regress_80_same_header_nested_loops#1 body", result)
    for _ = 1, 3 do
        while not flag do
            continue
        end
        continue
    end
    return result
end

local result = run(true)
assert(result == 1)
print("regress_80_same_header_nested_loops#1", result)
