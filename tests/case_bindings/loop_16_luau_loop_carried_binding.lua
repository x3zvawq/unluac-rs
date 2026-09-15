-- regress_304_luau_loop_carried_binding: 同槽loop-carried状态直接复用源码binding
-- unluac: expect-contains [[        r1_0 = r1_0 + 1]]
-- unluac: expect-contains [[            r1_1 = r1_1 +]]
-- unluac: expect-not-contains [[        local r1_2 = r1_0 + 1]]
-- unluac: expect-not-contains [[        r1_0, r1_1 =]]
-- unluac: expect-not-contains [[local r1_3]]
-- 返回语法重发原高槽 COPY，循环状态的两个初始化声明继续保留。
-- unluac: expect-contains [[return r1_1, r1_0]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
local function run(enabled, choose_first, limit)
    local count, value = 0, 0
    while count < limit do
        count = count + 1
        if enabled then
            local step = choose_first and 1 or 2
            value = value + step
        end
    end
    return value, count
end

local value1, count1 = run(true, false, 3)
local value2, count2 = run(false, true, 4)
assert(value1 == 6 and count1 == 3 and value2 == 0 and count2 == 4)
for limit = -1, 4 do
    local expected_count = math.max(limit, 0)
    local first, count = run(true, true, limit)
    assert(first == expected_count and count == expected_count)
    local second, second_count = run(0, false, limit)
    assert(second == expected_count * 2 and second_count == expected_count)
    local disabled, disabled_count = run(nil, true, limit)
    assert(disabled == 0 and disabled_count == expected_count)
end
assert(select("#", run(false, true, 0)) == 2)
print("regress_304_luau_loop_carried_binding", value1, count1, value2, count2)
