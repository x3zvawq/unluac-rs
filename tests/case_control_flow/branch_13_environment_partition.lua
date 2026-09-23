-- 两个 a 检查处于不同短路入口，不能仅按值等价提取公共条件。
-- unluac: expect-contains [[return (p1_0 and p1_1 or p1_0 and p1_2) and p1_3 and p1_4 and p1_5]]
-- unluac: expect-not-contains [[if p1_0 then]]

local function choose(a, b, c, d, e, f)
    return ((a and b) or (a and c)) and d and e and f
end

local result = choose(true, false, true, 4, 5, 6)
assert(result == 6)
assert(choose(false, true, true, 4, 5, 6) == false)
assert(choose(nil, true, true, 4, 5, 6) == nil)
assert(choose(true, true, false, 4, 5, 6) == 6)
assert(choose(true, false, nil, 4, 5, 6) == nil)
assert(choose(true, false, true, false, 5, 6) == false)
assert(choose(true, false, true, 4, nil, 6) == nil)
print("regress_426_decision_environment_partition", result)
