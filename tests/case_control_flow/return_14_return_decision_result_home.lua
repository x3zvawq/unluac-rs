-- 残余 Decision 保留原结果 home，循环后的条件更新不重建空 carrier。
-- unluac: expect-ast-min [[while]] [[1]]
-- unluac: expect-ast-min [[if]] [[2]]
-- unluac: expect-ast-min [[break]] [[1]]
-- unluac: expect-not-line [[local r1_1]]
local function run(flag, limit)
    local result = 0
    while flag do
        result = result + 1
        if result >= limit then
            break
        end
    end
    if flag then
        result = result + 10
    end
    return result
end

assert(run(true, 2) == 12)
assert(run(false, 2) == 0)
local comparisons = 0
local compare_mt = { __le = function(left, right)
    comparisons = comparisons + 1
    return left.n <= right.n
end }
local function after_compare(left, right)
    local result = 0
    if left <= right then
        result = result + 10
    end
    return result
end
local left = setmetatable({ n = 1 }, compare_mt)
local right = setmetatable({ n = 2 }, compare_mt)
assert(after_compare(left, right) == 10)
assert(after_compare(right, left) == 0 and comparisons == 2)

-- 原输入另有快照时，延后物化不得授予旧值/新值共址的额外许可。
local function snapshot(flag, value)
    local old = value
    if flag then
        value = value + 10
    end
    return value, old
end
local additions = 0
local box = setmetatable({ n = 7 }, { __add = function(value, amount)
    additions = additions + 1
    collectgarbage("collect")
    assert(value.n == 7 and amount == 10)
    return false
end })
local changed, old = snapshot(true, box)
assert(changed == false and old == box and additions == 1)
local unchanged, same = snapshot(false, box)
assert(unchanged == box and same == box and additions == 1)
print("return-decision-home", run(true, 2), run(false, 2), comparisons, additions)
