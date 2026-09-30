-- 残余 Decision 保留原结果 home，循环后的条件更新不重建空 carrier。
-- unluac: expect-ast-min [[while]] [[1]]
-- unluac: expect-ast-min [[if]] [[2]]
-- unluac: expect-ast-min [[break]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]]
-- 连续 nil 参数保持为原调用值包，不额外物化调用者的准备变量。
-- unluac: expect-count [[(nil, nil)]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=4]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=4]]
-- unluac: expect-ast-count [[local-binding]] [[16]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[break]] [[1]]
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

assert(run(nil, nil) == 0)
assert(run(0, 0) == 11 and run("", -2) == 11)
assert(run(true, 3) == 13)
left.n, right.n = 4, 4
assert(after_compare(left, right) == 10 and comparisons == 3)
assert(after_compare(right, left) == 10 and comparisons == 4)
changed, old = snapshot(0, 7)
assert(changed == 17 and old == 7)
changed, old = snapshot(nil, false)
assert(changed == false and old == false)
changed, old = snapshot("", box)
assert(changed == false and old == box and additions == 2)
