-- 未知键遮蔽此前的待定整数写入，但不能遮蔽之后才出现的待定字段。
local function before(k)
    return {[3] = 30, [k] = 40, [1] = 10, [2] = 20}
end

local function after(k)
    return {[k] = 40, [3] = 30, [1] = 10, [2] = 20}
end

local function duplicate(k)
    return {[3] = 30, [k] = 40, [3] = 50, [1] = 10, [2] = 20}
end

for _, k in ipairs({3, 4}) do
    for _, build in ipairs({before, after, duplicate}) do
        local result = build(k)
        print(k, result[1], result[2], result[3], result[4])
    end
end

-- 多个未知键共享一次位置事实；不能对每个未知键重扫全部待定字段。
local function many(k1, k2, k3, k4, k5, k6, k7, k8)
    return {
        [17] = 17, [18] = 18, [19] = 19, [20] = 20,
        [21] = 21, [22] = 22, [23] = 23, [24] = 24,
        [k1] = 1, [k2] = 2, [k3] = 3, [k4] = 4,
        [k5] = 5, [k6] = 6, [k7] = 7, [k8] = 8,
    }
end

local result = many(101, 102, 103, 104, 105, 106, 107, 108)
local sum = 0
for i = 1, 8 do
    sum = sum + result[16 + i] + result[100 + i]
end
assert(sum == 200)
print(sum)
