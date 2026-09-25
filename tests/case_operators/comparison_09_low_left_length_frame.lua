-- 左侧既有值与右侧 LEN 保持原比较方向、短路位置及可能的 __len 调用。
-- unluac: expect-count [[ == #]] [[2]]
-- unluac: expect-count [[ ~= #]] [[1]]
-- unluac: expect-not-contains [[= assert]]
-- unluac: expect-ast-max [[local-binding]] [[4]]
-- unluac: expect-count [[or false)]] [[1]] [[@dialect=luau]]
local reads = 0
local row = setmetatable({ 11, 22 }, {
    __len = function()
        reads = reads + 1
        return 2
    end,
})
local function check(value, items, flag)
    assert(value == #items and flag)
    assert(value ~= #items or flag)
    assert(value == #items or false)
    return true
end
-- 保留独立函数调用，避免优化编译器在常量实参处复制或消去被测比较。
local dispatch = { check }
assert(dispatch[1](2, "ab", true))
assert(dispatch[1](2, row, true))
assert(not pcall(dispatch[1], 2, row, false))
assert(not pcall(dispatch[1], 3, row, true))
-- 各 VM 对表 __len 的支持不同，运行比较保留各自原程序的调用次数。
print("low-left-length", reads)
