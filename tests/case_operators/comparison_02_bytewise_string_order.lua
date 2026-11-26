-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- 原 NOT 的短路参数保留两次取反，不拆出 callee 或首叶 Boolean 临时变量。

-- 四结果 CALL 的末参数在完整结果区之后准备索引键，声明与调用须保持同一初始化。

local function compare_strings()
    return "ä" < "z", "ä" <= "z"
end

local less, less_equal = compare_strings()
assert(not less and not less_equal)

local function compare_values(left, right)
    return left < right, left <= right, left > right, left >= right
end
-- 预期按原始字节及前缀长度给出，不用另一个关系表达式充当同源 oracle。
local cases = {
    { "", "", false, true, false, true },
    { "", "\000", true, true, false, false },
    { "\000", "\000\000", true, true, false, false },
    { "a\000b", "a\000c", true, true, false, false },
    { "\127", "\128", true, true, false, false },
    { "\255", "ä", false, false, true, true },
    { "ä", "z", false, false, true, true },
}
for index = 1, 7 do
    local row = cases[index]
    local lt, le, gt, ge = compare_values(row[1], row[2])
    assert(lt == row[3] and le == row[4] and gt == row[5] and ge == row[6])
    assert(select("#", compare_values(row[1], row[2])) == 4)
end
assert(select("#", compare_strings()) == 2)

return less, less_equal
