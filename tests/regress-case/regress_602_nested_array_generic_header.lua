-- 原数组 batch、内表缓冲槽与 iterator dispatch endpoint 必须由完整事务共同消费。
-- unluac: expect-ast-min [[generic-for]] [[1]]
-- unluac: expect-contains [[in ipairs(]]
-- unluac: expect-not-contains [[ = nil]]
local function identity(value)
    return value
end
local rows = {
    { identity, 1 },
    { identity, 2 },
    { identity, 3 },
    { identity, 4 },
    { identity, 5 },
    { identity, 6 },
}
for index, row in ipairs(rows) do
    assert(row[1](row[2]) == index)
    print("nested-row", index, row[2])
end
