-- 原数组 batch、内表缓冲槽与 iterator dispatch endpoint 必须由完整事务共同消费。
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-contains [[in ipairs(]]
-- unluac: expect-not-contains [[ = nil]]
-- 数组和内表直接初始化；迭代器准备不留下额外绑定。
-- unluac: expect-ast-count [[table-constructor]] [[7]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[5]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
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
local visited = 0
for index, row in ipairs(rows) do
    visited = visited + 1
    assert(index == visited and row[1] == identity)
    assert(row[1](row[2]) == index)
    print("nested-row", index, row[2])
end
assert(visited == 6 and #rows == 6)
