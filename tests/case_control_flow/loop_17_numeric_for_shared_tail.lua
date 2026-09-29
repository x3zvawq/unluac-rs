-- regress_180_numeric_for_shared_tail#1: 分支汇入 numeric-for 共享尾时不能提前 continue
-- unluac: expect-ast-min [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-min [[if]] [[1]] [[@proto=1]]

local function run(n, value, cond)
    local sink = {}
    for _ = 0, n - 1 do
        local current = value
        if current == 1 then
            sink[1] = cond and 2 or 3
        elseif current == 2 then
            sink[1] = 4
        end
        value = value + 1
    end
    return value, sink[1]
end

local value, sink = run(1, 2, true)
assert(value == 3 and sink == 4)
print("regress_180_numeric_for_shared_tail#1", value, sink)

local dispatch = {run}
local cases = {
    {0, 1, true, 1, nil}, {-1, 1, true, 1, nil},
    {1, 1, true, 2, 2}, {1, 1, false, 2, 3},
    {1, 1, nil, 2, 3}, {1, 1, 0, 2, 2},
    {2, 1, false, 3, 4}, {4, 0, false, 4, 4},
    {3, 3, true, 6, nil}, {2.5, 1, false, 3, 4},
}
for i = 1, #cases do
    local input = cases[i]
    local final, output = dispatch[1](input[1], input[2], input[3])
    assert(final == input[4] and output == input[5])
end
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[goto]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]]
-- current 快照、共享尾写回和两个表写保持原位；分支不能提前退出本轮。
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[call]] [[0]] [[@proto=1]]
-- 构造器与多结果调用不引入额外 COPY holder 或中间比较变量。
-- unluac: expect-ast-count [[local-binding]] [[9]] [[@proto=0]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[call]] [[5]] [[@proto=0]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=0]]
