-- regress_167_same_header_repeat_short_circuit#1: 外层 repeat 短路尾条件不能与内层 while 合并
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while]]
-- unluac: expect-not-contains [[goto]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[until p1_1 or p1_2]]
-- unluac: expect-not-contains [[if p1_1 then]]
local function flags(a, b, c)
    repeat
        while a do
        end
    until b or c
    return a, b, c
end

local a, b, c = flags(false, true, false)
assert(a == false and b == true and c == false)
print("regress_167_same_header_repeat_short_circuit#1", a, b, c)

local dispatch = {flags}
local cases = {
    {false, false, true}, {false, true, true},
    {false, 0, false}, {false, false, ""},
    {nil, true, nil}, {nil, nil, 0},
}
for i = 1, #cases do
    local input = cases[i]
    local first, second, third = dispatch[1](input[1], input[2], input[3])
    assert(first == input[1] and second == input[2] and third == input[3])
end
-- a 为真或 b/c 同为假时是没有观察点的无限循环；保留其空循环结构。
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- 三结果调用、分派表和循环输入分别保留身份，不留下 buffer COPY 或调用参数别名。
-- unluac: expect-ast-count [[local-binding]] [[11]] [[@proto=0]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[call]] [[5]] [[@proto=0]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[call]] [[0]] [[@proto=1]]
