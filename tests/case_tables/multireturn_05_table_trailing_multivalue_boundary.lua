-- regress_52_table_trailing_multivalue_boundary#1: 尾部多返回之后的字段不能继续吸收入同一构造器
-- unluac: expect-not-contains [[end)(]]
-- unluac: expect-not-contains [[unluac error]]
-- 构造器仅含一个开放尾；label 保持后续写入，不引入额外表根或返回接棒。
-- unluac: expect-ast-count [[table-constructor]] [[1]]
-- unluac: expect-ast-count [[table-list-field]] [[1]]
-- unluac: expect-ast-count [[table-record-field]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[8]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=2]]
local calls = 0
local function many()
    calls = calls + 1
    return "a", "b"
end

local function build(label)
    local values = { many() }
    values.label = label
    return #values, values[1], values[2], values.label
end

local count, first, second, label = build("kept")
assert(count == 2 and first == "a" and second == "b" and label == "kept")
assert(calls == 1, calls)
print(
    "regress_52_table_trailing_multivalue_boundary#1",
    count,
    first,
    second,
    label
)
