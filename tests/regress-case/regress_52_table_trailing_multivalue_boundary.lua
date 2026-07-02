-- regress_52_table_trailing_multivalue_boundary#1: 尾部多返回之后的字段不能继续吸收入同一构造器
-- unluac: expect-not-contains [[unluac error]]
local function many()
    return "a", "b"
end

local function build(label)
    local values = { many() }
    values.label = label
    return #values, values[1], values[2], values.label
end

local count, first, second, label = build("kept")
print(
    "regress_52_table_trailing_multivalue_boundary#1",
    count,
    first,
    second,
    label
)
