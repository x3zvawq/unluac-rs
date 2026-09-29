-- regress_236_table_constructor_pending_alias: future integer fields do not cross aliasing writes
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- 交错构造及嵌套开放尾保持在原初始化中，不拆成独立写表或临时 callee。
-- unluac: expect-ast-count [[table-constructor]] [[5]] [[@proto=0]]
-- unluac: expect-ast-min [[table-list-field]] [[5]] [[@proto=0]]
-- unluac: expect-ast-count [[table-list-field]] [[7]] [[@proto=0]] [[@dialect=luajit]]
-- 构造后的常量键准备复用旧槽，完整 assert 不应残留预写与读取别名。
-- unluac: expect-ast-count [[local-binding]] [[9]] [[@proto=0]] [[@dialect=luau]]
local duplicate = {}
duplicate[2] = "first"
duplicate[2] = "second"
duplicate[1] = "one"
assert(duplicate[1] == "one" and duplicate[2] == "second")

local numeric = {}
numeric[2] = "integer"
numeric[2.0] = "float"
numeric[1] = "one"
assert(numeric[1] == "one" and numeric[2] == "float")

local function build(key)
    local result = {}
    result[2] = "first"
    result[key] = "second"
    result[1] = "one"
    return result
end

local aliased = build(2)
local distinct = build(3)
assert(aliased[2] == "second")
assert(distinct[1] == "one" and distinct[2] == "first" and distinct[3] == "second")

local mixed = {
    [0] = "zero",
    "one",
    [3] = "three",
    [2] = "two",
    key = "value",
    [false] = "false-key",
    [2] = "two-final",
}
assert(mixed[0] == "zero" and mixed[1] == "one")
assert(mixed[2] == "two-final" and mixed[3] == "three")
assert(mixed.key == "value" and mixed[false] == "false-key")

-- record 会提前提交短数组批次，但整份字面量的数组缓冲仍保留；键、值与嵌套分配依次求值。
local trace = ""
local function mark(label, value)
    trace = trace .. label
    return value, label .. "-extra"
end
local interleaved = {
    [mark("k", 0)] = mark("v", "zero"),
    mark("a", 11),
    tag = mark("b", 22),
    mark("c", 33),
    [mark("d", 7)] = { mark("e", 44) },
    mark("f", 55),
}
assert(trace == "kvabcdef")
assert(interleaved[0] == "zero" and interleaved.tag == 22)
assert(interleaved[1] == 11 and interleaved[2] == 33 and interleaved[3] == 55)
assert(interleaved[4] == "f-extra" and interleaved[5] == nil)
assert(interleaved[7][1] == 44 and interleaved[7][2] == "e-extra")
print("interleaved-order", trace)

print("regress_236_table_constructor_pending_alias", "ok")
