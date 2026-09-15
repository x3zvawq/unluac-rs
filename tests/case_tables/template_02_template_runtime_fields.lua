-- 模板初始数组容量不能因后续运行时字段变成常量而扩大。
-- dump/load 让源码执行同样使用序列化模板，避免源码编译器未裁尾的容量掩盖问题。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-min [[table-constructor]] [[7]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
local function boolean_value(a)
    local x = true
    return {true, a, x}
end
local function arithmetic_value(a)
    local x = 2
    return {true, a, x + 3}
end
local function comparison_value(a)
    return {true, a, 1 < 2}
end
local function nested_value(a)
    local x = "kept"
    return {inner = {true, a, x, a, x}}
end
local function hash_template(a)
    local x = true
    return {marker = true, a, a, x}
end
local function record_value(a)
    local x = true
    return {true, a, a, [3] = x}
end
local function compiled(f)
    return assert(loadstring(string.dump(f)))
end
local function show(label, t)
    print(label, #t, t[1], t[2], t[3], t[4], t[5])
end
for i = 0, 1 do
    local a
    if i == 1 then a = false end
    show("boolean", compiled(boolean_value)(a))
    show("arithmetic", compiled(arithmetic_value)(a))
    show("comparison", compiled(comparison_value)(a))
    show("nested", compiled(nested_value)(a).inner)
    show("hash-template", compiled(hash_template)(a))
    show("record", compiled(record_value)(a))
end
