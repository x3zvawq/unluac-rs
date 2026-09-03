-- 常量的运行时 binding 不能消失成 TDUP 模板，改变重编译后的数组容量。
-- unluac: expect-not-contains [[unluac error]]
local function boolean_value(a, c)
    local value = true
    return {a, value, c}
end
local function nil_value(a, c)
    local value = nil
    return {a, value, c}
end
local function string_value(a, c)
    local value = "kept"
    return {a, value, c}
end
local function arithmetic_value(a, c)
    local left = 2
    local right = 3
    return {a, left + right, c}
end
local function show(label, t)
    print(label, #t, t[1], t[2], t[3])
end
local function comparison_value(a, c)
    local left = 1
    local right = 2
    return {a, left < right, c}
end
local function direct_comparison(a, c)
    return {a, 1 < 2, c}
end
local function nested_comparison(a, c)
    return {inner = {a, 1 < 2, c}}
end
local function runtime_key(a, c)
    local key = "marker"
    return {a, a, c, [key] = true}
end
for mask = 0, 3 do
    local a, c
    if mask % 2 == 1 then a = false end
    if mask >= 2 then c = 3 end
    show("boolean", boolean_value(a, c))
    show("nil", nil_value(a, c))
    show("string", string_value(a, c))
    show("arithmetic", arithmetic_value(a, c))
    show("comparison", comparison_value(a, c))
    show("direct-comparison", direct_comparison(a, c))
    show("nested-comparison", nested_comparison(a, c).inner)
    local keyed = runtime_key(a, c)
    show("runtime-key", keyed)
    print("runtime-key-marker", keyed.marker)
end
