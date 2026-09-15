-- TNEW/TDUP 的数组布局不得在 LowInstr -> HIR -> constructor commit 中丢失。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-min [[table-constructor]] [[6]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[table-record-field]] [[3]] [[@proto=3]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[table-list-field]] [[0]] [[@proto=3]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=3]] [[@dialect=luajit]]
local events = 0
local event_trace = ""
local function take(value)
    events = events + 1
    event_trace = event_trace .. tostring(value) .. ","
    return value
end
local function one(a) return {take(a)} end
local function two(a, b) return {take(a), take(b)} end
local function three(a, b, c) return {take(a), take(b), take(c)} end
local function mixed(a, b, c)
    return {[0] = take("zero"), take(a), name = take("name"), take(b), take(c)}
end
local function keyed(a, b, c)
    return {[1] = take(a), [2] = take(b), [3] = take(c)}
end
local function template(a) return {nil, take(a), true} end
local function check(label, value)
    -- 混合 hash key 的原始 source/chunk 本身会因 hash 布局得到不同 nil-hole 边界；
    -- 此项检查键值与事件顺序，纯数组项才把长度作为稳定的运行 oracle。
    local length = "hash-layout"
    if label ~= "mixed" then length = #value end
    print(label, length, value[0], value[1], value[2], value[3], value.name)
end
for i = 0, 7 do
    local a, b, c
    if i % 2 == 1 then a = false end
    if math.floor(i / 2) % 2 == 1 then b = 2 end
    if i >= 4 then c = true end
    check("one", one(a))
    check("two", two(a, b))
    check("three", three(a, b, c))
    check("mixed", mixed(a, b, c))
    check("keyed", keyed(a, b, c))
    check("template", template(b))
end
assert(events == 120)
print(event_trace)
print("regress_469_luajit_indexed_array_capacity", "OK")
