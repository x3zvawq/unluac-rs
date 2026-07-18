-- regress_274_temp_live_use_boundaries: proto级live-use必须保留跨结构存活与覆盖写入副作用
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local events = {}

local function mark(label, value)
    events[#events + 1] = label
    return value
end

local index = 0
local snapshot
repeat
    snapshot = mark("repeat", index)
    index = index + 1
until snapshot >= 1
assert(snapshot == 1)

local values = { 2, 3, 4 }
local product = 1
local products = {}
for key, value in ipairs(values) do
    product = mark("for", product * value)
    products[key] = product
end
assert(product == 24)
assert(products[1] == 2 and products[2] == 6 and products[3] == 24)

local active = true
local overwritten
while active do
    overwritten = mark("first", 10)
    overwritten = mark("second", 20)
    active = false
end
assert(overwritten == 20)

assert(table.concat(events, ",") == "repeat,repeat,for,for,for,first,second")
print("regress_274_temp_live_use_boundaries")
