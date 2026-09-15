-- CONCAT 的 operand 左到右求值，合并右到左；中间根的存活由原缓冲槽决定。
-- unluac: expect-contains [[("a") .. ":" ..]]
local weak = setmetatable({}, {__mode = "v"})
local meta = {}
local function label(value)
    return type(value) == "table" and value.name or value
end
meta.__concat = function(left, right)
    collectgarbage("collect")
    print("concat", label(left), label(right), weak.a ~= nil, weak.b ~= nil, weak.c ~= nil)
    return "(" .. label(left) .. label(right) .. ")"
end
local function piece(name)
    local value = setmetatable({name = name}, meta)
    weak[name] = value
    print("piece", name)
    return value, "discarded"
end
local function joined(factory)
    return factory("a") .. ":" .. factory("b") .. ":" .. factory("c")
end
local function separated(factory)
    local prefix = factory("a") .. factory("b")
    print("between")
    return prefix .. factory("c")
end
local function stored(factory)
    local value = factory("a") .. ":" .. factory("b") .. ":" .. factory("c")
    print("stored", value)
end
print("joined", joined(piece))
collectgarbage("collect")
print("separated", separated(piece))
collectgarbage("collect")
stored(piece)
