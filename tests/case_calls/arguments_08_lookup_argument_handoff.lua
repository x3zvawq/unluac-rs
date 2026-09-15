-- Only the passed argument home belongs to the callee; an independent source home remains.
do
local weak = setmetatable({}, { __mode = "v" })
local object = {}
weak.key = object
object = nil
local function consume(value)
    value = nil
    collectgarbage("collect")
    assert(weak.key == nil, "callee argument home must release")
end
consume(weak.key)
local overwritten = 123
collectgarbage("collect")
assert(weak.key == nil, "caller argument home already released")
assert(overwritten == 123)

end

do
local weak = setmetatable({}, { __mode = "v" })
local object = {}
weak.key = object
object = nil
local function consume(value)
    value = nil
    collectgarbage("collect")
    assert(weak.key ~= nil, "independent caller home must retain")
end
local source = weak.key
consume(source)
source = nil
local overwritten = 123
collectgarbage("collect")
assert(weak.key == nil, "caller argument home already released")
assert(overwritten == 123)

end
