-- unluac: expect-ast-count [[local-binding]] [[3]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
local weak = setmetatable({}, { __mode = "v" })
local object = {}
weak[1] = object
object = nil
local value = weak[1]
collectgarbage("collect")
assert(value ~= nil and value == weak[1])
value = nil
collectgarbage("collect")
assert(weak[1] == nil, "released")
