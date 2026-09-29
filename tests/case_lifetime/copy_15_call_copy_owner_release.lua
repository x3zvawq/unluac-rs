-- CALL 后的 COPY 即使不是 GC 观察代表，也须登记已物化 owner 的精确释放点。
-- unluac: expect-ast-count [[local-binding]] [[4]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[function]] [[1]]
local weak = setmetatable({}, { __mode = "v" })
local function make()
    local object = {}
    weak[1] = object
    return object
end
local factory = make
factory = factory()
assert(type(factory) == "table" and factory == weak[1])
factory = nil
collectgarbage("collect")
assert(weak[1] == nil)
print("move-root-released")
