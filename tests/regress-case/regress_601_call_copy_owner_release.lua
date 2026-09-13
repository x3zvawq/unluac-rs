-- CALL 后的 COPY 即使不是 GC 观察代表，也须登记已物化 owner 的精确释放点。
local weak = setmetatable({}, { __mode = "v" })
local function make()
    local object = {}
    weak[1] = object
    return object
end
local factory = make
factory = factory()
factory = nil
collectgarbage("collect")
assert(weak[1] == nil)
print("move-root-released")
