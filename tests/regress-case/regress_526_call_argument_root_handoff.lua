-- 参数前缀里的 GC 必须保留尚未交接的值，callee 清除参数后 caller 不能继续持有副本。
local weak = setmetatable({}, { __mode = "k" })
local function make()
    local value = {}
    weak[value] = true
    return value
end
local function extra()
    collectgarbage("collect")
    assert(next(weak) ~= nil, "argument died while evaluating another argument")
    return false
end
local function use(value, ignored)
    assert(value ~= nil)
    local before = next(weak) ~= nil
    print("after-prefix-gc", before)
    assert(before, "argument died before handoff")
    value = nil
    collectgarbage("collect")
    local alive = next(weak) ~= nil
    print("inside-after-clear", alive)
    assert(not alive, "caller retained handed-off argument")
end
use(make(), extra())
use(make(), collectgarbage("collect"))
collectgarbage("collect")
local alive = next(weak) ~= nil
print("outside-after-call", alive)
assert(not alive, "argument retained after call")