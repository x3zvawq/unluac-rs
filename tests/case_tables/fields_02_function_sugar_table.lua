-- 表分配内的 receiver 快照不授权普通 GETFIELD/COPY 变成 SELF 预写。
-- unluac: expect-contains [[{ r2_0.table_relaxed(r2_0, 41) }]]
-- unluac: expect-ast-count [[method-call]] [[0]] [[@proto=2]]
-- unluac: expect-ast-max [[local-decl]] [[2]] [[@proto=2]]

local method_owner = {}
function method_owner:table_relaxed(value)
    return value
end

local function table_sink(...)
    local receiver_alias = ...
    local values = { receiver_alias.table_relaxed(receiver_alias, 41) }
    return values[1]
end

assert(table_sink(method_owner) == 41)
print("function-sugar-table", table_sink(method_owner))

local weak = setmetatable({}, {__mode = "v"})
local trace = {}
local dynamic_owner = setmetatable({}, {__index = function()
    collectgarbage("collect")
    collectgarbage("collect")
    trace[#trace + 1] = type(weak.value)
    return function(self, value) return value end
end})
local function method(...)
    local receiver_alias = ...
    local values = { receiver_alias:table_relaxed(41) }
    return values[1]
end
local function seed(a, b, c, d, e, resource)
    weak.value = resource
    return true
end
local function observe(callback)
    do local result = seed(false, false, false, false, false, {}) end
    callback(dynamic_owner)
end
collectgarbage("stop")
observe(table_sink)
observe(method)
collectgarbage("restart")
assert(table.concat(trace, ",") == "table,nil")
