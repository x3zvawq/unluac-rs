-- numeric-for start 只求值一次，但普通字段调用不能改成 SELF 预写。
-- unluac: expect-contains [[.first(r2_0), 3 do]]
-- unluac: expect-ast-count [[method-call]] [[0]] [[@proto=2]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=2]]

local owner = {}

function owner:first()
    return 1, 99
end

local observed = {}

local function collect(source)
    local receiver = source
    for value = receiver.first(receiver), 3 do
        observed[#observed + 1] = value
    end
end

collect(owner)
local result = table.concat(observed, ",")
assert(result == "1,2,3", result)
print("regress_407_method_alias_numeric_for_start", result)

local weak = setmetatable({}, {__mode = "v"})
local trace = {}
local dynamic_owner = setmetatable({}, {__index = function()
    collectgarbage("collect")
    collectgarbage("collect")
    trace[#trace + 1] = type(weak.value)
    return function() return 1, 99 end
end})
local function method(source)
    local receiver = source
    for value = receiver:first(), 3 do
        observed[#observed + 1] = value
    end
end
local function seed(a, b, c, resource)
    weak.value = resource
    return true
end
local function observe(callback)
    do local result = seed(false, false, false, {}) end
    callback(dynamic_owner)
end
collectgarbage("stop")
observe(collect)
observe(method)
collectgarbage("restart")
assert(table.concat(trace, ",") == "table,nil")
