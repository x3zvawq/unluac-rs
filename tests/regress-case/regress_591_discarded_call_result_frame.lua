-- 单结果 CALL 后紧邻常量写覆盖原结果槽；其结果与旧 callee 都不能延长到下次观察。
local weak = setmetatable({}, {__mode = "v"})
local trace = ""
local function result()
    trace = trace .. "call;"
    local object = {}
    weak.result = object
    return object, "discarded"
end
local function observe(value)
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak.result == nil)
    assert(value == 9)
    trace = trace .. "observe;"
end
local function run(factory, inspect)
    local value = (factory() and false) or 9
    inspect(value)
end
run(result, observe)
assert(trace == "call;observe;")
print("discarded-result", trace)
