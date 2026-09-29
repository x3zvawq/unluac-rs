-- 纯 test 规范化不授权删除原调用结果的低槽根，Boolean 结果也不等于输入对象身份。
-- unluac: expect-ast-max [[local-binding]] [[17]]
-- unluac: expect-ast-count [[function]] [[9]]
-- unluac: expect-ast-count [[if]] [[0]]
local weak = setmetatable({}, {__mode="v"})
local function make_resource()
    local value = {}
    weak.value = value
    return value
end
local function observe_gc()
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak.value ~= nil, "original lower home must remain rooted")
    return "fallback"
end
local function selected(a,b,c)
    local d = make_resource()
    return a and (b or c) and not d or observe_gc()
end
local function not_and(flag)
    local saved = make_resource()
    return not (flag and saved) or observe_gc()
end
local function not_or(flag)
    local saved = make_resource()
    return not (flag or saved) or observe_gc()
end
assert(selected(true,true,false) == "fallback")
assert(selected(true,false,true) == "fallback")
assert(selected(false,true,true) == "fallback")
assert(selected(true,false,false) == "fallback")
assert(not_and(true) == "fallback")
assert(not_and(false) == true)
assert(not_or(true) == "fallback")
assert(not_or(false) == "fallback")
assert(not_and(nil) == true)
assert(not_or(nil) == "fallback")

local function effectful(a,b,c,probe,fallback)
    return a and (b or c) and not probe() or fallback()
end
local log = {}
local function probe()
    log[#log+1] = "probe"
    return make_resource()
end
local function fallback()
    log[#log+1] = "fallback"
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak.value == nil, "discarded test result is not an independent lower home")
    return "done", "ignored"
end
local result, extra = effectful(true,false,true,probe,fallback)
assert(result == "done" and extra == nil)
assert(table.concat(log, ",") == "probe,fallback")
log = {}
assert(effectful(false,true,true,probe,fallback) == "done")
assert(table.concat(log, ",") == "fallback")
log = {}
assert(effectful(true,false,false,probe,fallback) == "done")
assert(table.concat(log, ",") == "fallback")
log = {}
assert(effectful(true,true,false,probe,fallback) == "done")
assert(table.concat(log, ",") == "probe,fallback")
local function probe_false()
    log[#log+1] = "probe-false"
    return false
end
log = {}
assert(effectful(true,true,false,probe_false,fallback) == true)
assert(table.concat(log, ",") == "probe-false")
print("regress_564_pure_decision_gc", "OK")
