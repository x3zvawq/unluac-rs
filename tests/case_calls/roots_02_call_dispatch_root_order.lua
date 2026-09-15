-- regress_509_call_dispatch_root_order: LuaJIT caller roots survive callee lookup until dispatch.
-- Compare official-runtime stdout; the argument case keeps a separate caller home for the same value.
local weak = setmetatable({}, {__mode="v"})
local collect = collectgarbage
local report = print
local function pair()
    local a, b = {}, {}
    weak[1], weak[2] = a, b
    return a, b
end
local function observe(tag)
    collect("collect")
    report(tag, weak[1] ~= nil, weak[2] ~= nil)
end
local function dispatch(value)
    observe("dispatch")
    value = nil
    observe("cleared")
end
local env = setmetatable({}, {__index=function(_, key)
    observe("lookup")
    return dispatch
end})
local function run_callee()
    local f = pair
    local a, b
    a, b = f()
    a, b = nil, nil
    observed_global("collect")
end
local function run_argument()
    local f = pair
    local a, b
    a, b = f()
    a = nil
    observed_global(b)
    b = nil
end
setfenv(run_callee, env)
setfenv(run_argument, env)
report("callee")
run_callee()
observe("after")
report("argument")
run_argument()
observe("after")
