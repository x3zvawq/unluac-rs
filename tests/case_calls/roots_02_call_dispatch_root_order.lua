-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=2]] [[@debug=retained]]
-- unluac: expect-contains [[    a, b = nil, nil]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=2]] [[@debug=retained]]
-- unluac: expect-contains [[target.first, target.second = left, right]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=7]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=6]]
-- unluac: expect-contains [[weak[1], weak[2] = a, b]] [[@debug=retained]]
-- regress_509_call_dispatch_root_order: LuaJIT caller roots survive callee lookup until dispatch.
-- Compare official-runtime stdout; the argument case keeps a separate caller home for the same value.
-- 两个上值目标必须在第一次字段写入前完成读取；逆序写入触发的
-- __newindex 即使更换 target，另一项仍写入原对象。
do
    local writes = {}
    local target
    local original = {}
    target = setmetatable(original, { __newindex = function(self, key, value)
        writes[#writes + 1] = key
        rawset(self, key, value)
        target = {}
    end })
    local function assign(left, right)
        target.first, target.second = left, right
    end
    local left, right = {}, {}
    assign(left, right)
    assert(original.first == left and original.second == right)
    assert(writes[1] == "second" and writes[2] == "first" and #writes == 2)
    assert(target ~= original and next(target) == nil)
end

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
