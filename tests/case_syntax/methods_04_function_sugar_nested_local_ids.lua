-- 子函数的局部身份与外层结果根分别验证，不按 LocalId 数字复用推导跨函数使用。
-- child LocalId 独立；中间结果同时是 finish 执行期间的 caller 根。
-- unluac: expect-contains [[local r1_0 = p1_0:begin()]]
-- unluac: expect-contains [[r1_0:finish(function()]]
-- unluac: expect-ast-count [[method-call]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]]

local function build(obj)
    local value = obj:begin()
    value:finish(function()
        local value = side()
        use(value)
        return value
    end)
end

-- begin 的 receiver 与 finish 的 receiver 不同，回调在 build 返回之后才执行。
local obj, chain, token = {}, {}, {}
local callbacks, log = {}, {}
function obj:begin()
    assert(self == obj)
    log[#log + 1] = "begin"
    return chain
end
function chain:finish(callback)
    assert(self == chain)
    log[#log + 1] = "finish"
    callbacks[#callbacks + 1] = callback
end
function side()
    log[#log + 1] = "side"
    return token
end
function use(value)
    assert(value == token)
    log[#log + 1] = "use"
end
assert(select("#", build(obj)) == 0)
assert(#callbacks == 1 and table.concat(log, ",") == "begin,finish")
assert(callbacks[1]() == token)
assert(table.concat(log, ",") == "begin,finish,side,use")
print("regress_402_nested_ids#1", table.concat(log, ","))

-- finish 清空参数后，build 的中间 local 仍须保活 begin 返回的新对象。
local chain_weak = setmetatable({}, {__mode = "v"})
local finish_observations = 0
local function observe_finish(self, callback)
    self = nil
    collectgarbage("collect")
    collectgarbage("collect")
    finish_observations = finish_observations + 1
    assert(chain_weak.value ~= nil, "method chain lost its caller result root")
end
local fresh_owner = {}
function fresh_owner:begin()
    local fresh = {finish = observe_finish}
    chain_weak.value = fresh
    return fresh
end
collectgarbage("stop")
build(fresh_owner)
collectgarbage("restart")
assert(finish_observations == 1)
