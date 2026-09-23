-- 同语句的值身份相同不代表返回准备区可缩短；尾调用仍消费原完整调用帧。
-- unluac: expect-contains [[return r1_0, r1_1, r1_1]]
-- unluac: expect-contains [[return p2_0(r2_0, r2_1, r2_1)]]
-- unluac: expect-contains [[local r2_1 = r2_0]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=2]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=1]]
-- unluac: expect-contains [[return r6_0, r6_0, r6_0]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=6]]
-- unluac: expect-not-contains [[local r9_0 = p9_0]]
-- unluac: expect-contains [[.value = p9_0()]]
-- unluac: expect-ast-count [[local-decl]] [[6]] [[@proto=9]]

local function return_alias()
    local source = {}
    local alias = source
    return source, alias, alias
end

local function call_alias(sink)
    local source = {}
    local alias = source
    return sink(source, alias, alias)
end

local function split_uses(sink)
    local source = {}
    local alias = source
    sink(alias)
    return alias
end

local first, second, third = return_alias()
assert(first == second and second == third)
assert(call_alias(function(a, b, c)
    return a == b and b == c
end))

local observed
local split = split_uses(function(item)
    observed = item
end)
assert(observed == split)

-- caller 丢弃返回值后，原高槽与删除 alias 后的低槽仍有不同的覆盖窗口。
local function direct()
    local source = {}
    return source, source, source
end
local weak = setmetatable({}, {__mode = "v"})
local observations = {}
local methods = setmetatable({}, {__index = function()
    collectgarbage("collect")
    collectgarbage("collect")
    observations[#observations + 1] = type(weak.value)
    return function() end
end})
local function observe(callback)
    weak.value = callback()
    local a, b, c, d, e = 1, 1, 1, 1, 1
    methods.observe()
    -- 保持 caller 的高槽处于真实 frame 内，观察低槽覆盖后的残值。
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
    return reserve[1]
end
collectgarbage("stop")
observe(return_alias)
observe(direct)
collectgarbage("restart")
assert(table.concat(observations, ",") == "table,nil")

-- 尾调用搬移参数后，原准备区的高槽仍可由 caller 在返回后观察。
local function direct_call(sink)
    local source = {}
    return sink(source, source, source)
end
local function remember_tail(a, b, c)
    assert(a == b and b == c)
    weak.value = a
    return true
end
local function observe_tail(callback)
    local ok = callback(remember_tail)
    local a, b, c, d, e = 1, 1, 1, 1, 1
    methods.observe()
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}
    return ok, reserve[1]
end
local function observe_tail_later(callback)
    local ok = callback(remember_tail)
    local a, b, c, d, e, f = 1, 1, 1, 1, 1, 1
    methods.observe()
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}
    return ok, reserve[1]
end
collectgarbage("stop")
if _VERSION == "Lua 5.1" then
    observe_tail(call_alias)
    observe_tail(direct_call)
else
    observe_tail_later(call_alias)
    observe_tail_later(direct_call)
end
collectgarbage("restart")
assert(observations[3] == "table" and observations[4] == "nil")
