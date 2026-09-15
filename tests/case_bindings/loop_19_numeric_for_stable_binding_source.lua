-- numeric-for 正常路径的数值要求不能证明类型错误路径上的参数副本可删除。
-- PUC 异常退出及 LuaJIT lookup 中的额外实参观察分别约束原帧；Luau 消解稳定参数副本。
-- unluac: expect-contains [[for r1_3 = r1_0, 1 do]] [[@dialect=lua5.1]]
-- unluac: expect-contains [[for r1_3 = r1_0, 1 do]] [[@dialect=lua5.2]]
-- unluac: expect-contains [[for r1_3 = r1_0, 1 do]] [[@dialect=lua5.3]]
-- unluac: expect-contains [[for r1_3 = r1_0, 1 do]] [[@dialect=lua5.4]]
-- unluac: expect-contains [[for r1_3 = r1_0, 1 do]] [[@dialect=lua5.5]]
-- unluac: expect-contains [[for r8_3 = r8_0, 1 do]] [[@dialect=luajit]]
-- unluac: expect-contains [[for r1_2 = p1_0, 1 do]] [[@dialect=luau]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-max [[local-decl]] [[3]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-max [[local-decl]] [[3]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-max [[local-decl]] [[3]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-max [[local-decl]] [[3]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-max [[local-decl]] [[3]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-max [[local-decl]] [[3]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=8]] [[@dialect=luajit]]
-- unluac: expect-ast-max [[local-decl]] [[3]] [[@proto=8]] [[@dialect=luajit]]

local function run(value)
    local start = value
    local keep = math.abs(-9)
    local total = 0
    for index = start, 1 do
        total = total + index
    end
    return total, keep
end

local total, keep = run(1)
assert(total == 1 and keep == 9)

-- 删除 start 的对照仍返回同样的数值，但错误退出时不再保留原高槽根。
local function folded(value)
    local keep = math.abs(-9)
    local total = 0
    for index = value, 1 do total = total + index end
    return total, keep
end
local weak = setmetatable({}, {__mode = "v"})
local observations = {}
local function make_value()
    local value = {}
    weak.value = value
    return value
end
local methods = setmetatable({}, {__index = function()
    collectgarbage("collect")
    collectgarbage("collect")
    observations[#observations + 1] = type(weak.value)
    return function() end
end})
-- 两个入口固定不同 VM 的低槽覆盖窗口；把 GC 放进新 callee 会改变观察帧。
local function observe(callback)
    if pcall(callback, make_value()) then error("numeric-for accepted a table") end
    local a1, a2, a3, a4, a5 = 1, 1, 1, 1, 1
    methods.observe()
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
    return reserve[1]
end
local function observe_later(callback)
    if pcall(callback, make_value()) then error("numeric-for accepted a table") end
    local a1, a2, a3, a4, a5, a6, a7 = 1, 1, 1, 1, 1, 1, 1
    methods.observe()
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
    return reserve[1]
end
if not jit and _VERSION ~= "Luau" then
    collectgarbage("stop")
    if _VERSION == "Lua 5.1" then
        observe(run)
        observe(folded)
    else
        observe_later(run)
        observe_later(folded)
    end
    collectgarbage("restart")
    assert(table.concat(observations, ",") == "table,nil")
end

-- LuaJIT 会把原 frame 范围内的额外实参作为根；删除 start 改变 frame 大小及其可见范围。
-- math.abs 的普通字段查找能触发 __index，这里只做 GC 观察，不修改参数或局部变量。
if jit then
    local saved_math = math
    math = setmetatable({}, {__index = function(_, key)
        assert(key == "abs")
        collectgarbage("collect")
        collectgarbage("collect")
        observations[#observations + 1] = type(weak.value)
        return saved_math[key]
    end})
    collectgarbage("stop")
    run(1, nil, nil, nil, nil, nil, nil, make_value())
    folded(1, nil, nil, nil, nil, nil, nil, make_value())
    collectgarbage("restart")
    math = saved_math
    assert(table.concat(observations, ",") == "table,nil", "numeric-for frame lost its incoming root window")
end
