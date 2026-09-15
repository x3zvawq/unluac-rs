-- 算术结果也可能是对象；保留原低槽结果和高槽返回准备，不按正常数值路径压缩布局。
-- unluac: expect-contains [[return r1_0, r1_1]]
-- unluac: expect-contains [[return p3_0 == 42]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[local-decl]] [[2]] [[@proto=1]]
-- unluac: expect-contains [[return p5_0 + 1, p5_1 + 2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=5]]
local function run(lhs, rhs)
    local first = lhs + 1
    local second = rhs + 2
    if false then
        print(first, second)
    end
    return first, second
end

local first, second = run(40, 40)
assert(first == 41 and second == 42)

local function identity(value)
    return value
end

local function compare(value)
    local compared = value == 42
    return compared, identity(value)
end

local matches, echoed = compare(42)
assert(matches and echoed == 42)

-- __add 可以返回对象并触发 GC；第一个结果必须在第二次求值期间仍由原结果槽持有。
local events = {}
local weak = setmetatable({}, { __mode = "v" })
local arithmetic = {
    __add = function(value, amount)
        events[#events + 1] = value.id
        if value.id == 2 then
            collectgarbage("collect")
            assert(weak[1] ~= nil and weak[1].n == 41)
        end
        local result = { n = value.n + amount }
        if value.id == 1 then
            weak[1] = result
        end
        return result
    end,
}
local left, right = run(
    setmetatable({ id = 1, n = 40 }, arithmetic),
    setmetatable({ id = 2, n = 40 }, arithmetic)
)
assert(left.n == 41 and right.n == 42 and weak[1] == left)
assert(#events == 2 and events[1] == 1 and events[2] == 2)

-- 复用上面的 __add 对象结果及弱表，同时检查 caller 覆写低槽后的残根。
local function direct(lhs, rhs)
    return lhs + 1, rhs + 2
end
local root_left = setmetatable({id = 1, n = 40}, arithmetic)
local root_right = setmetatable({id = 2, n = 40}, arithmetic)
local observations = {}
local methods = setmetatable({}, {__index = function()
    collectgarbage("collect")
    collectgarbage("collect")
    observations[#observations + 1] = type(weak[1])
    return function() end
end})
local function observe(callback)
    callback(root_left, root_right)
    local a, b, c, d = 1, 1, 1, 1
    methods.observe()
    -- 高槽仍属于 caller 的真实 frame；这里的构造器维持被观察的覆盖窗口。
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
    return reserve[1]
end
collectgarbage("stop")
observe(run)
observe(direct)
collectgarbage("restart")
assert(table.concat(observations, ",") == "table,nil")
