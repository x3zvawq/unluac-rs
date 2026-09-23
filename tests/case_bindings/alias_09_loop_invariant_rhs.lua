-- 稳定 truthiness 不授权删除原高槽参数副本；caller 在返回后仍能观察该根。
-- 保留原入口前缀及参数副本，允许 Boolean 表达式在不移动这些槽的前提下整理。
-- unluac: expect-contains [[local r1_0 = 0]]
-- unluac: expect-contains [[local r1_1 = p1_0]]
-- unluac: expect-contains [[local r2_0 = 0]]
-- unluac: expect-contains [[local r2_1 = p2_0]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=2]]
-- unluac: expect-ast-max [[local-decl]] [[4]] [[@proto=1]]
-- unluac: expect-ast-max [[local-decl]] [[4]] [[@proto=2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=5]]
-- unluac: expect-contains [[+ 1] = type(]]

local function stable_while(flag)
    local count = 0
    local first = flag
    local second = not first
    local condition = not second
    if false then
        print(first, second, condition)
    end
    while condition == true do
        count = count + 1
        if count == 2 then
            break
        end
    end
    return count
end

assert(stable_while(true) == 2)
assert(stable_while(false) == 0)

local function stable_repeat(flag)
    local count = 0
    local first = flag
    local second = not first
    local condition = not second
    if false then
        print(first, second, condition)
    end
    repeat
        count = count + 1
    until condition == true
    return count
end

assert(stable_repeat(true) == 1)

-- 对照删除参数副本的候选：函数内返回值相同，返回后的高槽根不同。
local function folded_while(flag)
    local condition = not not flag
    local count = 0
    while condition == true do
        count = count + 1
        if count == 2 then break end
    end
    return count
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
local function observe(callback)
    callback(make_value())
    local a, b = 1, 1
    methods.observe()
    -- 保持 caller 的实际 frame 足够大，观察低槽覆盖后仍存留的旧高槽。
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
    return reserve[1]
end
collectgarbage("stop")
observe(stable_while)
observe(stable_repeat)
observe(folded_while)
collectgarbage("restart")
assert(table.concat(observations, ",") == "table,table,nil")
