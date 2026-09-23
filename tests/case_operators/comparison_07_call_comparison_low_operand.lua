-- CALL 后的比较直接读取原低槽，同时保留算术中间对象的物理根。
-- unluac: expect-not-contains [[= assert]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=9]]
local function run_iife(seed)
    local result = (function(value)
        local doubled = value * 2
        local shifted = doubled + 1
        if shifted > 10 then return shifted end
        return shifted * 2
    end)(seed)
    return result
end
local weak = setmetatable({}, {__mode = "v"})
local shifted = setmetatable({}, {__lt = function()
    collectgarbage("collect")
    collectgarbage("collect")
    print("doubled-alive", weak.doubled ~= nil)
    return true
end})
local seed = setmetatable({}, {__mul = function()
    local doubled = setmetatable({}, {__add = function() return shifted end})
    weak.doubled = doubled
    return doubled
end})
collectgarbage("stop")
assert(run_iife(seed) == shifted)
collectgarbage("restart")

local function compare_parameter(run, expected)
    assert(run() == expected)
end
compare_parameter(function() return seed end, seed)

local function compare_captured()
    local expected = {}
    local function replace()
        expected = {}
        return expected
    end
    -- 右侧读取必须留在 CALL 后，不能先保存旧 cell 值。
    assert(replace() == expected)
    local snapshot = expected
    local result = replace()
    assert(result ~= snapshot)
    return result
end
assert(compare_captured() ~= nil)
