-- CALL 后的比较直接读取原低槽，同时保留算术中间对象的物理根。
-- unluac: expect-not-contains [[= assert]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=9]]
-- unluac: expect-ast-count [[function]] [[9]]
-- unluac: expect-ast-count [[if]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[21]]
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
local multiplies, additions, comparisons = 0, 0, 0
local shifted = setmetatable({}, {__lt = function()
    comparisons = comparisons + 1
    collectgarbage("collect")
    collectgarbage("collect")
    print("doubled-alive", weak.doubled ~= nil)
    return true
end})
local seed = setmetatable({}, {__mul = function()
    multiplies = multiplies + 1
    local doubled = setmetatable({}, {__add = function()
        additions = additions + 1
        return shifted
    end})
    weak.doubled = doubled
    return doubled
end})
collectgarbage("stop")
assert(run_iife(seed) == shifted)
collectgarbage("restart")
assert(multiplies == 1 and additions == 1 and comparisons == 1)
assert(run_iife(4) == 18)
assert(run_iife(4.5) == 20)
assert(run_iife(5) == 11)
assert(run_iife(0) == 2)
assert(run_iife(-1) == -2)
assert(select("#", run_iife(5)) == 1)
assert(multiplies == 1 and additions == 1 and comparisons == 1)

local function compare_parameter(run, expected)
    assert(run() == expected)
    assert(expected == run())
end
local producer_calls = 0
local producer = function()
    producer_calls = producer_calls + 1
    return seed, "extra"
end
compare_parameter(producer, seed)
seed = false
compare_parameter(producer, false)
seed = nil
compare_parameter(producer, nil)
assert(not pcall(compare_parameter, producer, true))
assert(select("#", compare_parameter(producer, nil)) == 0)
assert(producer_calls == 9)

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
local first_result = compare_captured()
local second_result = compare_captured()
assert(not rawequal(first_result, second_result))
assert(select("#", compare_captured()) == 1)
