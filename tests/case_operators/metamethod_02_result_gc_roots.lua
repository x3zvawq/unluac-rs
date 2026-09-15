-- 运算元方法可以返回对象；最后一次活读不是独立 VM home 的 GC 终点。
local function binary(value, observe)
    local doubled = value * 2
    local shifted = doubled + 1
    observe(true)
    return shifted
end

local function unary(value, observe)
    local negated = -value
    local shifted = negated + 1
    observe(true)
    return shifted
end

local function concat(value, observe)
    local joined = value .. "suffix"
    local shifted = joined + 1
    observe(true)
    return shifted
end

local function overwrite(value, observe)
    local doubled = value * 2
    local shifted = doubled + 1
    observe(true)
    doubled = nil
    observe(false)
    return shifted
end

-- 03 的实际分支形状：比较元方法观察已被加法消费的乘法结果。
local function branch(value)
    local doubled = value * 2
    local shifted = doubled + 1
    if shifted > 10 then
        return shifted
    end
    return shifted * 2
end

local function return_chain(value)
    local doubled = value * 2
    local shifted = doubled + 1
    return shifted * 2
end

local function check(run, mixed_comparison)
    local weak = setmetatable({}, {__mode = "v"})
    local observations = 0
    local function observe(expected)
        collectgarbage("collect")
        collectgarbage("collect")
        assert((weak.intermediate ~= nil) == expected, "operator result root lifetime")
        observations = observations + 1
    end
    local shifted = setmetatable({}, {
        __lt = function()
            observe(true)
            return true
        end,
        __mul = function()
            observe(true)
            return "done"
        end,
    })
    local function make_intermediate()
        local value = setmetatable({}, {__add = function() return shifted end})
        weak.intermediate = value
        return value
    end
    local seed = setmetatable({}, {
        __mul = make_intermediate,
        __unm = make_intermediate,
        __concat = make_intermediate,
    })
    collectgarbage("stop")
    local ok, result = pcall(run, seed, observe)
    if mixed_comparison and not ok then
        -- Lua 5.1 等 VM 不接受 table 与 number 的有序比较，不能误判为反编译错误。
        assert(observations == 0)
        assert(string.find(tostring(result), "compare", 1, true) ~= nil)
    else
        assert(ok, result)
        assert(result == shifted or result == "done")
        assert(observations > 0)
    end
    collectgarbage("restart")
    print("operator-root", ok, observations)
end

check(binary)
check(unary)
check(concat)
check(overwrite)
check(branch, true)
check(return_chain)
