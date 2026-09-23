-- 高槽分支状态作为比较操作数时，入口初始化与后继调用保持各自的声明边界。
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-contains [[print("inline-state",]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local base = getfenv()
-- unluac-runtime: local events, assertions, calls = {}, 0, 0
-- unluac-runtime: local function observed_print(tag, ...)
-- unluac-runtime:     collectgarbage("collect")
-- unluac-runtime:     calls = calls + 1
-- unluac-runtime:     events[#events + 1] = "print:" .. tag
-- unluac-runtime:     print(tag, ...)
-- unluac-runtime: end
-- unluac-runtime: local environment = {assert = function(value)
-- unluac-runtime:     assert(value)
-- unluac-runtime:     assertions = assertions + 1
-- unluac-runtime:     events[#events + 1] = "assert"
-- unluac-runtime:     return value
-- unluac-runtime: end}
-- unluac-runtime: setmetatable(environment, {__index = function(_, key)
-- unluac-runtime:     if key == "print" then
-- unluac-runtime:         collectgarbage("collect")
-- unluac-runtime:         events[#events + 1] = "lookup:print"
-- unluac-runtime:         return observed_print
-- unluac-runtime:     end
-- unluac-runtime:     return base[key]
-- unluac-runtime: end})
-- unluac-runtime: setfenv(run, environment)
-- unluac-runtime: run()
-- unluac-runtime: assert(assertions == 13 and calls == 9)
-- unluac-runtime: print("inlined-observation", table.concat(events, ","))
local function value(a, c)
    local total = 0
    for i = 1, 3 do
        if a then
            break
        end
        if c then
            continue
        end
        total = total + i
    end
    return total
end

local function check(a, c)
    assert(value(a, c) == ((not a and not c) and 6 or 0))
    print("inline-state", a, c)
end

local checks = {check}
checks[1](false, false)
checks[1](false, true)
checks[1](true, false)
checks[1](true, true)

-- 同样的分支状态若从外部对象开始，加法可经元方法产生新资源，不能借数值外形退休它。
local function object_value(seed, a, c)
    local total = seed
    for i = 1, 3 do
        if a then
            break
        end
        if c then
            continue
        end
        total = total + i
    end
    return total
end

local function object_check(seed, a, c)
    assert(object_value(seed, a, c).total == ((not a and not c) and 6 or 0))
    print("object-state", a, c)
end

local additions = 0
local weak = setmetatable({}, {__mode = "v"})
local metadata = {}
metadata.__add = function(left, right)
    additions = additions + 1
    local result = setmetatable({total = left.total + right}, metadata)
    weak[additions] = result
    collectgarbage("collect")
    assert(left.total + right == result.total)
    return result
end
local object_checks = {object_check}
object_checks[1](setmetatable({total = 0}, metadata), false, false)
object_checks[1](setmetatable({total = 0}, metadata), false, true)
object_checks[1](setmetatable({total = 0}, metadata), true, false)
object_checks[1](setmetatable({total = 0}, metadata), true, true)
assert(additions == 3)
collectgarbage("collect")
assert(weak[1] == nil and weak[2] == nil and weak[3] == nil)
print("object-additions", additions)
