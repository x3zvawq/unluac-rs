-- 正常结果事实不能替代求值事件证明；falsy 结果也不能被统一改成 false。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local events = 0
local function mark(value)
    events = events + 1
    return value
end

local function falsy(value)
    return (value and false) and true
end
assert(falsy(nil) == nil)
assert(falsy(false) == false)
assert(falsy({}) == false)

local function selected_number(flag)
    if (mark(flag) and 2 or 3) + 4 then
        return 7
    end
    return 9
end
assert(selected_number(false) == 7)
assert(selected_number(true) == 7)
assert(events == 2)

local function selected_value(flag, a, b)
    local value
    if flag then value = a else value = b end
    return value and true
end
assert(selected_value(true, nil, {}) == nil)
assert(selected_value(false, {}, false) == false)
assert(selected_value(true, {}, nil) == true)

local object = {}
local operand = setmetatable({}, {
    __add = function() events = events + 1; return object end,
    __unm = function() events = events + 1; return object end,
    __lt = function() events = events + 1; return true end,
})
local function arithmetic(value)
    local result = value + 1
    return { result, -value, value < value }
end
local result = arithmetic(operand)
assert(result[1] == object and result[2] == object and result[3] == true)
assert(events == 5)
object = nil
result = arithmetic(operand)
assert(result[1] == nil and result[2] == nil and result[3] == true)
assert(events == 8)
-- nil-hole 的边界由各 VM 的原始运行作 oracle，不跨方言硬编码一个长度。
print("nil-hole-length", #result)

local function failing()
    if (mark(true) and error("expected") or 2) + 4 then
        events = events + 100
    end
end
local ok = pcall(failing)
assert(not ok and events == 9)

-- 批次中的临时对象必须跨过后续元方法，返回后只由结果表继续持有。
local weak = setmetatable({}, { __mode = "v" })
local source = setmetatable({}, {
    __add = function() return nil end,
    __unm = function()
        local value = {}
        weak[1] = value
        return value
    end,
    __lt = function()
        collectgarbage("collect")
        collectgarbage("collect")
        assert(weak[1] ~= nil)
        return true
    end,
})
result = arithmetic(source)
assert(result[1] == nil and result[2] == weak[1] and result[3] == true)
result[2] = nil
collectgarbage("collect")
collectgarbage("collect")
assert(weak[1] == nil)
print("regress_468_shared_expression_value_facts", "OK")
