-- 静态展开保留连续 NOT 指令，检查内联后仍能被官方解析器重新编译。
local function coerce(value)
    local result = value
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result; result = not result
    return result
end

local function check(value, expected)
    local result = coerce(value)
    assert(type(result) == "boolean", "boolean result became the original value")
    assert(result == expected, "NOT chain changed truthiness")
    assert(select("#", coerce(value)) == 1, "NOT chain changed return width")
end
check(nil, false)
check(false, false)
check(true, true)
check(0, true)
check("", true)
check({}, true)
check(function() end, true)

local calls = 0
local function callback(value)
    calls = calls + 1
    return value, "extra result"
end
local function double(value)
    return not not callback(value)
end
local function triple(value)
    return not not not callback(value)
end
local function assert_one(expected, ...)
    assert(select("#", ...) == 1, "NOT exposed extra callback results")
    local actual = ...
    assert(type(actual) == "boolean" and actual == expected, "callback coercion changed")
end
assert_one(false, double(nil))
assert_one(true, double(0))
assert_one(true, triple(false))
assert_one(false, triple({}))
assert(calls == 4, "callback evaluation count changed")

local comparisons = 0
local meta = {__lt = function(left, right)
    comparisons = comparisons + 1
    return left.order < right.order
end}
local left = setmetatable({order = 1}, meta)
local right = setmetatable({order = 2}, meta)
assert_one(true, not not (left < right))
assert_one(false, not not (right < left))
assert(comparisons == 2, "comparison metamethod evaluation count changed")
local function falsy_choice(value) return not not (value and false) end
local function truthy_choice(value) return not not (value or true) end
assert_one(false, falsy_choice(nil))
assert_one(false, falsy_choice(0))
assert_one(true, truthy_choice(0))
assert_one(true, truthy_choice(nil))
local function fail() error("not-chain-error", 0) end
local ok, reason = pcall(function() return not not not fail() end)
assert(not ok and reason == "not-chain-error", "NOT changed error propagation")
print("regress_547_not_value_chain", "OK")
