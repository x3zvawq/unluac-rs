-- regress_297_luau_decision_guard_mutation: decision arm不能改变guard后误执行另一臂
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=0]] [[@variant=O0]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=0]] [[@variant=O1]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=0]] [[@variant=O2]] [[@debug=stripped]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=0]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-not-contains [[false or ]] [[@variant=O2]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=0]] [[@variant=O2]]
-- unluac: expect-not-contains [[= print]] [[@variant=O2]]
-- unluac: expect-contains [[assert(result == "selected", result)]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-contains [[print("regress_297_luau_decision_guard_mutation", result, value_result)]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-contains [[if (if ]] [[@variant=O0]]
-- unluac: expect-contains [[if (if ]] [[@variant=O1]]
-- unluac: expect-contains [[= (if ]] [[@variant=O0]]
-- unluac: expect-contains [[= (if ]] [[@variant=O1]]
-- unluac: expect-contains [[() or ]] [[@variant=O0]]
-- unluac: expect-contains [[() or ]] [[@variant=O1]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=5]] [[@variant=O0]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=5]] [[@variant=O1]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=5]] [[@variant=O2]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=5]] [[@variant=O2]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=8]] [[@variant=O0]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=8]] [[@variant=O1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=8]] [[@variant=O2]]
-- unluac: expect-ast-max [[local-binding]] [[5]] [[@proto=8]] [[@variant=O2]] [[@debug=stripped]]
-- unluac: expect-ast-max [[local-binding]] [[5]] [[@proto=8]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-not-contains [[= assert]] [[@variant=O2]]
-- unluac: expect-contains [[assert(value == false)]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-contains [[assert(value2 == true)]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=11]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=11]] [[@debug=retained]]

local guard = true
local trace = {}

local function selected()
    guard = false
    trace[#trace + 1] = "selected"
    return false
end

local function wrong_fallback()
    trace[#trace + 1] = "wrong"
    return true
end

if if guard then selected() else wrong_fallback() then
    trace[#trace + 1] = "truthy"
end

local result = table.concat(trace, ",")
assert(result == "selected", result)

local value_guard = true
local value_trace = {}

local function mutate_value_guard()
    value_guard = false
    value_trace[#value_trace + 1] = "value"
    return false
end

local function wrong_value_fallback()
    value_trace[#value_trace + 1] = "wrong-value"
    return true
end

local value = if value_guard then mutate_value_guard() or value_guard else wrong_value_fallback()
local value_result = table.concat(value_trace, ",")
assert(value == false, value)
assert(value_result == "value", value_result)
print("regress_297_luau_decision_guard_mutation", result, value_result)

-- 两臂都改变选择条件；false/nil 结果不能触发另一臂，额外返回值不能成为外层条件。
local function check_arm(flag, returned, expected_arm)
    local events = {}
    local function left()
        flag = false
        events[#events + 1] = "left"
        return returned, true
    end
    local function right()
        flag = true
        events[#events + 1] = "right"
        return returned, true
    end
    if if flag then left() else right() then
        events[#events + 1] = "truthy"
    end
    assert(events[1] == expected_arm, table.concat(events, ","))
    assert(#events == (returned and 2 or 1), #events)
    assert(events[2] == (returned and "truthy" or nil), events[2])
end

check_arm(true, false, "left")
check_arm(true, nil, "left")
check_arm(true, "value", "left")
check_arm(false, false, "right")
check_arm(false, nil, "right")
check_arm(false, "value", "right")

-- 备用值是被闭包修改的参数；or 右臂必须读到调用后的值。
local function check_value(flag, spare, returned)
    local updates = 0
    local function produce()
        updates = updates + 1
        spare = "after"
        return returned
    end
    local function other()
        updates = updates + 10
        return "else"
    end
    local chosen = if flag then produce() or spare else other()
    assert(chosen == (flag and (returned or "after") or "else"), chosen)
    assert(updates == (flag and 1 or 10), updates)
    return chosen
end

assert(check_value(true, "before", false) == "after")
assert(check_value(true, "before", nil) == "after")
assert(check_value(true, "before", 7) == 7)
assert(check_value(false, "before", false) == "else")

-- 提前生效的 debug 声明不属于条件表达式的 initializer。
local function declared_before(flag, left, right)
    local value
    if flag then
        value = left()
    else
        value = right()
    end
    return value
end

assert(declared_before(true, selected, wrong_fallback) == false)
assert(declared_before(false, selected, wrong_fallback) == true)
