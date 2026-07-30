-- regress_297_luau_decision_guard_mutation: decision arm不能改变guard后误执行另一臂
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

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
