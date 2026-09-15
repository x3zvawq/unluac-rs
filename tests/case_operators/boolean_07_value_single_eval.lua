-- regress_241_branch_value_single_eval: branch-value折叠与物化保留单次求值和求值顺序
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local function run(a, b, c, d)
    local trace = {}
    local function p(tag, value)
        trace[#trace + 1] = tag
        return value
    end

    local value = p("a", a) or (p("b", b) and p("c", c)) or p("d", d)
    return value, table.concat(trace, ",")
end

local function materialize_order()
    local assigned = "old"
    local target_trace = {}

    local function observe_target(tag, value)
        target_trace[#target_trace + 1] = tag .. ":" .. tostring(assigned)
        return value
    end

    assigned = observe_target("a", false)
        or (observe_target("b", true) and observe_target("c", true))
        or observe_target("d", true)

    local observed = "old"
    local function old_target(first)
        return "old-target:" .. first
    end
    local function new_target(first)
        return "new-target:" .. first
    end

    local target = old_target
    local function mutate_siblings(_, value)
        observed = "new"
        target = new_target
        return value
    end

    local result = target(
        observed,
        mutate_siblings("a", false)
            or (mutate_siblings("b", true) and mutate_siblings("c", true))
            or mutate_siblings("d", true)
    )
    return assigned, table.concat(target_trace, ","), result
end

local function method_order()
    local observed = "old"
    local receiver = {}
    receiver.pick = function(_, first)
        return "old-method:" .. first
    end

    local function mutate_method(_, value)
        observed = "new"
        receiver.pick = function(_, first)
            return "new-method:" .. first
        end
        return value
    end

    return receiver:pick(
        observed,
        mutate_method("a", false)
            or (mutate_method("b", true) and mutate_method("c", true))
            or mutate_method("d", true)
    )
end

local value1, trace1 = run(true, true, true, true)
local value2, trace2 = run(false, true, true, true)
local value3, trace3 = run(false, true, false, true)
local value4, trace4 = run(false, false, true, true)
local value5, trace5 = run(false, false, true, false)
local assigned, target_trace, sibling_result = materialize_order()
local method_result = method_order()

assert(value1 == true and trace1 == "a")
assert(value2 == true and trace2 == "a,b,c")
assert(value3 == true and trace3 == "a,b,c,d")
assert(value4 == true and trace4 == "a,b,d")
assert(value5 == false and trace5 == "a,b,d")
assert(assigned == true and target_trace == "a:old,b:old,c:old")
assert(sibling_result == "old-target:old", sibling_result)
assert(method_result == "old-method:old", method_result)
print("regress_241_branch_value_single_eval", trace1, trace2, trace3, trace4, trace5)
