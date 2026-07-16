-- regress_241_branch_value_single_eval: branch-value折叠不能重复执行带副作用的guard producer
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

local value1, trace1 = run(true, true, true, true)
local value2, trace2 = run(false, true, true, true)
local value3, trace3 = run(false, true, false, true)
local value4, trace4 = run(false, false, true, true)
local value5, trace5 = run(false, false, true, false)

assert(value1 == true and trace1 == "a")
assert(value2 == true and trace2 == "a,b,c")
assert(value3 == true and trace3 == "a,b,c,d")
assert(value4 == true and trace4 == "a,b,d")
assert(value5 == false and trace5 == "a,b,d")
print("regress_241_branch_value_single_eval", trace1, trace2, trace3, trace4, trace5)
