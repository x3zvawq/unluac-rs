-- regress_233_raw_branch_value_before_locals#1: branch value 应在 locals 前消解机械 guard temp
-- unluac: expect-not-contains [[if ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local function run(a, b)
    local trace = {}
    local function mark(tag, value)
        trace[#trace + 1] = tag
        return value
    end

    return a
            and (mark("b", b) or (mark("c", true) and mark("d", "done"))),
        table.concat(trace, ",")
end

local first, first_trace = run(false, true)
local second, second_trace = run(true, false)
assert(first == false)
assert(first_trace == "")
assert(second == "done")
assert(second_trace == "b,c,d")
print("regress_233_raw_branch_value_before_locals#1", first, first_trace, second, second_trace)
