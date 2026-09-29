-- regress_233_raw_branch_value_before_locals#1: branch value 应在 locals 前消解机械 guard temp
-- unluac: expect-not-contains [[if ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-max [[local-binding]] [[8]]
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
first, first_trace = run(nil, true)
assert(first == nil and first_trace == "")
second, second_trace = run(true, true)
assert(second == true and second_trace == "b")
local shared = {}
second, second_trace = run(true, shared)
assert(second == shared and second_trace == "b")
second, second_trace = run(true, 0)
assert(second == 0 and second_trace == "b")
second, second_trace = run(true, "")
assert(second == "" and second_trace == "b")
second, second_trace = run(true, nil)
assert(second == "done" and second_trace == "b,c,d")
assert(select("#", run(nil, nil)) == 2)
