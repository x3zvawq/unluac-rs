-- regress_290_luau_numeric_for_early_continue_tail: early continue不能吞掉外层共享tail
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[if]] [[3]]
-- unluac: expect-ast-count [[continue]] [[1]]
-- unluac: expect-ast-count [[break]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[8]]
-- unluac: expect-ast-count [[assign]] [[5]]

local function run(a, b, c, n)
    local count = 0
    for j = 1, n do
        if not a then
            print(j)
        elseif b then
            continue
        end
        count = count + j
        if c then
            break
        end
    end
    return count
end

local first = run(false, false, false, 2)
local second = run(true, true, false, 2)
local third = run(true, false, true, 2)
assert(first == 3, first)
assert(second == 0, second)
assert(third == 1, third)
local saved_print = print
local trace = {}
print = function(value)
    trace[#trace + 1] = value
end
assert(run(false, true, false, 3) == 6)
assert(table.concat(trace, ",") == "1,2,3")
trace = {}
assert(run(nil, true, true, 3) == 1)
assert(table.concat(trace, ",") == "1")
trace = {}
assert(run(true, true, true, 3) == 0)
assert(run(0, "", true, 3) == 0)
assert(run("", false, false, 3) == 6)
assert(run(true, nil, 0, 3) == 1)
assert(run(false, false, false, 0) == 0)
assert(run(false, false, false, -1) == 0)
assert(#trace == 0)
print = saved_print
print("regress_290_luau_numeric_for_early_continue_tail", first, second, third)
