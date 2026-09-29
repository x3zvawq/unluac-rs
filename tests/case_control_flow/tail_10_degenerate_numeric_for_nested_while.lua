-- regress_90_degenerate_numeric_for_nested_while#1: unreachable numeric latch may share nested while header
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[while not true do]]
-- unluac: expect-contains [[while not p1_1 do]]
-- unluac: expect-not-contains [[while false do]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[break]] [[2]]
-- unluac: expect-ast-count [[local-binding]] [[6]]
local function run(a, b, xs)
    local x = 0
    if a and b then
        print(x)
        for _ = 1, 3 do
            while not b do
                if a then
                    continue
                end
                print(x)
                if xs[x] then
                    break
                end
            end
            break
        end
    end
    return x
end

local skipped = run(false, true, {})
local numeric_break = run(true, true, {})
assert(skipped == 0 and numeric_break == 0)
print("regress_90_degenerate_numeric_for_nested_while#1", skipped, numeric_break)

local saved_print, calls = print, 0
print = function(value)
    assert(value == 0)
    calls = calls + 1
end
assert(run(false, false, nil) == 0 and calls == 0)
assert(run(true, false, nil) == 0 and calls == 0)
assert(run(nil, true, nil) == 0 and calls == 0)
assert(run(true, true, nil) == 0 and calls == 1)
assert(run(0, "", nil) == 0 and calls == 2)
print = saved_print
