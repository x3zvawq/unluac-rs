-- regress_285_short_circuit_nested_break_tail: 双臂branch不能伪装成same-header loop control
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-contains [[ and ]]
-- unluac: expect-contains [[ or ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[if]] [[2]]
-- unluac: expect-ast-count [[break]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[6]]
local function run(a, b, c)
    local x = 0
    for _ = 1, 3 do
        if (a and b) or c then
            if c then
                break
            end
            x = x + 1
        else
            x = x + 2
        end
        x = x + 3
    end
    return x
end

local fallback = run(false, false, false)
local selected = run(true, true, false)
local stopped = run(false, false, true)
assert(fallback == 15 and selected == 12 and stopped == 0)
assert(run(false, true, false) == 15)
assert(run(true, false, false) == 15)
assert(run(false, true, true) == 0)
assert(run(true, false, true) == 0)
assert(run(true, true, true) == 0)
assert(run(nil, true, false) == 15)
assert(run(true, nil, nil) == 15)
assert(run(0, "", false) == 12)
assert(run("", 0, nil) == 12)
assert(run(false, false, 0) == 0)
assert(run(nil, false, "") == 0)
print(
    "regress_285_short_circuit_nested_break_tail",
    fallback,
    selected,
    stopped
)
