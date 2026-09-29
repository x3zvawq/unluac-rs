-- regress_96_luau_loop_exit_bounded_branch#1: local break must not push the enclosing branch merge to loop exit
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[break]] [[1]]
-- unluac: expect-ast-count [[if]] [[4]]
-- unluac: expect-ast-count [[local-binding]] [[8]]
local function run(a, b, c, xs)
    for _ in xs do
        if a then
            if c then
                break
            end
            while b do
                continue
            end
        end
        if c then
            continue
        end
    end
    return 0
end

local empty_result = run(false, true, false, {})
local local_break = run(true, true, true, { true })
local skipped_while = run(true, false, false, { true })
assert(empty_result == 0 and local_break == 0 and skipped_while == 0)
local calls = 0
local function iterate(_, control)
    calls = calls + 1
    local next_index = (control or 0) + 1
    if next_index <= 3 then
        return next_index
    end
end
assert(run(false, true, false, iterate) == 0)
assert(calls == 4)
calls = 0
assert(run(false, true, true, iterate) == 0)
assert(calls == 4)
calls = 0
assert(run(true, false, false, iterate) == 0)
assert(calls == 4)
calls = 0
assert(run(true, true, true, iterate) == 0)
assert(calls == 1)
calls = 0
assert(run(0, true, "", iterate) == 0)
assert(calls == 1)
calls = 0
assert(run(nil, true, 0, iterate) == 0)
assert(calls == 4)
calls = 0
assert(run("", nil, false, iterate) == 0)
assert(calls == 4)
print("regress_96_luau_loop_exit_bounded_branch#1", empty_result, local_break, skipped_while)
