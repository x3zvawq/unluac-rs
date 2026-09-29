-- regress_185_branch_control_forward_guards#1: irreducible island 内多个 forward guard 共用 label
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]

local function run(entry, a, b, cycle)
    local value = 0
    if entry then
        goto second
    end

    ::first::
    if a then
        goto done
    end
    value = value + 1

    ::second::
    if b then
        goto done
    end
    value = value + 10
    if cycle then
        goto first
    end

    ::done::
    return value
end

local from_second_done = run(true, false, true, false)
local from_second_tail = run(true, false, false, false)
local from_first_done = run(false, true, false, false)
local from_first_second_done = run(false, false, true, false)
assert(from_second_done == 0 and from_second_tail == 10)
assert(from_first_done == 0 and from_first_second_done == 1)
print(
    "regress_185_branch_control_forward_guards#1",
    from_second_done,
    from_second_tail,
    from_first_done,
    from_first_second_done
)

-- 两个 guard 都不退出且 cycle=true 时无限循环；其余 14 组均有限。
for mask = 0, 15 do
    local entry = mask % 2 == 1
    local a = math.floor(mask / 2) % 2 == 1
    local b = math.floor(mask / 4) % 2 == 1
    local cycle = mask >= 8
    if a or b or not cycle then
        local want = 0
        if entry then
            if not b then want = 10 end
        elseif not a then
            want = b and 1 or 11
        end
        assert(run(entry, a, b, cycle) == want)
    end
end
assert(run(nil, 0, false, false) == 0)
assert(run(0, false, nil, false) == 10)
-- unluac: expect-ast-count [[goto]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[label]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[4]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
