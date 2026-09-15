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
