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

print(
    "regress_185_branch_control_forward_guards#1",
    run(true, false, true, false),
    run(true, false, false, false),
    run(false, true, false, false),
    run(false, false, true, false)
)
