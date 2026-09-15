-- regress_364_terminal_else_single_goto: a single fallback goto can become the terminal else arm
-- unluac: expect-order [[goto L2]] [[r1_1 = r1_0]]

local function run(entry, first_exit, second_exit, cycle)
    local value = 0
    if entry then
        goto second
    end

    ::first::
    if first_exit then
        goto done
    end
    value = value + 1

    ::second::
    value = 100
    if second_exit then
        goto done
    end
    value = value + 10
    if cycle then
        goto first
    end

    ::done::
    return value
end

assert(run(true, false, true, false) == 100)
assert(run(false, true, false, false) == 0)
assert(run(false, false, true, false) == 100)
