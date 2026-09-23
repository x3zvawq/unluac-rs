-- regress_364_terminal_else_single_goto: a single fallback goto can become the terminal else arm
-- 状态 carrier 合并后不再要求机械交接；入口跳转仍须越过 first 的写入到达 second。
-- unluac: expect-order [[goto L2]] [[= 100]]
-- unluac: expect-ast-count [[goto]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[label]] [[2]] [[@proto=1]]

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
