-- regress_187_irreducible_plain_loop_owner#1: 不可规约 island 内 plain loop owner 只保留必要 goto
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]

local function run(skip_first, rewind_first, rewind_second, initial)
    local value = initial or 0
    for index = 1, 2 do
        value = value + index
    end
    if skip_first then
        goto second_entry
    end

    ::first_entry::
    value = value + 10
    goto loop_header

    ::second_entry::
    value = value + 1

    ::loop_header::
    while value < 3 do
        value = value + 1
        if value == 2 then
            if rewind_first then
                goto first_entry
            end
            if rewind_second then
                goto second_entry
            end
        end
    end
    return value
end

print(
    "regress_187_irreducible_plain_loop_owner#1",
    run(false, false, false),
    run(true, false, false),
    run(true, true, false),
    run(true, false, true)
)

-- 原来的 initial=0 在前置 for 后已不满足 while；负初值实际执行两个 rewind。
for mask = 0, 7 do
    local skip_first = mask % 2 == 1
    local rewind_first = math.floor(mask / 2) % 2 == 1
    local rewind_second = mask >= 4
    assert(run(skip_first, rewind_first, rewind_second) == (skip_first and 4 or 13))
    local want = 10
    if skip_first then want = rewind_first and 12 or 3 end
    assert(run(skip_first, rewind_first, rewind_second, -3) == want)
end
assert(run(nil, false, false, -3) == 10)
assert(run(0, 0, nil, -3) == 12)
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[goto]] [[4]] [[@proto=1]]
-- unluac: expect-ast-max [[label]] [[3]] [[@proto=1]]
