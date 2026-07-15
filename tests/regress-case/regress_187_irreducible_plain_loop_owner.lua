-- regress_187_irreducible_plain_loop_owner#1: 不可规约 island 内 plain loop owner 只保留必要 goto
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]

local function run(skip_first, rewind_first, rewind_second)
    local value = 0
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
