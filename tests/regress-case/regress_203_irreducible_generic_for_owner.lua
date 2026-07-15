-- regress_203_irreducible_generic_for_owner#1: 不可规约 island 内的 generic-for 仍须由循环候选接管
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]

local function run(start_second, jump_second)
    local total = 0
    if start_second then
        goto second
    end

    ::first::
    for _, value in ipairs({ 1, 2 }) do
        total = total + value
        if jump_second then
            goto second
        end
    end
    goto done

    ::second::
    total = total + 10
    if total < 20 then
        goto first
    end

    ::done::
    return total
end

print(
    "regress_203_irreducible_generic_for_owner#1",
    run(false, false),
    run(true, false),
    run(false, true)
)
