-- regress_204_irreducible_explicit_close_owner#1: island 重入与侧出口必须保留显式 close 生命周期
-- unluac: expect-contains [[<close>]]
-- unluac: expect-contains [[if p3_0 then]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]

local closed = 0
local mt = {
    __close = function()
        closed = closed + 1
    end,
}

local function closer()
    return setmetatable({}, mt)
end

local function run(start_second, jump_second, jump_first)
    if start_second then
        goto second
    end

    ::first::
    do
        local guard <close> = closer()
        if jump_second then
            goto second
        end
        goto done
    end

    ::second::
    if jump_first then
        goto first
    end

    ::done::
    return 1
end

print(
    "regress_204_irreducible_explicit_close_owner#1",
    run(false, false, false),
    run(true, false, false),
    run(false, true, false),
    run(true, false, true),
    closed
)
