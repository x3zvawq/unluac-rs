-- regress_183_mixed_irreducible_explicit_close#1: cleanup 出边不能吞掉 island 目标 label
-- unluac: expect-contains [[<close>]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]

local closed = 0
local function closer()
    return setmetatable({}, {
        __close = function()
            closed = closed + 1
        end,
    })
end

local function run(a, b, c)
    do
        local guard <close> = closer()
        if a then
            goto left
        end
        goto right

        ::left::
        if b then
            goto done
        end
        goto right

        ::right::
        if c then
            goto done
        end
        goto left
    end

    ::done::
    return 1
end

-- 覆盖两个入口、两个出口，以及 right -> left 的回跳；不执行无出口环。
assert(run(true, true, false) == 1)
assert(closed == 1)
assert(run(false, false, true) == 1)
assert(closed == 2)
assert(run(false, true, false) == 1)
assert(closed == 3)
assert(run(true, false, true) == 1)
assert(closed == 4)
print("regress_183_mixed_irreducible_explicit_close#1", closed)
