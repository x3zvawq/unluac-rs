-- regress_183_mixed_irreducible_explicit_close#1: cleanup 出边不能吞掉 island 目标 label
-- unluac: expect-contains [[<close>]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-ast-count [[local-binding]] [[4]]
-- unluac: expect-ast-count [[close-binding]] [[1]]
-- unluac: expect-ast-count [[do-block]] [[1]]
-- 两个源出口可共用 done，连续的尾部标签不应新增一个目标。
-- unluac: expect-ast-max [[label]] [[3]]

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
assert(run(0, "", nil) == 1)
assert(closed == 5)
print("regress_183_mixed_irreducible_explicit_close#1", closed)
