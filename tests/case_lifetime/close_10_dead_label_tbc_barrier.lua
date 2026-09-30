-- regress_328_dead_label_tbc_barrier: raw Close 收敛前必须保留 TBC active-set 的机械 label
-- unluac: expect-contains [[<close>]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- 资源、数值循环和 x 的原声明足够表达 island，不应分裂为每个入口的状态副本。
-- unluac: expect-ast-count [[local-binding]] [[5]]
-- unluac: expect-ast-count [[close-binding]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[do-block]] [[1]]
-- unluac: expect-count [[assert(]] [[3]]

local closed = 0
local closer = setmetatable({}, {
    __close = function()
        closed = closed + 1
    end,
})

do
    local guard <close> = closer
    for _ = 1, 1 do
    end

    local x = 0
    if closed == 0 then
        goto right
    end

    ::left::
    x = x + 1
    if x < 3 then
        goto right
    end
    goto done

    ::right::
    x = x + 1
    if x < 3 then
        goto left
    end

    ::done::
    assert(x == 3)
    assert(closed == 0)
end
assert(closed == 1)
print("regress_328_dead_label_tbc_barrier")
