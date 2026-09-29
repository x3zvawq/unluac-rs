-- regress_204_irreducible_explicit_close_owner#1: island 重入与侧出口必须保留显式 close 生命周期
-- unluac: expect-contains [[<close>]]
-- unluac: expect-contains [[if p3_0 then]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-ast-count [[local-binding]] [[9]]
-- unluac: expect-ast-count [[close-binding]] [[1]]
-- unluac: expect-ast-max [[label]] [[3]]
-- 独占出口 pad 不应使分支退回 island 原始跳转并逐轮增加 goto。
-- unluac: expect-count [[goto ]] [[3]]

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

local direct = run(false, false, false)
assert(closed == 1)
local second = run(true, false, false)
assert(closed == 1)
local side = run(false, true, false)
assert(closed == 2)
local reentry = run(true, false, true)
assert(direct == 1 and second == 1 and side == 1 and reentry == 1 and closed == 3)
print(
    "regress_204_irreducible_explicit_close_owner#1",
    direct,
    second,
    side,
    reentry,
    closed
)

-- 入口极性遵循 Lua 真值规则；重入路径的 close 仍只执行一次。
assert(run(nil, false, false) == 1 and closed == 4)
assert(run(0, false, false) == 1 and closed == 4)
assert(run("", false, true) == 1 and closed == 5)
