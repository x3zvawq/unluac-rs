-- 不可规约区域中的两种 for owner 分别保留；相同路径骨架不替代各自的 VM 协议。
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- PUC 按源码顺序保存 child，LuaJIT 的 child 编号相反；每条合同仍指向独立函数。
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]] [[@dialect=luajit]]

local function run_numeric(start_second, jump_second)
    local total = 0
    if start_second then
        goto second
    end

    ::first::
    for index = 1, 2 do
        total = total + index
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

local function run_generic(start_second, jump_second)
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

do
    local direct = run_numeric(false, false)
    local second = run_numeric(true, false)
    local jumping = run_numeric(false, true)
    assert(direct == 3 and second == 13 and jumping == 22)
    assert(run_numeric(true, true) == 21)
    print(
        "regress_202_irreducible_numeric_for_owner#1",
        direct,
        second,
        jumping
    )
end

do
    local direct = run_generic(false, false)
    local second = run_generic(true, false)
    local jumping = run_generic(false, true)
    assert(direct == 3 and second == 13 and jumping == 22)
    assert(run_generic(true, true) == 21)
    print(
        "regress_203_irreducible_generic_for_owner#1",
        direct,
        second,
        jumping
    )
end
