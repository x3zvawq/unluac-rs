-- 无用 Boolean 计算可以省略；承接槽与 and/or/vararg 的潜在对象根不能一并删除。
-- unluac: expect-not-contains [[ = not ]]
-- unluac: expect-not-contains [[unreachable]]
-- unluac: expect-contains [[print("discard-not",]]
-- unluac: expect-contains [[print("discard-and",]]
-- unluac: expect-contains [[print("discard-or",]]
-- unluac: expect-contains [[print("discard-vararg")]]

local function discard_not(value)
    local unused = not value
    if 1 == 1 then
        print("discard-not", value)
    else
        print("unreachable", unused)
    end
end

local function discard_and(left, right)
    local unused = left and right
    if 1 == 1 then
        print("discard-and", left, right)
    else
        print("unreachable", unused)
    end
end

local function discard_or(left, right)
    local unused = left or right
    if 1 == 1 then
        print("discard-or", left, right)
    else
        print("unreachable", unused)
    end
end

local function discard_vararg(...)
    local unused = ...
    if 1 == 1 then
        print("discard-vararg")
    else
        print("unreachable", unused)
    end
end

discard_not(false)
discard_and(true, "and-rhs")
discard_or(false, "or-rhs")
discard_vararg("unused")
