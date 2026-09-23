-- 结果未使用不授权删除原 NOT 或显式比较；and/or/vararg 的潜在对象根也须保留。
-- unluac: expect-count [[ = not ]] [[1]]
-- unluac: expect-count [[if 1 == 1 then]] [[4]]
-- unluac: expect-count [[print("unreachable",]] [[4]]
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
