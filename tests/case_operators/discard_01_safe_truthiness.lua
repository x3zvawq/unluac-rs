-- unluac: expect-ast-count [[function]] [[5]]
-- unluac: expect-ast-count [[if]] [[4]]
-- unluac: expect-ast-max [[local-binding]] [[10]]
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

local conversions = 0
local marker = setmetatable({}, { __tostring = function()
    conversions = conversions + 1
    return "marker"
end })
discard_not(nil)
discard_not(0)
discard_not("")
discard_not(marker)
discard_and(false, marker)
discard_and(nil, marker)
discard_and(0, marker)
discard_and(marker, false)
discard_or(true, marker)
discard_or(0, marker)
discard_or(nil, marker)
discard_or(marker, false)
discard_vararg(nil, marker)
discard_vararg(marker, nil, "tail")
assert(select("#", discard_not(true)) == 0)
assert(select("#", discard_and(marker, nil)) == 0)
assert(select("#", discard_or(nil, marker)) == 0)
assert(select("#", discard_vararg()) == 0)
assert(conversions == 11)
