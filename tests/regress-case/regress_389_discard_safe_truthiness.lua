-- unluac: expect-not-contains [[    local ]]

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
