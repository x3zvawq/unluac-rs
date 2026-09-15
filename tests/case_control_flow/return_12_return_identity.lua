-- Ordinary returns have no pending cleanup identity to distinguish equal arms.
-- unluac: expect-not-contains [[if ]]
-- unluac: expect-count [[return 42]] [[2]]
local function plain(flag)
    if flag then return 42 else return 42 end
end

local function effectful(predicate)
    if predicate() then return 42 else return 42 end
end

local calls = 0
local function yes()
    calls = calls + 1
    return true
end
local function no()
    calls = calls + 1
    return false
end

assert(plain(false) == 42)
assert(plain(true) == 42)
assert(effectful(yes) == 42)
assert(effectful(no) == 42)
assert(calls == 2)
print("regress_482_equal_return_identity", calls)
