-- 相等返回保留自然的条件返回，参数和调用结果的原 TEST 均须保留。
-- unluac: expect-ast-count [[if]] [[2]]
-- unluac: expect-ast-count [[local-decl]] [[1]]
-- unluac: expect-ast-count [[do-block]] [[0]]
-- unluac: expect-count [[return 42]] [[4]]
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
