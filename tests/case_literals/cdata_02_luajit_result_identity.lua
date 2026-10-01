-- Proto-anchored cdata need no old stack root, but copying a literal can change identity.
-- unluac: expect-ast-max [[local-binding]] [[9]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=3]]
local function signed_pair()
    local value = 1LL
    return value, value
end
local function unsigned_pair()
    local value = 1ULL
    return value, value
end
local function complex_pair()
    local value = 1i
    return value, value
end
local left, right, extra = signed_pair()
assert(rawequal(left, right) and not rawequal(1LL, 1LL))
assert(extra == nil and rawequal(left, (signed_pair())))
left, right, extra = unsigned_pair()
assert(rawequal(left, right) and not rawequal(1ULL, 1ULL))
assert(extra == nil and rawequal(left, (unsigned_pair())))
left, right, extra = complex_pair()
assert(rawequal(left, right) and not rawequal(1i, 1i))
assert(extra == nil and rawequal(left, (complex_pair())))
print("regress_511_luajit_result_identity", "OK")
