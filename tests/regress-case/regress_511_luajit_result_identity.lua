-- Proto-anchored cdata need no old stack root, but copying a literal can change identity.
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
local left, right = signed_pair()
assert(rawequal(left, right) and not rawequal(1LL, 1LL))
left, right = unsigned_pair()
assert(rawequal(left, right) and not rawequal(1ULL, 1ULL))
left, right = complex_pair()
assert(rawequal(left, right) and not rawequal(1i, 1i))
print("regress_511_luajit_result_identity", "OK")
