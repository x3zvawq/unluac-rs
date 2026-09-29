-- regress_489_phi_incoming_edge_identity: entry input and parallel physical edges retain distinct phi slots
-- unluac: expect-ast-count [[while]] [[2]]
-- 空 if 是输入字节码中的显式检查，须保留并行边的身份。
-- unluac: expect-ast-count [[if]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[2]]
-- unluac: expect-ast-count [[assign]] [[2]]
local function entry(flag)
    while flag do
        flag = false
    end
    return flag
end
local function parallel(flag, value)
    if flag then end
    while value do
        value = false
    end
    return value
end
assert(entry(true) == false)
assert(entry(false) == false)
assert(parallel(true, true) == false)
assert(parallel(false, true) == false)
assert(entry(nil) == nil)
assert(entry(0) == false)
assert(entry("") == false)
assert(parallel(true, false) == false)
assert(parallel(false, nil) == nil)
assert(parallel(nil, 0) == false)
assert(parallel(0, "") == false)
print("regress_489_phi_incoming_edge_identity", "closed")
