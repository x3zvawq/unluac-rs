-- cdata 字面量可作为短路返回值；成本分析与等价验证须共用完整的原子值域。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[13]]
local function signed(a, b)
    return a and 1LL or b and 2LL or 3LL
end
local function unsigned(a, b)
    return a and 1ULL or b and 2ULL or 3ULL
end
local function imaginary(a, b)
    return a and 1i or b and 2i or 3i
end

for bits = 0, 3 do
    local a, b = bits % 2 == 1, bits >= 2
    local expected = a and 1 or b and 2 or 3
    local s, signed_extra = signed(a, b)
    local u, unsigned_extra = unsigned(a, b)
    local c, imaginary_extra = imaginary(a, b)
    assert(type(s) == "cdata" and s == expected and signed_extra == nil)
    assert(type(u) == "cdata" and u == expected and unsigned_extra == nil)
    assert(type(c) == "cdata" and c.re == 0 and c.im == expected and imaginary_extra == nil)
    print("literals", bits, tostring(s), tostring(u), tostring(c))
end
