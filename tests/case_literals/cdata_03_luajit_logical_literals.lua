-- cdata 字面量可作为短路返回值；成本分析与等价验证须共用完整的原子值域。
-- unluac: expect-not-contains [[unluac error]]
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
    print("literals", bits, tostring(signed(a, b)), tostring(unsigned(a, b)), tostring(imaginary(a, b)))
end
