-- string.pack 逐值观察 f32 位模式；stock runtime 不代表 f32 VM 的算术验证。
-- unluac: expect-contains [[0.1]]
-- unluac: expect-contains [[0.2]]
-- unluac: expect-contains [[1e-45]]
-- unluac: expect-contains [[1.1754944e-38]]
-- unluac: expect-contains [[3.4028235e38]]
-- unluac: expect-not-contains [[0.10000000149011612]]
-- unluac: expect-not-contains [[0.20000000298023224]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[7]]

local function child()
    return 0.2, -0.0, 1.0
end
local values = {
    0.1, -0.1, 1e-45, -1e-45, 1.1754944e-38, 3.4028235e38,
    1.0000001, 1.0000002, 16777216.0, 0.0,
    child(),
}
local expected = {
    0x3dcccccd, 0xbdcccccd, 0x00000001, 0x80000001, 0x00800000, 0x7f7fffff,
    0x3f800001, 0x3f800002, 0x4b800000, 0x00000000,
    0x3e4ccccd, 0x80000000, 0x3f800000,
}
assert(#values == #expected)
assert(#values == 13)
local visits = 0
for i, value in ipairs(values) do
    visits = visits + 1
    assert(math.type(value) == "float")
    local bits = string.unpack("<I4", string.pack("<f", value))
    assert(bits == expected[i], i)
    print(i, string.format("%08x", bits))
end
assert(visits == 13)
