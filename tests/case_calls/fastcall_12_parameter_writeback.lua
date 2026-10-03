-- 前一 CALL 写回参数后，下一 FASTCALL 的高槽参数 COPY 归低槽输入定义承接。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[call]] [[6]] [[@proto=1]]
-- unluac: expect-instruction-count [[call]] [[6]] [[@proto=1]]
local function update(value)
    value = bit32.bxor(bit32.lrotate(value, 1), bit32.rrotate(value, 1))
    value = bit32.bxor(bit32.lrotate(value, 2), bit32.rrotate(value, 8))
    return value
end

local calls = { update }
assert(calls[1](0) == 0)
assert(calls[1](12345) == 1854005698)
assert(calls[1](4294967295) == 0)
print("fastcall-parameter-writeback", "OK")
