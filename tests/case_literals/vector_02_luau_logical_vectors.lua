-- 使用官方编译器的 vector 常量选项，覆盖共享原子域中的原生 vector 分支值。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- 恢复的选择调用仍先求值两个实参，并把单返回值补齐为 value/extra 两项。
-- unluac: expect-ast-max [[local-binding]] [[7]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=0]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- unluac: expect-contains [[--!optimize 2]]
local function choose(a,b)
    return a and vector.create(1,2,3) or b and vector.create(4,5,6) or vector.create(7,8,9)
end
for index, bits in ipairs({0, 1, 2, 3}) do
    local value, extra = choose(bits % 2 == 1, bits >= 2)
    local expected = bits % 2 == 1 and 1 or bits >= 2 and 4 or 7
    assert(index == bits + 1 and extra == nil)
    assert(value.x == expected and value.y == expected + 1 and value.z == expected + 2)
    print("vector", bits, value)
end
