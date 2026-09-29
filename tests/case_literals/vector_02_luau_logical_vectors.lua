-- 使用官方编译器的 vector 常量选项，覆盖共享原子域中的原生 vector 分支值。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- O2 内联后仍须先计算两个实参；保留这两个快照，不能把第二个比较移入短路分支。
-- unluac: expect-ast-max [[local-binding]] [[7]]
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
