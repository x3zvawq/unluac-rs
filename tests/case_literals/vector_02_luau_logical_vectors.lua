-- 使用官方编译器的 vector 常量选项，覆盖共享原子域中的原生 vector 分支值。
-- unluac: expect-not-contains [[unluac error]]
local function choose(a,b)
    return a and vector.create(1,2,3) or b and vector.create(4,5,6) or vector.create(7,8,9)
end
for bits = 0, 3 do
    print("vector", bits, choose(bits % 2 == 1, bits >= 2))
end
