-- 槽压缩必须保护本轮新提升的按值捕获；后续同槽调用结果不能改写 NaN 快照。
-- 64 个保活值及其调用准备足以触发压缩；循环生成会丢失这条物理槽路径。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
function make() return 1 end
function consume(x) total = total + x end
local k0, k1, k2, k3, k4, k5, k6, k7 = make(), make(), make(), make(), make(), make(), make(), make()
local k8, k9, k10, k11, k12, k13, k14, k15 = make(), make(), make(), make(), make(), make(), make(), make()
local k16, k17, k18, k19, k20, k21, k22, k23 = make(), make(), make(), make(), make(), make(), make(), make()
local k24, k25, k26, k27, k28, k29, k30, k31 = make(), make(), make(), make(), make(), make(), make(), make()
local k32, k33, k34, k35, k36, k37, k38, k39 = make(), make(), make(), make(), make(), make(), make(), make()
local k40, k41, k42, k43, k44, k45, k46, k47 = make(), make(), make(), make(), make(), make(), make(), make()
local k48, k49, k50, k51, k52, k53, k54, k55 = make(), make(), make(), make(), make(), make(), make(), make()
local k56, k57, k58, k59, k60, k61, k62, k63 = make(), make(), make(), make(), make(), make(), make(), make()
local factory = ({ 0/0 })[1]
do
    local snapshot = factory
    factory = function()
        local function owner(...) return snapshot end
        return function() return owner() end
    end
end
local first = factory()
local second = factory()
print("identity", first == second, first() ~= first(), second() ~= second())
assert(first ~= second and first() ~= first() and second() ~= second())
total = 0
consume(k0); consume(k1); consume(k2); consume(k3); consume(k4); consume(k5); consume(k6); consume(k7);
consume(k8); consume(k9); consume(k10); consume(k11); consume(k12); consume(k13); consume(k14); consume(k15);
consume(k16); consume(k17); consume(k18); consume(k19); consume(k20); consume(k21); consume(k22); consume(k23);
consume(k24); consume(k25); consume(k26); consume(k27); consume(k28); consume(k29); consume(k30); consume(k31);
consume(k32); consume(k33); consume(k34); consume(k35); consume(k36); consume(k37); consume(k38); consume(k39);
consume(k40); consume(k41); consume(k42); consume(k43); consume(k44); consume(k45); consume(k46); consume(k47);
consume(k48); consume(k49); consume(k50); consume(k51); consume(k52); consume(k53); consume(k54); consume(k55);
consume(k56); consume(k57); consume(k58); consume(k59); consume(k60); consume(k61); consume(k62); consume(k63)
assert(total == 64)
