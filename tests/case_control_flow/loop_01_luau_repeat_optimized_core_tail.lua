-- regress_108_luau_repeat_optimized_core_tail#1: O2 展开块沿当前 loop core 恢复 tail guard
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[until p1_0]]
-- unluac: expect-not-contains [[if not p1_0 then]]
-- unluac: expect-not-contains [[if p1_1 then]]
-- O2 最后一轮仍保留 a 控制下的 b TEST，不能因两边都到 latch 而删掉或无条件发射。
-- unluac: expect-count [[if p1_0 and p1_1 then]] [[3]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=1]]
local function optimized_tail(a, b)
    local x = 0
    repeat
        print(x)
        for i = 1, 3 do
            x = x + 1
            print(x)
            if a and b then
                break
            end
        end
    until a
    return x
end

local full = optimized_tail(true, false)
assert(full == 3)
local early = optimized_tail(true, true)
assert(early == 1)
local nil_guard = optimized_tail(0, nil)
assert(nil_guard == 3)
local truthy_guard = optimized_tail(0, 0)
assert(truthy_guard == 1)
print("regress_108_luau_repeat_optimized_core_tail#1", full, early, nil_guard, truthy_guard)
-- 首次生成保留原四次调用与四个结果，不把调用准备拆成可变别名。
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@proto=0]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[call]] [[9]] [[@proto=0]]
-- 展开后的三次加法仍写回同一状态，不生成各轮快照声明。
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[3]] [[@proto=1]]
