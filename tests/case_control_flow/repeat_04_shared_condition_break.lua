-- regress_225_repeat_shared_condition_break#1: repeat 尾条件共享 continuation 不能泄漏 residual Decision
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[p1_1 and p1_2 or r1_0 > 3]]
-- unluac: expect-not-contains [[if p1_1 and p1_2 then]]
-- unluac: expect-not-contains [[continue]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@proto=0]]
local function run(stop, left, right)
    local x = 0
    repeat
        x = x + 1
        if left and stop then
            break
        end
    until (left and right) or x > 3
    return x
end

local exhausted = run(false, false, false)
local condition = run(false, true, true)
local stopped = run(true, true, false)
assert(exhausted == 4 and condition == 1 and stopped == 1)
-- 原直接调用保留 O2 内联覆盖；额外输入经表调用，实际执行同一函数的各条件路径。
local subjects = {run}
assert(subjects[1](false, false, true) == 4)
assert(subjects[1](false, true, false) == 4)
assert(subjects[1](true, false, false) == 4)
assert(subjects[1](true, false, true) == 4)
assert(subjects[1](true, true, true) == 1)
assert(subjects[1](nil, 0, "") == 1)
assert(subjects[1](true, nil, true) == 4)
assert(subjects[1]("", 0, false) == 1)
assert(subjects[1](false, "", nil) == 4)
print(exhausted, condition, stopped)
