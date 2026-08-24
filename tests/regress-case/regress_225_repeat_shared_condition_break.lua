-- regress_225_repeat_shared_condition_break#1: repeat 尾条件共享 continuation 不能泄漏 residual Decision
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[until p1_1 and p1_2 or r1_0 > 3]]
-- unluac: expect-not-contains [[if p1_1 and p1_2 then]]
-- unluac: expect-not-contains [[continue]]
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

print(run(false, false, false), run(false, true, true), run(true, false, false))
