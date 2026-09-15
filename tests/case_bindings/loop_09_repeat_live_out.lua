-- regress_201_repeat_live_out#1: repeat 内更新的局部变量在退出后必须沿用同一 binding
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[r0_2, r0_3, r0_4 = r0_8, r0_6, r0_7]]
-- unluac: expect-not-contains [[r0_3, r0_4, r0_5 = r0_9, r0_7, r0_8]]
local i = 0
local maximum = 0
local minimum = 2

repeat
    local value = i / 10
    maximum = math.max(maximum, value)
    minimum = math.min(minimum, value)
    i = i + 1
until i > 2

assert(minimum == 0 and maximum == 0.2)
print("regress_201_repeat_live_out#1", "OK")
