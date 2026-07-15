-- regress_201_repeat_live_out#1: repeat 内更新的局部变量在退出后必须沿用同一 binding
-- unluac: expect-not-contains [[unluac error]]
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
