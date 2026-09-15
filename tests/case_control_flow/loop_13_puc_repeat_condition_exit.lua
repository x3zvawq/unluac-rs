-- regress_168_puc_repeat_condition_exit#1: 复合尾条件的退出方向必须保真
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while]]
-- unluac: expect-not-contains [[goto]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[until r1_0 == 3]]
-- unluac: expect-not-contains [[until false]]
-- 条件只读取循环外的计数器，不能被统计为 repeat 内局部声明。
-- unluac: expect-ast-count [[repeat-condition-local]] [[0]] [[@proto=1]]
local function counter()
    local x = 0
    repeat
        while x < 3 do
            x = x + 1
        end
    until (x == 3 and true) or false
    return x
end

local result = counter()
assert(result == 3)
print("regress_168_puc_repeat_condition_exit#1", result)
