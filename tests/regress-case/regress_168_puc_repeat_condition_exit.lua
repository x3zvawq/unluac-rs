-- regress_168_puc_repeat_condition_exit#1: 复合尾条件的退出方向必须保真
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while]]
-- unluac: expect-not-contains [[goto]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function counter()
    local x = 0
    repeat
        while x < 3 do
            x = x + 1
        end
    until (x == 3 and true) or false
    return x
end

print("regress_168_puc_repeat_condition_exit#1", counter())
