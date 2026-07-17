-- regress_263_repeat_tail_temp_inline#1: repeat尾条件的机械temp由HIR同轮内联
-- unluac: expect-contains [[until r0_0[r0_1] >= 1]]
local values = {}
local index = 1
repeat
    values[index] = index
until values[index] >= 1
print("regress_263_repeat_tail_temp_inline#1", values[index])

-- regress_263_repeat_tail_temp_inline#2: 自更新状态不是可删除的forwarding temp
-- unluac: expect-contains [[r0_2 = r0_2 + 1]]
local count = 0
repeat
    count = count + 1
until count >= 3
print("regress_263_repeat_tail_temp_inline#2", count)
