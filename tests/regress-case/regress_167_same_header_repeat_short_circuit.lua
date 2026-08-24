-- regress_167_same_header_repeat_short_circuit#1: 外层 repeat 短路尾条件不能与内层 while 合并
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while]]
-- unluac: expect-not-contains [[goto]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[until p1_1 or p1_2]]
-- unluac: expect-not-contains [[if p1_1 then]]
local function flags(a, b, c)
    repeat
        while a do
        end
    until b or c
    return a, b, c
end

print("regress_167_same_header_repeat_short_circuit#1", flags(false, true, false))
