-- regress_221_repeat_candidate_identity#1: repeat 必须消费 Structure 已选中的完整短路候选
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[p1_2 = r1_0]]
local function run(a, b, value)
    repeat
        for index = 1, 2 do
            value = value + index
        end
    until a and b
    return value
end

assert(run(true, true, 0) == 3)
print("regress_221_repeat_candidate_identity#1", run(true, true, 0))
