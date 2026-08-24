-- regress_100_adjacent_loop_redefining_header_state#1: 后继 loop header 重定义变量时仍要继承入口 state
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[r1_1 = r1_0]]
local function run(a)
    local x = 0
    for _ = 1, 3 do
        x = x + 1
    end
    repeat
        x = x + 1
    until a
    return x
end

print("regress_100_adjacent_loop_redefining_header_state#1", run(true))
