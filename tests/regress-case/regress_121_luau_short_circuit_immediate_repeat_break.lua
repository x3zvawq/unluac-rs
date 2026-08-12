-- regress_121_luau_short_circuit_immediate_repeat_break#1: repeat body 的短路失败出口保留立即 break
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[local r1_2 = r1_0]]
local function run(a, b, c, xs)
    local x = 0
    for i = 1, 3 do
        repeat
            if a or c then
                if a and b then
                    x = x + 1
                end
                for k, v in xs do
                    x = x + 1
                    x = x + 1
                    break
                end
            else
                break
            end
            continue
        until c
    end
    return x
end

print(
    "regress_121_luau_short_circuit_immediate_repeat_break#1",
    run(false, false, false, {})
)
