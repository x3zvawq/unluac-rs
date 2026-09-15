-- regress_121_luau_short_circuit_immediate_repeat_break#1: repeat body 的短路失败出口保留立即 break
-- unluac: expect-contains [[        repeat]]
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
            if a or c() then
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
        until c()
    end
    return x
end

local runner = _G.__unluac_regress_121_runner or run
local condition_calls = 0
local function stop_every_second_call()
    condition_calls = condition_calls + 1
    return condition_calls % 2 == 0
end
local value = runner(true, true, stop_every_second_call, {})
assert(value == 6 and condition_calls == 6)
print(
    "regress_121_luau_short_circuit_immediate_repeat_break#1",
    value,
    condition_calls
)
