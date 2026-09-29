-- regress_104_luau_repeat_skip_numeric_for#1: repeat 的条件 continue 可跳过完整 numeric-for
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[if not p1_0 or not p1_1 then]]
-- unluac: expect-not-contains [[else]]
-- unluac: expect-not-contains [[, nil, nil do]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
local function run(a, b, xs)
    local x = 0
    local iterations = 0
    for k, v in xs do
        local rounds = 0
        repeat
            rounds = rounds + 1
            iterations = iterations + 1
            if a and b then
                continue
            end
            for i = 1, 3 do
                x = x + 1
            end
        -- 有限尾条件同时观察 continue 是否仍执行本轮条件。
        until not b or rounds == 2
    end
    return x, iterations
end

local xs = {10, 20}
local value, iterations = run(true, true, xs)
assert(value == 0 and iterations == 4)
value, iterations = run(false, true, xs)
assert(value == 12 and iterations == 4)
value, iterations = run(true, false, xs)
assert(value == 6 and iterations == 2)
value, iterations = run(false, false, xs)
assert(value == 6 and iterations == 2)
value, iterations = run(true, true, {})
assert(value == 0 and iterations == 0)
print("regress_104_luau_repeat_skip_numeric_for#1")
