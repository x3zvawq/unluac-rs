-- regress_97_repeat_header_break_pad#1: a repeat body break pad must not become the loop post block
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[until ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- 尾条件直接消费调用结果；中转 local 不应在回编译中逐轮增长。
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[repeat-condition-local]] [[0]]
-- unluac: expect-ast-count [[do-block]] [[0]]
local function run(a, b, c, stop)
    local x = 0
    local rounds = 0
    while not b do
        rounds = rounds + 1
        if rounds == 3 then return x, rounds end
        repeat
            if a or c then
                if a and b then
                    break
                end
                break
            else
                x = x + 1
            end
        -- stop 只限住原无限路径；两条 break 都必须跳过它。
        until b or stop(x)
    end
    return x, rounds
end

local tests = 0
local function stop(x)
    tests = tests + 1
    return x >= 2
end
local result, rounds = run(false, true, false, stop)
assert(result == 0 and rounds == 0 and tests == 0)
result, rounds = run(true, false, false, stop)
assert(result == 0 and rounds == 3 and tests == 0)
result, rounds = run(false, false, true, stop)
assert(result == 0 and rounds == 3 and tests == 0)
result, rounds = run(false, false, false, stop)
assert(result == 3 and rounds == 3 and tests == 3)
print("regress_97_repeat_header_break_pad#1", result, rounds, tests)
