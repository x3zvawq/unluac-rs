-- regress_106_luau_repeat_current_iteration_tail#1: early continue 不能跨迭代抢占共享 tail
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[repeat]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=1]]
local function run(a, b, c, xs)
    local x = 0
    local rounds, tails, inner = 0, 0, 0
    repeat
        rounds = rounds + 1
        if a then
            if xs[x] then
                continue
            end
            while b and x < 2 do
                x = x + 1
            end
            local steps = 0
            repeat
                steps = steps + 1
                inner = inner + 1
                if a or c then
                    print(x)
                else
                    break
                end
            until (a and b) or steps == 2
        else
            local steps = 0
            repeat
                steps = steps + 1
                inner = inner + 1
                for k, v in xs do
                    break
                end
            until b or steps == 2
            if xs[x] then
                print(x)
            end
        end
        tails = tails + 1
        if a and b then
            break
        end
    until a or rounds == 2
    return x, rounds, tails, inner
end

-- 次数边界只终止原无限路径；continue 必须跳过所有嵌套循环与共享 tail。
local reads = 0
local skip = true
local xs = setmetatable({10}, {__index = function(_, key)
    assert(key == 0)
    reads = reads + 1
    return skip
end})
local x, rounds, tails, inner = run(true, true, false, xs)
assert(x == 0 and rounds == 1 and tails == 0 and inner == 0 and reads == 1)
x, rounds, tails, inner = run(true, false, true, xs)
assert(x == 0 and rounds == 1 and tails == 0 and inner == 0 and reads == 2)
skip = false
x, rounds, tails, inner = run(true, true, false, xs)
assert(x == 2 and rounds == 1 and tails == 1 and inner == 1 and reads == 3)
x, rounds, tails, inner = run(true, false, false, xs)
assert(x == 0 and rounds == 1 and tails == 1 and inner == 2 and reads == 4)
x, rounds, tails, inner = run(false, true, false, xs)
assert(x == 0 and rounds == 2 and tails == 2 and inner == 2 and reads == 6)
skip = true
x, rounds, tails, inner = run(false, false, true, xs)
assert(x == 0 and rounds == 2 and tails == 2 and inner == 4 and reads == 8)
print("regress_106_luau_repeat_current_iteration_tail#1")
