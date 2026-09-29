-- regress_81_degenerate_numeric_for_exit_pad#1: Luau keeps an unreachable latch exit jump pad
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-contains [[ = 1, 3 do]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[0]] [[@proto=1]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- 被测循环不需要 IIFE/辅助闭包；观察端可以把自定义迭代器作为参数传入。
-- unluac: expect-ast-count [[function]] [[0]] [[@proto=1]]
local function run(xs)
    for _ in xs do
        print("regress_81_degenerate_numeric_for_exit_pad#1 body")
        for _ = 1, 3 do
            break
        end
        continue
    end
end

run({ 1 })
run({})
local calls = 0
run(function()
    calls = calls + 1
    if calls <= 3 then return calls end
end)
assert(calls == 4)
