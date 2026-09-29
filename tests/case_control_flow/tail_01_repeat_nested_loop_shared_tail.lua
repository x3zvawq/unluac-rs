-- regress_103_repeat_nested_loop_shared_tail#1: 内层 repeat 的非 break 路径进入外层 repeat 共享 tail
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-min [[repeat]] [[2]] [[@proto=1]]
-- unluac: expect-ast-min [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-min [[break]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[2]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[break]] [[1]]
-- unluac: expect-ast-count [[if]] [[2]]
-- unluac: expect-ast-count [[local-binding]] [[2]]
local function run(a, b, c)
    local x = 0
    repeat
        if a then
            repeat
                x = x + 1
            until b
            if c then
                break
            end
        end
        while not b do
            x = x + 1
        end
    until not b
    return x
end

-- 固定参数下只有这类真值组合能正常退出；其余路径保留结构断言，不声称运行覆盖。
assert(run(true, true, true) == 1)
assert(run(0, "", 0) == 1)
print("regress_103_repeat_nested_loop_shared_tail#1")
