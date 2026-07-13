-- regress_103_repeat_nested_loop_shared_tail#1: 内层 repeat 的非 break 路径进入外层 repeat 共享 tail
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
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

-- 部分布尔组合不会终止；只编译该 proto，避免执行阶段超时。
print("regress_103_repeat_nested_loop_shared_tail#1")
