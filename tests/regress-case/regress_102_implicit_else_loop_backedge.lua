-- regress_102_implicit_else_loop_backedge#1: 内外 loop 共享 header 时保留各自的结构 owner
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while not]]
-- unluac: expect-contains [[else]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(b)
    local x = 0
    repeat
        while not b do
            x = x + 1
        end
    until not b
    return x
end

-- run 对任意布尔输入都不终止；只编译该 proto，避免执行阶段超时。
print("regress_102_implicit_else_loop_backedge#1")

-- regress_102_implicit_else_loop_backedge#2: 直接回 header 的分支臂是内层 loop 的空下一轮路径
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function toggle_until(b, c)
    repeat
        repeat
            c = not c
            if c then
                break
            end
        until c
    until b
    return c
end

print(
    "regress_102_implicit_else_loop_backedge#2",
    toggle_until(true, true),
    toggle_until(true, false)
)
