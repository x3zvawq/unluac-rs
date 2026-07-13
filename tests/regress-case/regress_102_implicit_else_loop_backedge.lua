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
