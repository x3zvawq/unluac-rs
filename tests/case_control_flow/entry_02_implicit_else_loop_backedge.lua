-- regress_102_implicit_else_loop_backedge#1: 内外 loop 共享 header 时保留各自的结构 owner
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while not]]
-- 两个函数在 LuaJIT 的 proto 顺序相反；模块总数同时固定共享 header 的恢复结构。
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-count [[local-decl]] [[3]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[repeat]] [[2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[repeat]] [[3]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[repeat]] [[3]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[repeat]] [[3]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[repeat]] [[2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[repeat]] [[2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[repeat]] [[3]] [[@dialect=luau]]
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

local from_true = toggle_until(true, true)
local from_false = toggle_until(true, false)
assert(from_true == true and from_false == true)
assert(toggle_until(0, nil) == true)
assert(toggle_until("", 0) == true)
print(
    "regress_102_implicit_else_loop_backedge#2",
    from_true,
    from_false
)
