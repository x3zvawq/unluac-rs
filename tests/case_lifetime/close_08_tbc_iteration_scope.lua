-- regress_243_repeat_tbc_iteration_scope: repeat 条件两侧的 CLOSE 属于每轮共享词法域
-- unluac: expect-contains [[<close>]]
-- 独立的循环计数 epoch 可以分别声明，条件写入不需要额外布尔中转变量。
-- unluac: expect-ast-max [[local-binding]] [[8]]
-- unluac: expect-ast-count [[close-binding]] [[3]]
-- unluac: expect-ast-count [[repeat]] [[3]]
-- unluac: expect-ast-count [[repeat-condition-local]] [[1]]

local closed = 0
local closer = setmetatable({}, {
    __close = function()
        closed = closed + 1
    end,
})

local i = 0
repeat
    i = i + 1
    assert(closed == i - 1)
    local unused <close> = closer
until i == 2
assert(closed == 2)

i = 0
repeat
    i = i + 1
    assert(closed == i + 1)
    closer.done = i == 2
    local state <close> = closer
until state.done
assert(closed == 4)

i = 0
repeat
    i = i + 1
    assert(closed == i + 3)
    local break_guard <close> = closer
    if i == 2 then
        break
    end
until false
assert(closed == 6)

print("regress_243_repeat_tbc_iteration_scope")
